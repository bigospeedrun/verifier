#!/usr/bin/env python3
"""Thin A2A client: GitHub issues as topics, comments as messages.

Stdlib only (urllib). See SPEC.md for the protocol.

Environment: GITHUB_TOKEN (required), GITHUB_REPO (``owner/repo``, or pass
``repo=`` to the constructor). No retries, no queuing, no persistence — by
design. A failed call raises; the caller decides what to do.

Typical use:

    from client import A2A

    alice = A2A(me="darkhipo")                # bound later by open_topic/post
    req = alice.post(to="crocswap", type_="verify-request",
                     body="Verify lemma X at <url>")
    for msg in A2A(me="crocswap").poll():      # poll my routing label
        if msg.type == "verify-request":
            A2A(me="crocswap").reply(msg.comment_id, body="VERDICT: ...")
"""

from __future__ import annotations

import json
import os
import re
import urllib.error
import urllib.request
from dataclasses import dataclass

API = "https://api.github.com"
HEADER_RE = re.compile(r"^(from|to|type|priority|body):\s*(.*)$")
USER_AGENT = "a2a-thin-client/0.1"


@dataclass
class Message:
    """One parsed A2A message. comment_id/issue/url are set when the message
    came from the API (parse() alone leaves them None)."""

    from_: str
    to: str
    type: str
    priority: str
    body: str
    comment_id: int | None = None
    issue: int | None = None
    url: str | None = None


def format_message(from_: str, to: str, type_: str, priority: str, body: str) -> str:
    """Render a comment body: header lines, then `body:` marker, then free text."""
    return f"from: {from_}\nto: {to}\ntype: {type_}\npriority: {priority}\nbody:\n{body}"


def parse(text: str) -> Message | None:
    """Parse a comment body. Returns None if it is not an A2A message
    (first non-blank line must be a `from:` header; the `body:` line is
    required and terminates the header)."""
    lines = text.splitlines()
    i = 0
    while i < len(lines) and not lines[i].strip():
        i += 1
    hdr: dict[str, str] = {}
    while i < len(lines):
        m = HEADER_RE.match(lines[i])
        if not m:
            return None  # not an A2A message
        key, val = m.group(1), m.group(2).strip()
        if key == "body":
            i += 1
            break  # everything after the marker is the body
        hdr[key] = val
        i += 1
    if "from" not in hdr or "to" not in hdr:
        return None
    return Message(
        from_=hdr.get("from", ""),
        to=hdr.get("to", ""),
        type=hdr.get("type", "note"),
        priority=hdr.get("priority", "normal"),
        body="\n".join(lines[i:]).strip(),
    )


def verify_reply_body(request: Message, verdict: str, evidence=()) -> str:
    """Build a verify-reply body per the reply convention: verdict, quote,
    evidence links."""
    quote = "\n".join("> " + ln for ln in request.body.splitlines()[:8]) or "> (empty)"
    lines = [f"VERDICT: {verdict}", "", "Request:", quote]
    if evidence:
        lines += ["", "Evidence:"] + [f"- {e}" for e in evidence]
    return "\n".join(lines)


class A2A:
    """One swarm's view of one transport repo. Optionally bound to a topic
    (issue number); an unbound post() opens a fresh topic."""

    def __init__(self, repo: str | None = None, token: str | None = None,
                 me: str | None = None, issue: int | None = None):
        self.repo = repo or os.environ.get("GITHUB_REPO") or ""
        self.token = token or os.environ.get("GITHUB_TOKEN") or ""
        self.me = me or os.environ.get("A2A_SWARM", "anonymous")
        self.issue = issue
        if not self.repo or not self.token:
            raise RuntimeError("A2A needs GITHUB_REPO and GITHUB_TOKEN (or repo=/token=)")

    # -- transport -----------------------------------------------------

    def _api(self, method: str, path: str, payload: dict | None = None) -> dict:
        req = urllib.request.Request(
            API + path,
            data=json.dumps(payload).encode() if payload is not None else None,
            method=method,
            headers={
                "Authorization": f"Bearer {self.token}",
                "Accept": "application/vnd.github+json",
                "Content-Type": "application/json",
                "User-Agent": USER_AGENT,
            },
        )
        try:
            with urllib.request.urlopen(req) as resp:
                return json.loads(resp.read().decode() or "{}")
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode()[:300]
            raise RuntimeError(f"GitHub {exc.code} on {method} {path}: {detail}") from exc

    def _wrap(self, msg: Message | None, comment: dict) -> Message:
        if msg is None:
            raise RuntimeError("posted body failed to parse back; bug in format_message")
        msg.comment_id = comment["id"]
        msg.issue = int(comment["issue_url"].rsplit("/", 1)[-1])
        msg.url = comment.get("html_url")
        return msg

    # -- protocol ------------------------------------------------------

    def open_topic(self, title: str, label: str | None = None) -> int:
        """Create an issue (topic), optionally routed with an a2a: label."""
        labels = [f"a2a:{label}"] if label else []
        issue = self._api("POST", f"/repos/{self.repo}/issues", {
            "title": title,
            "body": f"A2A topic opened by {self.me}. Messages follow as comments.",
            "labels": labels,
        })
        self.issue = issue["number"]
        return issue["number"]

    def post(self, to: str, body: str, type_: str = "verify-request",
             priority: str = "normal") -> Message:
        """Send a message. If not bound to a topic, opens one titled from the
        first body line, labeled a2a:<to>."""
        if self.issue is None:
            title = (body.strip().splitlines() or ["a2a topic"])[0][:72]
            self.open_topic(title, label=to)
        comment = self._api("POST", f"/repos/{self.repo}/issues/{self.issue}/comments", {
            "body": format_message(self.me, to, type_, priority, body),
        })
        return self._wrap(parse(comment["body"]), comment)

    def reply(self, comment_id: int, body: str, type_: str | None = None,
              priority: str = "normal") -> Message:
        """Reply to a message: addressed to its sender, in its topic. Type
        defaults to verify-reply when answering a verify-request."""
        comment = self._api("GET", f"/repos/{self.repo}/issues/comments/{comment_id}")
        parent = parse(comment.get("body", ""))
        if parent is None:
            raise ValueError(f"comment {comment_id} is not an A2A message")
        if type_ is None:
            type_ = "verify-reply" if parent.type == "verify-request" else parent.type
        self.issue = int(comment["issue_url"].rsplit("/", 1)[-1])
        return self.post(to=parent.from_, body=body, type_=type_, priority=priority)

    def poll(self, label: str | None = None) -> list[Message]:
        """All messages in open topics carrying a2a:<label> (default: my own
        handle). First page only — thin means you poll often, not hard."""
        label = self.me if label is None else label
        out: list[Message] = []
        issues = self._api("GET",
                           f"/repos/{self.repo}/issues?labels=a2a:{label}&state=open&per_page=20")
        for issue in issues:
            if "pull_request" in issue:
                continue
            number = issue["number"]
            for comment in self._api(
                    "GET", f"/repos/{self.repo}/issues/{number}/comments?per_page=100"):
                msg = parse(comment["body"])
                if msg is not None:
                    msg.comment_id = comment["id"]
                    msg.issue = number
                    msg.url = comment["html_url"]
                    out.append(msg)
        return out

    def close(self) -> None:
        """Close the bound topic (done when a conversation is over)."""
        if self.issue is not None:
            self._api("PATCH", f"/repos/{self.repo}/issues/{self.issue}",
                      {"state": "closed"})
