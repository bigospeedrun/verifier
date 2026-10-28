#!/usr/bin/env python3
"""End-to-end demo of A2A-over-GitHub: living proof the protocol works.

Two demo swarms talk through a real transport repo:

    demo-asker  --verify-request-->  demo-responder  (posted, then polled)
    demo-responder  --verify-reply-->  demo-asker   (reply, verdict, evidence)

Run:   GITHUB_TOKEN=... GITHUB_REPO=owner/repo python3 demo/demo_test.py
or:    pytest demo/demo_test.py
Skips cleanly (exit 0) when GITHUB_TOKEN / GITHUB_REPO are absent, so it can
sit in CI and run whenever the secrets are provided.
"""

import os
import sys
import uuid

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from client import A2A, verify_reply_body  # noqa: E402

ASKER, RESPONDER = "demo-asker", "demo-responder"


def run() -> str:
    token = os.environ.get("GITHUB_TOKEN")
    repo = os.environ.get("GITHUB_REPO") or os.environ.get("A2A_DEMO_REPO")
    if not (token and repo):
        print("skip: set GITHUB_TOKEN and GITHUB_REPO to run the a2a demo")
        return "skip"

    asker = A2A(repo=repo, token=token, me=ASKER)
    responder = A2A(repo=repo, token=token, me=RESPONDER)
    suffix = uuid.uuid4().hex[:8]
    req = rep = None
    try:
        # 1. Ask: open a routed topic and post a verify-request in one call.
        req = asker.post(
            to=RESPONDER,
            type_="verify-request",
            body=f"Verify claim {suffix}: the demo test file exists.\n"
                 f"Artifact: demo/demo_test.py in {repo}\n"
                 f"Verified means: the file is present at HEAD.",
        )
        assert req.to == RESPONDER and req.type == "verify-request" and req.issue

        # 2. The responder polls its routing label and finds the request.
        found = [m for m in responder.poll(label=RESPONDER)
                 if m.comment_id == req.comment_id]
        assert found, "verify-request not found by poll()"
        got = found[0]
        assert (got.from_, got.to, got.type, got.body) == (
            ASKER, RESPONDER, "verify-request", req.body), "round-trip mismatch"

        # 3. The responder replies: verdict + quote + evidence link.
        rep = responder.reply(
            req.comment_id,
            body=verify_reply_body(
                got, "verified",
                [f"https://github.com/{repo} — {ASKER} artifacts at HEAD"]),
        )
        assert rep.to == ASKER and rep.type == "verify-reply"
        assert "VERDICT: verified" in rep.body

        # 4. The asker sees the verdict addressed to it.
        verdicts = [m for m in asker.poll(label=RESPONDER)
                    if m.type == "verify-reply" and m.to == ASKER]
        assert any(v.comment_id == rep.comment_id for v in verdicts), \
            "verify-reply not visible to the asker"

        print(f"a2a demo OK: issue #{req.issue}, "
              f"request #{req.comment_id}, reply #{rep.comment_id}")
        return "ok"
    finally:
        if req and req.issue:
            try:
                asker.close()
            except RuntimeError as exc:
                print(f"cleanup: could not close issue #{req.issue}: {exc}")


def test_round_trip():
    """pytest entry point: end-to-end post -> poll -> parse -> reply."""
    assert run() in ("ok", "skip")


if __name__ == "__main__":
    sys.exit(0 if run() in ("ok", "skip") else 1)
