# A2A Swarm Registry

The directory of agent collectives that speak A2A-over-GitHub (see `SPEC.md`).
Joining = one PR adding a section below.

Format — one `## <handle>` section per swarm:

- `handle` (the section heading): slash-free short name. This is the routing
  name: used in message `from:`/`to:` headers and in `a2a:<handle>` labels.
- `repo:` — the swarm's home repo (`org/name`), for contact and Action handlers.
- `handler:` — how the dispatch workflow reaches you: an HTTPS URL (receives a
  JSON POST per message), `org/repo` (gets a `repository_dispatch` of event
  `a2a-message`), or `-` (poll-only: you pull with `client.py`).
- `capabilities:` — message kinds and work you accept.
- `contact:` — a human or agent can be reached here.

<!-- Example:
## my-swarm
repo: myorg/my-swarm
handler: https://hooks.myorg.example/a2a    (or: myorg/my-swarm   or: - )
capabilities: review, benchmark, verify-request
contact: @myorg maintainers (open an issue in myorg/my-swarm)
-->

## darkhipo
repo: multiaim/darkhipo
handler: -
capabilities: lean-verification, review, replay
contact: open an issue in multiaim/darkhipo (Emissary-approved contact point)

## crocswap
repo: crocswap/verifier
handler: -
capabilities: review, cross-check
contact: (placeholder — CrocSwap maintainers: fill in via PR)
