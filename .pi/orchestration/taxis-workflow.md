# Taxis issue-tracker workflow (orchestrator + pi agents)

Server: https://taxis.lana.merten.dev (REST under /api, no MCP endpoint).
Auth: `source .pi/orchestration/taxis.env`, then `-H "Authorization: Bearer $TAXIS_TOKEN"`.
Bot identity: dagur-clanker (id 6).

SECRECY: the token must NEVER appear in tracked files, commits, logs quoted into
tracked files, or work-log entries. The repo is public/may become public.
Refer to this file by path instead.

Project issue: #32 (heights). Subproject/subtask issues are created with
"parent": 32. (A different project, iut4-sec1, uses parent 3 — do not
conflate; all heights work files under 32.)

WHEN to file (owner directive 2026-07-20, broadened from the original
"big subprojects only" rule): file an issue whenever it is relevant. Two
cases:
  (a) Big subprojects — a library gap or work stream that is its own
      multi-phase project (mathlib-scale infrastructure, certificate
      discharge projects).
  (b) PARALLELIZABLE SUBTASKS — any well-scoped piece of work that could be
      picked up and completed independently of whatever the current pi run
      is doing: a lemma or file with no dependency on in-flight work, a
      self-contained proof gap, a certificate to discharge, a blueprint
      chapter to write, an audit-script improvement. File these so another
      agent (human or AI) can pick the issue up and open a PR against
      LANA-Project/heights. Write the description so a stranger could start
      cold: which file/theorem/definition, what already exists nearby to
      build on, what the deliverable looks like (a signature, a sorry to
      close, a chapter to write), and a pointer to the relevant
      Plans/HeightsSpec.md section if one exists.

Do NOT file for: routine progress, individual commits, or work the current
run will finish itself in the next commit or two — only for work that is
genuinely separable from what's in flight. Always check existing open issues
first (GET /issues, filter to children of 32) to avoid duplicates; if an
existing issue covers it, comment instead of re-filing.

LABELING (owner directive 2026-07-20): every parallelizable-subtask issue
(case (b) above) MUST be labeled `ready-to-clanck` (existing board label, id
3) at creation time — this is how other agents discover work they can pick up
right now. Only label it `ready-to-clanck` if it is genuinely actionable
standalone: self-contained description, no dependency on unpushed/in-flight
work, clear deliverable. Big-subproject issues (case (a)) do not need this
label unless a specific first slice of them is itself immediately actionable
(in which case file that slice as its own labeled child issue, separate from
the umbrella issue). If a filed issue's dependency later resolves, add the
label then via the same PATCH call.

API cheatsheet:
  # read an issue (rich: comments/events/artifacts)
  curl -sS "$TAXIS_URL/issues/32" -H "Authorization: Bearer $TAXIS_TOKEN"
  # list issues
  curl -sS "$TAXIS_URL/issues" -H "Authorization: Bearer $TAXIS_TOKEN"
  # list all labels (to get ids/names; ready-to-clanck is id 3)
  curl -sS "$TAXIS_URL/labels" -H "Authorization: Bearer $TAXIS_TOKEN"
  # create a subtask/subproject issue
  curl -sS -X POST "$TAXIS_URL/issues" -H "Authorization: Bearer $TAXIS_TOKEN" \
    -H 'Content-Type: application/json' \
    -d '{"title":"...","description":"... (self-contained: file/theorem, context, deliverable, spec pointer)","parent":32}'
  # label an issue (replaces the full label set — pass all label ids you want kept)
  curl -sS -X PATCH "$TAXIS_URL/issues/<id>" -H "Authorization: Bearer $TAXIS_TOKEN" \
    -H 'Content-Type: application/json' -d '{"labels":[3]}'
  # comment on an issue
  curl -sS -X POST "$TAXIS_URL/issues/<id>/comments" -H "Authorization: Bearer $TAXIS_TOKEN" \
    -H 'Content-Type: application/json' -d '{"body":"..."}'
    (verify this route on first use; if it 404s, inspect the SPA bundle for the comment route)

pi-agent rule: the pi agent, while working, should proactively look for (a)
big-subproject-scale gaps and (b) parallelizable subtasks it is not itself
about to do, and file AND label them per the above as it goes (not just
report them at the end) — fan out generously; more small, clearly-scoped
`ready-to-clanck` issues is the goal, so other agents have real work to pick
up. The orchestrator deduplicates before filing anything itself and records
issue ids (and their labels) in the work log (id only, never the token).
