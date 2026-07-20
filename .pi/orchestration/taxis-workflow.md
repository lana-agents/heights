# Taxis issue-tracker workflow (orchestrator + pi agents)

Server: https://taxis.lana.merten.dev (REST under /api, no MCP endpoint).
Auth: `source .pi/orchestration/taxis.env`, then `-H "Authorization: Bearer $TAXIS_TOKEN"`.
Bot identity: dagur-clanker (id 6).

SECRECY: the token must NEVER appear in tracked files, commits, logs quoted into
tracked files, or work-log entries. The repo is public. Refer to this file by
path instead.

Project issue: #3 (iut4-sec1). All subproject issues are created with "parent": 3.
Existing children: #4 local-field analytic infrastructure (P5-P11 stack);
#5 elliptic reduction theory (Prop 1.8(v)-(vii) certificate discharge);
#6 PrimeCountingCertificate discharge via PrimeNumberTheoremAnd (Prop 1.6).

WHEN to file: only genuinely big subprojects — a library gap or work stream that
is its own multi-phase project (mathlib-scale infrastructure, certificate
discharge projects). NOT phase-sized tasks, review findings, or fixes; those
stay in the spec/work log. Check the existing children first (GET) to avoid
duplicates; if an existing issue covers it, add a comment instead.

API cheatsheet:
  # read an issue (rich: comments/events/artifacts)
  curl -sS "$TAXIS_URL/issues/3" -H "Authorization: Bearer $TAXIS_TOKEN"
  # list issues
  curl -sS "$TAXIS_URL/issues" -H "Authorization: Bearer $TAXIS_TOKEN"
  # create a subproject issue
  curl -sS -X POST "$TAXIS_URL/issues" -H "Authorization: Bearer $TAXIS_TOKEN" \
    -H 'Content-Type: application/json' \
    -d '{"title":"...","description":"... (mention iut4-sec1 phase/spec section that surfaced it)","parent":3}'
  # comment on an issue
  curl -sS -X POST "$TAXIS_URL/issues/<id>/comments" -H "Authorization: Bearer $TAXIS_TOKEN" \
    -H 'Content-Type: application/json' -d '{"body":"..."}'
    (verify this route on first use; if it 404s, inspect the SPA bundle for the comment route)

pi-agent rule: implementers/reviewers who identify a big-subproject-scale gap
report it in their final message AND may file it per the above; the orchestrator
deduplicates and records the issue id in the work log (id only, never the token).
