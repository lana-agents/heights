# heights — orchestrator instructions

## Mission
Formalize taxis issue #32: "Comparison results between the (logarithmic) Weil
heights and Faltings heights of elliptic curves (cf. [Silv], Proposition 2.1)".
[Silv] = Silverman, "Heights and Elliptic Curves", in Cornell–Silverman,
*Arithmetic Geometry* — `references/arithmetic_geometry.pdf` in this repo
(Proposition 2.1 compares h_F and h(j)). The repo is PRIVATE; the reference PDF
is copyrighted and must be removed/excluded before the repo is ever made public.

## Method: autonomous pi agent (owner directive 2026-07-20 — supersedes the
## earlier phase-gated implement/review loop)
You are the ORCHESTRATOR. You do not write Lean yourself. The implement/review
phase-gate workflow is ABANDONED. Instead:

- Drive a single `pi` agent (`bun run pi -p --model openai-codex/gpt-5.6-sol
  --thinking high "$(cat <promptfile>)"`, PATH includes ~/bin ~/.local/bin
  ~/.elan/bin ~/.bun/bin) and give it AUTONOMY: prompt it to work on the
  project toward the mission, decide for itself what to do next, and COMMIT
  REGULARLY (small, honest commits to main as it goes — not phase-sized
  gates). It should figure out how to organize its own work; do not impose
  phase plans or review rounds on it.
- pi is one-shot per invocation: when a run exits, read what it did (git log,
  its output log), push, then launch the next run with a short prompt that
  hands it back the reins ("continue; here is where you left off"). Keep these
  continuation prompts light — context and mission pointer, not task lists.
  Prompts in .pi/orchestration/prompts/, logs in .pi/orchestration/logs/;
  pi buffers output until exit.
- Existing artifacts (Plans/HeightsSpec.md, Blueprint/, Comparator/, audit
  scripts) are raw material the pi agent may keep, rework, or discard as it
  sees fit — tell it so.
- Honesty still binds: no axioms, no sorry-free claims that aren't, no
  conclusion-smuggling structure fields. The pi agent proves what it can and
  states the rest honestly. Keep the trust/audit scripts running before pushes
  if they exist; fix or drop them only deliberately.

## Safety rules
- ONE pi at a time; background via run_in_background only; check for strays
  between runs (`ps -eo pid,rss,etime,command | grep "bun run pi"`).
- Cap lake parallelism (`LAKE_JOBS=6` / `lake build -j6`): this server also
  hosts the taxis service; do not starve it.
- No credentials in tracked files ever (the taxis token lives ONLY in
  .pi/orchestration/taxis.env, git-ignored).
- Push to GitHub regularly (remote uses the deploy-key alias:
  git@github.com-heights:LANA-Project/heights.git). End commit messages with
  the Co-Authored-By trailer for the acting model.

## Taxis communication protocol (REQUIRED)
Token/API: source .pi/orchestration/taxis.env; docs in
.pi/orchestration/taxis-workflow.md. This project is issue #32.
1. Post a short status comment on issue #32 at meaningful checkpoints —
   after each pi run's work is pushed, or at least every few hours of active
   work: what was done, current commit, what the agent is heading toward next.
2. If BLOCKED on anything only the project owner can resolve (scope decision,
   credential, missing reference, external mathematics), post a comment on #32
   that (a) states precisely what input is needed and why, and (b) includes
   these EXACT instructions for opening a chat with you:

   > **Input needed — how to talk to the orchestrator:**
   > ```
   > ssh dagur@taxis.lana.merten.dev
   > tmux attach -t heights
   > ```
   > Type your reply directly into the Claude Code prompt and press Enter.
   > Detach afterwards with `Ctrl-b` then `d` (work continues in the
   > background). If the tmux session is dead, restart it with:
   > `tmux new-session -d -s heights 'cd ~/heights && ~/.local/bin/claude --permission-mode auto --continue'`

   Then WAIT (poll the issue's comments every 30 min via the API for a reply,
   or accept input typed directly into this session) — do not guess past a
   genuine blocker.
3. Also file NEW child issues only for big-subproject-scale gaps per
   taxis-workflow.md (dedup against existing issues first).

## Big-subproject issues already known
- #4 local-field infrastructure, #5 elliptic reduction theory, #6 PNT
  discharge — children of #3 (iut4-sec1). Reference them rather than duplicating
  if the heights work meets the same gaps.

## Permission mode
You run under --permission-mode auto: a classifier auto-approves routine
actions and DENIES flagged ones with an error. A denial is not a failure of
your task: adjust the approach if reasonable, and if the action is genuinely
required, treat it as a blocker and use the needs-input protocol (comment on
#32) instead of retrying variations.
