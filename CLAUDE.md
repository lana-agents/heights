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

## Parallel sub-issue agents (owner directive 2026-07-20)
In addition to the main-line autonomous pi agent working on `main`, launch
separate pi agents against `ready-to-clanck` child issues of #32 so they run
in parallel. Protocol:
- Each parallel agent gets its own `git worktree add ../heights-issue-<id>
  issue-<id>` (branch off current `main`) — never share a working tree
  between concurrently running pi processes.
- CLAIM before starting (dedup against other agents/lines, board-wide
  convention): PATCH `/issues/<id>` labels to swap `ready-to-clanck` (3) for
  `o-claimed` (4), PATCH `assignees:[6]`, and post a claim comment naming the
  branch/worktree. Re-fetch the issue immediately before claiming — skip if
  already claimed/closed by the time you look (race with another agent or the
  main line).
- The agent works its worktree, commits as it goes (small honest commits,
  same conventions as the main line), and when done pushes the branch:
  `git push origin issue-<id>`.
- No `gh` CLI or GitHub API PR-creation token exists on this server yet (only
  the push-only deploy key) — so real GitHub PRs aren't possible right now.
  Interim: after a branch is pushed, run its checks (ci-checks.sh / trust +
  axiom audits / full build) from the worktree; if clean, merge into `main`
  yourself (`git merge --no-ff issue-<id>`), push `main`, delete the worktree
  and branch, and set the issue's label to `o-in-review` while you post the
  merge commit, then close the issue once you've confirmed it's genuinely
  resolved. If checks fail or the work is unclear, label `o-blocked` (or
  `o-rejected` if the approach was wrong) and comment why — do not merge
  broken or dubious work. If you later get a real GitHub token, switch to
  actual PRs instead of self-merging.
- Concurrency cap: at most 3 parallel sub-issue pi agents running at once (in
  addition to the one main-line pi), each with `LAKE_JOBS=4` (server has 16
  cores; leaves headroom for the main line's build and the taxis service).
  Check for stray processes before launching more
  (`ps -eo pid,rss,etime,command | grep "bun run pi"`).
- If you filed `ready-to-clanck` issues that never actually got the label set
  (check via GET before assuming) — labels PATCH may have been missed in an
  earlier run — fix the label first, or just claim+work them directly since
  claiming already supersedes the ready label.

## Safety rules
- Background all pi invocations via run_in_background only; check for strays
  between runs (`ps -eo pid,rss,etime,command | grep "bun run pi"`).
- Cap lake parallelism per process (`LAKE_JOBS=6` main line / `LAKE_JOBS=4`
  parallel sub-issue agents): this server also hosts the taxis service and
  runs multiple pi processes concurrently now — do not starve it.
- No credentials in tracked files ever (the taxis token lives ONLY in
  .pi/orchestration/taxis.env, git-ignored).
- Push after EVERY commit (owner directive, revised): do NOT rely on the pi
  agent to push mid-run. Instead YOU (the orchestrator) push after each pi run
  exits, AND poll for new commits while a pi run is in progress (e.g. every
  few minutes via a background check of git log / rev-list --count
  origin/main..HEAD) and push immediately whenever new commits appear, without
  waiting for the run to finish. This gives push-after-every-commit behavior
  even though pi itself is one-shot per invocation. (remote uses the
  deploy-key alias: git@github.com-heights:LANA-Project/heights.git). End
  commit messages with the Co-Authored-By trailer for the acting model.

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
3. File NEW child issues (parent: 32) proactively per taxis-workflow.md,
   broadened per owner directive 2026-07-20 — not just big subprojects but
   also PARALLELIZABLE SUBTASKS: any well-scoped, separable piece of work
   another agent (human or AI) could pick up independently and complete as a
   PR against LANA-Project/heights, right now, without waiting on the current
   pi run. Do this as you go, not only at the end of a run. Dedup against
   existing open issues first (GET, filter to children of 32).

## Related issues (different project — do not conflate)
- #4 local-field infrastructure, #5 elliptic reduction theory, #6 PNT
  discharge — children of #3 (iut4-sec1, a separate project). Reference them
  only if the heights work happens to hit the same underlying library gap;
  heights' own subtask/subproject issues are children of #32, not #3.

## Permission mode
You run under --permission-mode auto: a classifier auto-approves routine
actions and DENIES flagged ones with an error. A denial is not a failure of
your task: adjust the approach if reasonable, and if the action is genuinely
required, treat it as a blocker and use the needs-input protocol (comment on
#32) instead of retrying variations.
