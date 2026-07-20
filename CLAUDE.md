# heights — orchestrator instructions

## Mission
Formalize taxis issue #32: "Comparison results between the (logarithmic) Weil
heights and Faltings heights of elliptic curves (cf. [Silv], Proposition 2.1)".
[Silv] = Silverman, "Heights and Elliptic Curves", in Cornell–Silverman,
*Arithmetic Geometry* — `references/arithmetic_geometry.pdf` in this repo
(Proposition 2.1 compares h_F and h(j)). The repo is PRIVATE; the reference PDF
is copyrighted and must be removed/excluded before the repo is ever made public.

## Method: phase-gated pi orchestration
You are the ORCHESTRATOR. You do not write Lean yourself. Drive the `pi` coding
agent (invoke as `bun run pi -p --model openai-codex/gpt-5.6-sol --thinking
high|medium "$(cat <promptfile>)"`, PATH includes ~/bin ~/.local/bin ~/.elan/bin)
in one-shot implementer/reviewer rounds, exactly one pi process at a time,
launched in background without inner `&`. Prompts in .pi/orchestration/,
logs beside them. pi buffers output until exit — poll by process exit.

Copy the methodology proven in https://github.com/LANA-Project/iut4-sec1
(public; read its Plans/Iut4Sec1Spec.md and README for the shape):
spec-author round → adversarial review gate → phase implementer → adversarial
reviewer, CHANGES REQUESTED loops capped at 4 rounds; phase gates recorded in
the spec's review log; push to GitHub at accepted gates (remote uses the
deploy-key alias: git@github.com-heights:LANA-Project/heights.git).
Structure: verso blueprint (template: github.com/chrisflav/proetale
blueprint-verso), leanprover/comparator challenge/solution pair (headline:
mathlib-statable form of the Weil/Faltings comparison; challenge = import
Mathlib only, sorried target suite; config lists only proved theorems),
trust/axiom audit scripts, honesty boundary (Faltings height may need explicit
interface/certificate structures if mathlib lacks it — never axioms, never
conclusion-smuggling structure fields; spec must draw the boundary explicitly).

## Safety rules
- ONE pi at a time; background via run_in_background only; check for strays
  between phases (`ps -axo pid,rss,etime,command | grep "bun run pi"`).
- Cap lake parallelism (`LAKE_JOBS=6` / `lake build -j6`): this server also
  hosts the taxis service; do not starve it.
- No credentials in tracked files ever (the taxis token lives ONLY in
  .pi/orchestration/taxis.env, git-ignored; audit scripts must reject
  credential patterns, as in iut4-sec1).
- Commit convention: phase-sized commits to main, `P<n>: <summary>`; end commit
  messages with the Co-Authored-By trailer for the acting model.

## Taxis communication protocol (REQUIRED)
Token/API: source .pi/orchestration/taxis.env; docs in
.pi/orchestration/taxis-workflow.md. This project is issue #32.
1. At EVERY closed phase gate (accepted review), post a short status comment on
   issue #32: phase, commit, what is now proved/stated, next phase.
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
