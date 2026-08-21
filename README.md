# Lean tutorial

A three-hour, hands-on introduction to the [Lean 4](https://lean-lang.org)
theorem prover and [Mathlib](https://github.com/leanprover-community/mathlib4),
for people who have never used a proof assistant.

The material is split so that **quantifiers get their own hour**. Part 2 stays
deliberately quantifier-free so that learners can pick up the tactics on
familiar algebraic ground; Part 3 then introduces `∀`/`∃` as the only new idea,
with analysis as the setting. In our experience that is the wall beginners hit,
and separating it out is worth the extra session.

## Session plan (≈3 hours)

| | Part | Time | Contents |
| - | ---- | ---- | -------- |
| 1 | [What is Lean?](LeanTutorial/Part1_WhatIsLean.lean) | 45 min | installation, terms and types, propositions as types, first tactic proofs |
| 2 | [Algebra](LeanTutorial/Part2_Algebra.lean) | 60 min | `ring`, `rw`, `linarith`, `norm_num`, `calc`, `have`, `field_simp`, abstract groups and rings |
| 3 | [Analysis](LeanTutorial/Part3_Analysis.lean) | 75 min | `∀`/`∃` discipline, quantifier order, `push Not`, ε–N limits, ε–δ continuity |

Each part ends with exercises marked `sorry`. Worked answers are in
[`LeanTutorial/Solutions.lean`](LeanTutorial/Solutions.lean).

Budget roughly half of each part for the learners typing, not for slides. The
info view — Lean's live goal display — is the actual teaching tool; everything
else is scaffolding around it.

## Getting a working Lean

Two routes. **For a workshop, use Codespaces** — a local Lean install is a fine
thing to own, but it is a bad thing to debug for twenty people at once while
the clock runs.

### Option A — GitHub Codespaces (nothing to install)

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/hyunsanghwang/Lean_tutorial)

Click the badge, or **Code → Codespaces → Create codespace on main**. You get
VS Code in the browser with Lean, Mathlib and this repository already set up.
Works on a Chromebook or an iPad. Configuration lives in
[`.devcontainer/`](.devcontainer).

Notes for the organiser:

* **Have students create their Codespace the day before the session**, wait
  for setup to finish, then stop it. A Codespace keeps its `.lake` directory
  across stop and resume, so on the day it comes back in seconds. This is the
  single most important piece of logistics — do not let twenty people run that
  build simultaneously at 09:00.

  Setup downloads prebuilt Mathlib and builds the tutorial. CI performs the
  identical work on the same Linux and the same four cores, from a cold cache,
  in about two and a half minutes; a Codespace also builds the container image
  first, so tell students to expect roughly five and not to worry at ten. The
  window stays on "Setting up your codespace" until it is genuinely ready.
* GitHub's *prebuild* feature would automate this, but it requires a Team or
  Enterprise Cloud organisation, and this repository lives on a personal
  account, so the option does not appear under Settings → Codespaces. The
  day-before trick is the equivalent and works just as well for a scheduled
  session.
* **Students need read access to the repo.** This repository is public, so
  anyone with the link can create a Codespace from it — nothing to arrange in
  advance. If you fork it into a private repository, remember to add the
  participants first.
* **Watch the quota.** Codespaces bills by core-hour, so the 4-core machine
  costs 4 core-hours per wall-clock hour — roughly 12 for a three-hour session,
  plus storage for however long the Codespace lives. Personal accounts have a
  free monthly allowance (at the time of writing, 120 core-hours and 15 GB of
  storage), which one session fits inside comfortably; check the current
  figures before relying on it.
* Tell everyone to **stop their Codespace** at the end (they also auto-stop
  after 30 minutes idle, and are deleted after 30 days of inactivity).
* `hostRequirements` pins the machine to 4 cores, which leaves exactly one
  option in the size picker: 4 cores / 16 GB RAM / 32 GB storage. That is
  deliberate — Mathlib's language server thrashes on smaller machines, and one
  option means nobody picks wrong.

### Option B — local installation

Have participants do this **before** the session — the Mathlib download is a
few GB and will not finish over conference wifi.

1. **Install VS Code**: <https://code.visualstudio.com>

2. **Install the Lean 4 extension**: open VS Code, go to Extensions
   (`Ctrl/Cmd + Shift + X`), search for `lean4`, install the one published by
   `leanprover`. It will offer to install Lean itself (via `elan`) the first
   time you open a Lean file — accept.

   Command-line alternative:

   ```sh
   curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
   ```

3. **Get this repository and its dependencies**:

   ```sh
   git clone https://github.com/hyunsanghwang/Lean_tutorial.git
   cd Lean_tutorial
   lake exe cache get     # downloads prebuilt Mathlib — do not skip this
   lake build
   ```

   `lake exe cache get` fetches Mathlib already compiled. Without it, `lake
   build` compiles Mathlib from source, which takes hours.

4. **Open the folder in VS Code** (`File → Open Folder`, choose
   `Lean_tutorial`) and open `LeanTutorial/Part1_WhatIsLean.lean`. If the info
   view does not appear on the right, press `Ctrl/Cmd + Shift + Enter`.

### Checking it works

Put your cursor at the end of this line in any Lean file:

```lean
#eval 2 + 2
```

The info view should say `4`. If it does, you are ready.

**Do not use Safari for a Codespace.** The info view is a webview, and in
Safari it renders blank — Lean works, the file compiles, the goals simply never
appear. Since the info view *is* the teaching tool, that is a dead session.
Use Chrome or Edge, or open the Codespace in desktop VS Code. Tell students
this in advance; on a Mac, Safari is the default they will reach for.

If the info view is blank in a supported browser, check where your cursor is
before assuming a fault: term-mode proofs such as `theorem foo : P := rfl` have
no intermediate goals, so an empty pane there is correct. Put the cursor at the
end of an `#eval` or `#check` line to confirm the view is alive.

### Last-resort fallback

If a laptop refuses to cooperate and Codespaces is unavailable, [Lean 4
Web](https://live.lean-lang.org) runs Lean with Mathlib in the browser. Paste a
part file in and it works — slower, and with no project set-up at all.

## How to work through a file

* Put the cursor at the end of a line; the **info view** shows the goal state at
  that point. Moving the cursor through a proof replays it step by step.
* Orange squiggles mean "still processing", red means an error, and a file with
  no red is a file Lean has fully checked.
* `sorry` is an admitted goal. It makes a file compile with a warning, which is
  exactly what the exercises rely on — fill them in one at a time.
* **Opening a file takes a few seconds while Lean loads its imports**, and the
  info view stays empty until it finishes. Parts 1 and 2 import only what they
  use and load in about six seconds; Part 3 imports all of Mathlib's tactics so
  that `exact?` and `apply?` can actually find things, and takes about thirty.
  Tell students to open the next part *before* the break, not after it.
* Stuck? `exact?` searches Mathlib for a lemma that closes the goal, `apply?`
  for one that makes progress, and `hint` just tries a batch of standard
  tactics. [Loogle](https://loogle.lean-lang.org) searches by shape.

## Repository layout

```
LeanTutorial.lean               root module, imports everything
LeanTutorial/
  Part1_WhatIsLean.lean         part 1
  Part2_Algebra.lean            part 2
  Part3_Analysis.lean           part 3
  Solutions.lean                worked answers to all exercises
lakefile.toml                   package definition (depends on Mathlib)
lean-toolchain                  pinned Lean version — do not edit by hand
.devcontainer/                  GitHub Codespaces / dev container definition
.github/workflows/              CI: builds the whole tutorial on every push
LICENSE                         Apache License 2.0
```

CI runs `lake build` with the Mathlib cache on every push and pull request, so
a broken proof is caught immediately. The `sorry`s in the exercises are
warnings, not errors, so the build stays green.

`.github/workflows/update.yml` can be run manually to open a PR bumping Mathlib
to a newer release. That requires **Settings → Actions → General → Allow GitHub
Actions to create and approve pull requests** to be enabled.

## Further reading

* [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
  — the standard next step, a full book with exercises.
* [The Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4)
  — a browser game teaching induction and rewriting. Excellent warm-up homework.
* [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
  — the reference for the underlying type theory.
* [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/)
  and the [Lean Zulip](https://leanprover.zulipchat.com), where questions get
  answered quickly and kindly.

## License

Apache License 2.0 — see [`LICENSE`](LICENSE). You are welcome to fork this,
adapt it for your own group, and teach from it.
