---
name: adapt-file-to-mathlib
description: Bring a whole SKW file up to Mathlib form, in place. Use when the user says to adapt a file to Mathlib, prepare a file for upstreaming, or asks for Mathlib formatting, naming or docstrings on a file.
allowed-tools: Read, Edit, Write, Bash, Glob, Grep
---

# Adapting an SKW file to Mathlib

A whole file is brought to the state Mathlib would accept: dependencies accounted for,
header and docstrings in Mathlib form, declarations named by Mathlib conventions. The
file **stays in SKW** while this happens, and keeps compiling there — do not copy it into
a mathlib clone, and do not open a PR as part of this skill (`upstream-to-mathlib`
handles the PR when the file is ready).

**This is a pass, not a one-shot pipeline.** Every time the file changes — a new proof, a
changed construction, a new declaration — the pass is run again on what changed. Expect
the author to rework the file between passes; the earlier steps' conclusions (which
dependencies, which names) are not permanent.

**Scope discipline.** This skill adapts; it does not review the mathematics and does not
second-guess the author. A lemma in the file is there for a reason: do not delete it,
weaken it, or replace it with a composition of Mathlib lemmas because that looks tidier.
Suggest such things separately, afterwards, if at all.

## While iterating, build only the file

```bash
lake build SKW.<Module.Of.The.File>
```

The whole-project build belongs to the last step. Building everything after each edit
wastes minutes per iteration.

## 1. Find the dependencies that are not in Mathlib

The file must end up resting only on Mathlib, plus whatever this skill decides to carry
with it. Find what it still needs from SKW:

- List the file's imports. An aggregate import such as `SKW.Misc` hides everything, so
  replace it with the specific Mathlib imports the file really uses plus the specific SKW
  file(s) whose declarations it needs, then let the compiler tell you what is missing.
- For each name the compiler reports as unknown, locate it:
  ```bash
  grep -rn "theorem <name>\|def <name>" SKW --include="*.lean"
  grep -rln "<name>" .lake/packages/mathlib/Mathlib --include="*.lean"
  ```
- **The build stops at the first error, so step 1 is not finished until the file compiles.**
  Stub the offending call (`sorry -- TEMP: needs <name>`), rebuild, and repeat until it
  builds. Only then do you know the full list. Remove the stubs afterwards.

## 2. Decide what happens to each dependency

- **Too small for a PR of its own** (a `rfl` lemma, a one-line restatement): it is
  *associated with this file* and ships in the same PR. Note it, and say so in a comment
  on the SKW import that provides it (see step 3).
- **Big enough to stand alone**: flag it as a **priority upstream candidate**, and record
  that in `~/Desktop/Claude/plan_kronecker_weber.md` (the on-disk plan), since the file
  cannot go upstream before it does.

Record the disposition in the plan either way: the next pass should not have to
rediscover it.

## 3. Formatting

- **Copyright header**, exactly Mathlib's shape, above `module`:
  ```lean
  /-
  Copyright (c) <year> Xavier Roblot. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Xavier Roblot
  -/
  ```
- **Imports**: explicit Mathlib imports, **sorted alphabetically**, in their own block;
  remaining SKW imports in a block below, each **with a comment naming the declarations it
  is there for** and their step-2 disposition. A reader must not have to guess why an
  `SKW.*` import survives.
- **Module docstring** right after the imports: title, then (filled in at step 5)
  the paragraph, `## Main definitions`, `## Main results`, `## Tags`.
- **`public section`, plain** — never `@[expose] public section` (see the project memory
  `feedback_public_section_expose_selectively`). `@[expose]` goes only on an individual
  `def` that genuinely needs its body visible.

**Gotcha, every time:** dropping `@[expose]` breaks any `theorem foo_apply … := rfl`
("This theorem is exported from the current module. This requires that all definitions
that need to be unfolded to prove this theorem must be exposed"). The fix is `:= by rfl`;
the `def` itself stays unexposed, because that `_apply` lemma *is* its unfolding API.

## 4. Naming: the defs first, then the theorems

Invoke `lean:mathlib-review` for this step — naming is what a reviewer will spend their
time on, and renaming later is expensive.

- **Defs first**, because every theorem name keys off the def's name and namespace. A
  root-namespace definition will not be accepted; pick the namespace from the first
  explicit argument (dot-notation) or from what the definition produces, and check the
  precedents in the destination file: e.g. inside `AddChar`, Mathlib keeps the `Char`
  suffix (`zmodChar`, `primitiveZModChar`), so `traceChar` fits and `trace` does not.
- **Ask the author before applying**, with the alternatives and a recommendation. The
  author may already be planning to change the construction, which changes the right
  name — that is exactly what happened with `addCharTrace`, where an `Ideal.` namespace
  was wrong because the ideal was about to disappear.
- **Then the theorems**, named after the conclusion: `isPrimitive_traceChar`, not
  `traceChar_isPrimitive`, when the conclusion's head is `AddChar.IsPrimitive`.
- **Park the names that depend on a shape about to change** rather than guessing; say
  which and why.
- Apply renames **across the whole project** in one pass (step 6 checks it).

## 5. Docstrings

- **The def gets one**, always.
- **The important results get one.** Not every result: the signal for "important" is use
  outside the file —
  ```bash
  grep -rn "<name>" SKW --include="*.lean" | grep -v "<the file>" | wc -l
  ```
  plus the workhorse lemmas the file's own proofs lean on. Statement-is-documentation
  lemmas (`_apply`, `_eq_one_iff`) do not need prose.
- **Then complete the module docstring** with those same declarations: one opening
  paragraph saying what the construction is and what the file establishes, the defs under
  `## Main definitions`, the important results under `## Main results`, each with one line
  of mathematics rather than a restatement of the Lean.

Keep docstrings to the project's style: one or two lines, stating the fact, no bold
headers or motivation essays (`feedback_short_docstrings`).

## 6. Propagate to the rest of the project

- The renames of step 4 must reach every call site.
- Replacing an aggregate import with explicit ones can break *other* files that were
  getting declarations transitively through this one. This is the step where that shows up.
- The call sites are not only Lean code: the **blueprint** cites declarations by name in
  `\lean{...}`, and `checkdecls` validates each one against the built library, so a rename
  that misses `blueprint/src/content.tex` turns CI red even though the project builds.
- The check is the **whole-project build**, not the file's, plus the blueprint:
  ```bash
  lake build
  grep -n "<old name>" blueprint/src/content.tex
  ```
- Then commit (ask first, as always).

## Notes

- Worked example: `SKW/Stickelberger/AddCharTrace.lean`, 6 October 2026. One dependency
  (`Ideal.absNorm_eq_card`, a `rfl` lemma) → ships with the file; `SKW.Misc` replaced by
  four sorted Mathlib imports; `@[expose]` dropped, which forced `traceChar_apply := by rfl`;
  def named `AddChar.traceChar` by the author, seven theorems renamed, four parked pending
  an ideal-free construction; docstrings on the def and the four results used elsewhere;
  15 call sites updated in three other files.
