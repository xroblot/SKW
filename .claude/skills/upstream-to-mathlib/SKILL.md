---
name: upstream-to-mathlib
description: Find code in SKW that's ready to be upstreamed to Mathlib4 and prepare/open the corresponding PR from the user's fork.
---

# Upstreaming SKW code to Mathlib4

SKW carries lemmas written as generalizations of, or complements to, existing Mathlib
files, with the explicit intent of eventually moving them upstream (see e.g. the
`/-! # Generalizations of Mathlib.FieldTheory.KummerExtension -/` section in
`SKW/Prereqs/KummerExtension.lean`). This skill locates such code and turns it into
a Mathlib4 PR.

## 1. Find candidates

### Stage 1 — narrow with the import filter (mechanical, cheap)

Code that's a clean generalization of Mathlib API can't depend on anything
project-specific, so it can only import Mathlib (plus other such files). Filter out
everything that imports an `SKW.*` file — that's an immediate, reliable signal that a
file is entangled with this project's setup:

```bash
for f in $(find SKW -name "*.lean"); do
  grep -qE "^(public )?import " "$f" && \
  grep -E "^(public )?import " "$f" | grep -qv "Mathlib\." || echo "$f"
done
```

In SKW (as of 2026-06), this shrinks 22 files to 7: the five `SKW/Prereqs/*.lean` files
that read as plain Mathlib-namespace lemma collections (`NumberTheory`, `Digits`,
`AlgebraMisc`, `MulChars`, `IntermediateFields` — e.g. theorems named
`NumberField.Units.*`, `Finset.*`, `MulEquiv.*`, `MulChar.*`), plus
`KummerExtension.lean` and `Reduction.lean`.

### Stage 2 — read content, because the filter isn't sufficient

A file can pass Stage 1 and still be pure project content: `Reduction.lean` only
imports Mathlib, but its module docstring says *"This file establishes the reduction
steps that allow us to prove Kronecker-Weber by induction"* — entirely specific to this
project's proof strategy, not upstreamable. So for each file that survives Stage 1,
read its declarations and ask, **per declaration**:

- Is it a *generalization or complement of existing Mathlib API* (something Mathlib
  itself would plausibly want), or an *application* of that API to this project's
  specific goal? The two can sit in the same file — e.g. in `KummerExtension.lean`,
  `PowerBasis.ofAdjoinSimpleEqTop`, `rootOfSplitsXPowSubC'`, and
  `IsPrimitiveRoot.eq_pow_mul_of_pow_eq` are generic candidates, while
  `isGalois_iff_forall_apply_eq_pow_mul_zpow` — after a `variable` block introducing
  `F`/`K`/`Ω`/`μ` — is the project-specific Kummer-criterion application built *on top*
  of them.
- Is it sorry-free and fully proved?

**Don't rely on a fixed keyword grep for "generalizes"/"upstream"-style phrasing** —
wording varies too much to catch reliably. One doc-string says "Generalizes
`rootOfSplitsXPowSubC`..."; another says "Version of `PowerBasis.ofAdjoinEqTop` for
`IntermediateField.adjoin`" with no "generalize" anywhere. The real signal is
*backtick-quoted references to non-`SKW` Mathlib declarations* in the doc-string —
that marks "this is about Mathlib's API" regardless of phrasing — combined with the
structural seam where generic lemmas give way to a `variable` block carrying the
project's own notation.

Use `lean_file_outline` or `grep -n "^lemma\|^theorem\|^def\|^noncomputable\|^/-!"` to
get the declaration list per file quickly.

### Stage 3 — pick a *good first* candidate by size and cohesion

Not all valid candidates are equally good *starting points*. Mathlib PRs review faster
and merge more easily when they're small and self-contained, so prefer:

- **Neat, short proofs** — aim for declarations whose proof bodies run roughly 1–20
  lines (`rfl`, one-liners, small structure literals, short calc chains). Long, fiddly
  proofs slow down review and are riskier to port (they may lean on SKW-local lemmas in
  non-obvious ways).
- **A cohesive cluster, not a lone lemma** — group declarations that are *about the same
  underlying idea* and naturally belong together (a `def` plus its `@[simp]` API lemmas,
  or a statement proved for two parallel cases). Splitting such a cluster across PRs
  produces an inconsistent, half-finished-looking diff; bundling unrelated lemmas
  produces a PR reviewers will ask you to split. Related-and-bundled is the sweet spot.
- **Target under ~50 lines of actual code** for a first PR; up to ~200 lines is
  acceptable when the cluster genuinely doesn't split further, but treat 200 as a hard
  ceiling, not a target. If you find a good cluster that's too big, the right move is
  to draft the PR with everything connected, then split it — not to arbitrarily cut a
  cohesive group in half from the start.

**Worked example** — `SKW/Prereqs/AlgebraMisc.lean:32–74` (~43 lines) is a strong first
candidate:
```
RingEquiv.toRatAlgEquiv, _toRingEquiv, _apply, AlgEquiv.toRingEquiv_toRatAlgEquiv,
RingEquiv.equivRatAlgEquiv,
RingEquiv.toIntAlgEquiv, _coe, _apply, _injective
```
One idea stated for `ℚ` and `ℤ` ("a `RingEquiv` is canonically a `ℚ`-/`ℤ`-algebra
isomorphism, since that algebra structure is unique") — every proof is `rfl` or a 2-line
structure literal, and the `ℚ`/`ℤ` halves clearly belong in one PR together.

Two extra checks that helped confirm it was a *good* (not just *valid*) pick:
- **Not already in Mathlib**: `grep -rn "toRatAlgEquiv\|toIntAlgEquiv\|equivRatAlgEquiv"
  mathlib4-alt/Mathlib --include="*.lean"` came back empty — genuinely missing, not a
  near-duplicate that'd get bounced.
- **Battle-tested, not speculative**: `grep -rn "<name>" SKW --include="*.lean"` showed
  `toIntAlgEquiv` is actually used in `SKW/Stickelberger/Stickelberger.lean:55` — it's
  load-bearing code, not an untested generalization nobody needs.

Run both checks (against `mathlib4-alt/Mathlib` and against `SKW`) for whatever cluster
you're considering before committing to it.

Before doing any porting work, list the candidates for the user: file:line, a one-line
description of what it generalizes, and the Mathlib module it belongs in. Let the user
pick which one(s) to pursue — don't push multiple unrelated lemmas into a single PR.

## 2. Prepare the port

Working copy: `/Users/roblot/Desktop/EnCours/Lean/Lean4/mathlib4-alt`
(`origin` = user's fork `xroblot/mathlib4`, `upstream` = `leanprover-community/mathlib4`).

- `git fetch upstream && git checkout -b <branch-name> upstream/master`
  (branch from fresh `upstream/master`, not a possibly-stale local `master`).
- Move the declaration(s) into the right Mathlib file:
  - Drop the `SKW.*` namespace/imports; fit into existing `open`/`namespace` blocks.
  - Adjust naming to Mathlib conventions — run `lean:mathlib-review` on any new/changed
    names before committing to them (see project memory on naming).
  - Rewrite doc-strings in Mathlib doc style; remove references to SKW-internal
    declarations the Mathlib version won't have (e.g. "Generalizes
    `PowerBasis.ofAdjoinSimpleEqTop`" only makes sense inside SKW).
- Run `lake exe mk_all` if files were added or removed.
- Build the touched file(s) and confirm no errors/`sorry`: `lake build Mathlib.<Module>`.

## 3. Self-review the diff with `lean:mathlib-review`

Before opening the PR, always run the `lean:mathlib-review` skill on the ported
declarations and act on its findings — this is a required step, not optional. A Mathlib
reviewer will apply exactly these criteria, so catching them now avoids a review round
trip.

**Review the WHOLE diff, not the parts you happen to be thinking about.** Reviewing only the
names and the hypotheses, and skipping how the declarations read and where they sit, is not a
review — a reviewer reads every added line. Go through all of the following, every time, and
for each one either act on it or be able to say why it is fine:

- **Binder explicitness.** For each variable: can it actually be inferred? A variable that
  appears *only in instance arguments* cannot be inferred unless the expected type pins it, so
  it must be explicit — and it must match what the surrounding declarations in that file do.
  Deciding this requires imagining the use site, not just reading the statement.
- **Placement.** Put the declarations where a reader would look for them: in the section where
  the notions involved are in scope, next to the cluster they belong with, and *obeying the
  `variable` block already in force*. Adding a `variable` line to flip a binder for your own
  declarations is a sign they are in the wrong place.
- **Proof readability**, independently of whether it compiles: anonymous-constructor hypothesis
  grabs (`‹_›`), one-letter names, a second lemma repeating the first's argument instead of
  deriving it.

Then the usual points:

- **Naming.** The names that were fine inside SKW are often not the most idiomatic Mathlib
  names. Check the conclusion-describes-the-name convention and existing precedent (e.g.
  the `_op_algebraMap` suffix: `adjoin_simple_add_algebraMap`, not a bare `adjoin_simple_add`
  that reads ambiguously). Renaming here is cheap; renaming after review is not. Since the
  quarantined SKW copy (§5) keeps its original names, a Mathlib rename just means the
  post-merge redirect maps the SKW name to the new upstream name.
- **Missing API / attributes** on any new `def` (`@[simp]` lemmas, `@[ext]`, instances).
- **Style** the compiler won't flag: unsqueezed terminal `simp`, `erw`/`rfl`-after-`rw`
  smells, line length, docstrings on every new declaration.

Then confirm the touched module still builds and `lake exe runLinter Mathlib.<Module>`
passes after any changes the review prompted.

## 4. Commit, push, open the PR

Once the review has been acted on and the module builds and lints clean, carry this section
out without stopping to ask: commit, push, create the PR. The user picked the candidate in §1
and that choice is the go-ahead for the whole sequence, so don't re-confirm the commit message,
the push or the PR text — just apply the rules below and report the resulting URL.

Follow `lean:mathlib-pr` for fork/branch conventions and labels.

Commit message: the opening commit of the branch is named `1st commit`, and that convention
covers the first commit only — every later commit says what it does instead (`clean up`,
`review` for changes answering an actual reviewer comment, `fix after merge`); never continue
the numbering. The `<type>(<scope>): <subject>` line is the **PR title**, not a commit message.

PR description style (from project memory):
- **Short and non-technical.** A couple of sentences saying what the PR adds, in plain
  mathematical English. No hypothesis-by-hypothesis justification, no design discussion, no
  comparison with the alternatives considered — that belongs in the docstrings, or in a reply
  if a reviewer asks. A one-line PR gets a one-line description.
- No `Co-Authored-By` trailer in commit messages.
- Close the description with `:robot: This PR was extracted from the [SKW project](https://github.com/xroblot/SKW) by Claude.`
- No bold titles in the description body.
- List PR dependencies (`- [ ] depends on: #XXXX`) at the very bottom, after a `---`.

Steps:
- `git commit -m "1st commit"` with the reviewed diff.
- Push the branch to `origin` (the fork).
- `gh pr create --repo leanprover-community/mathlib4 --base master ...` with a HEREDOC
  body. Note the resulting PR number/URL — it's needed for the quarantine step below.

## 5. Quarantine the SKW copy in `PRed2Mathlib`

Once the PR is open (so you have its number to link), don't leave the ported
declarations sitting in their original SKW
file — that makes it easy to forget they're now duplicated upstream, and easy to lose
track of which PR they came from. Instead, move them into a mirror file under
`SKW/PRed2Mathlib/`, immediately, as part of opening the PR (not as a deferred TODO):

- **Mirror the path/filename**: `SKW/Prereqs/AlgebraMisc.lean` →
  `SKW/PRed2Mathlib/AlgebraMisc.lean` (so it's obvious at a glance which original file a
  quarantined cluster came from, even once there are several).
- **Move the declarations verbatim** (same names, same proofs — this is meant to be a
  pure relocation, not a rewrite) into the mirror file, with its own `module` header,
  `public import`s for whatever Mathlib API the cluster needs (drop SKW-internal imports
  that no longer apply), and `@[expose] public section`.
- **Add a module docstring linking the PR**, e.g.:
  ```
  /-!
  # PRed to Mathlib: `RingEquiv.toRatAlgEquiv` / `RingEquiv.toIntAlgEquiv`

  The declarations in this file were extracted from `SKW.Prereqs.AlgebraMisc` and submitted
  upstream as Mathlib PR [#40298](https://github.com/leanprover-community/mathlib4/pull/40298).

  Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit,
  this file (and its import in `SKW.Prereqs.AlgebraMisc`) should be deleted, and any usages
  redirected to the Mathlib versions.
  -/
  ```
- **In the original file**, delete the moved declarations (and any `variable` block that
  only existed for them) and add `public import SKW.PRed2Mathlib.<MirrorName>` — `public`
  so the declarations are still re-exported transitively to anything that imported the
  original file, keeping the rest of SKW compiling unchanged.
- **Register the new file** in the project's root import list (`SKW.lean` here — check
  for a `mk_all`-style script first; this project doesn't have one, so the entry is added
  by hand, near the original file's entry).
- **Build both files** (`lake build SKW.PRed2Mathlib.<MirrorName> SKW.<OriginalModule>`)
  and confirm clean. A spurious cascade of "expected token" / "declaration uses sorry"
  errors that don't point at any real typo usually means a **missing transitive import for
  notation** (e.g. `≃ₐ` is declared in `Mathlib.Algebra.Algebra.Equiv`, not in
  `Mathlib.Algebra.Algebra.Hom.Rat`): the mirror file only imports the module the PR
  targets, but the *currently-pinned, pre-merge* version of that module may not yet import
  the file declaring the notation — that import is often exactly what the PR itself adds!
  The original SKW file usually builds only because some unrelated import happens to pull
  the notation in transitively. Fix by adding the missing `public import` (e.g.
  `Mathlib.Algebra.Algebra.Equiv`) directly to the mirror file; it's harmless once the PR
  merges and the file gets deleted anyway.

This way the eventual cleanup (once the PR merges and the pin bumps — see below) is a
two-line deletion: drop the `PRed2Mathlib` file and the one `public import` line, with
zero risk of missing a stray duplicated declaration elsewhere in the original file.

## 6. Plan the post-merge cleanup

Once the PR merges, the `PRed2Mathlib` mirror file becomes fully redundant. Don't delete
it immediately — SKW pins a specific Mathlib commit via `lake-manifest.json`, so the
cleanup has to wait until that pin is bumped past the merge commit. Note it as a TODO for
the user: delete `SKW/PRed2Mathlib/<MirrorName>.lean`, remove its entry from `SKW.lean`,
and remove the `public import SKW.PRed2Mathlib.<MirrorName>` line from the original file.

## Cautions

- Pushing to the fork and opening the PR are part of §4 and need no separate confirmation:
  the user's choice of candidate in §1 authorizes them. Anything beyond that sequence (closing
  or editing someone else's PR, pushing to a branch that isn't yours, posting review comments)
  still gets confirmed first.
- Keep PRs focused: one logical unit of generalization per PR, per Mathlib reviewer
  preference (mentioned in `lean:mathlib-pr`'s `easy`/`WIP` label guidance).
