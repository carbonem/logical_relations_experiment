# Cemetery: the two abandoned presentations

Everything here compiles, all `Qed`, axiom-free, against Rocq 9.1.1 +
mathcomp 2.5.  To rebuild standalone: copy this directory somewhere
empty and `coqc` the files in `_CoqProject` order.

Nothing here is on the live path.  The live development is the
polarity line in `../error_freedom/cut/` — twelve files,
`Base` … `FN` — which proves `error_free_typedP : typedP Γ P ->
error_freeP P` unconditionally.  Note that this directory keeps its OWN
copies of `synsem.v`, `Errors.v` and `LogRel.v`: those names no
longer exist upstairs, where the surviving fragments were merged
into `Base.v` (names, renamings, finite search) and `Types.v`
(actions, compatibility, session types, duality).  These
files are kept because they *measure* the two design decisions the
live line rests on: each stratum is a wall we hit, and the cost of
hitting it.

## Stratum 1: the structural-congruence presentation

Frozen at the pivot to a label-based (LTS-only) calculus.

- `Errors.v`      err/safe over reduction-up-to-≅
- `LogRel.v`      the logical relation with ≅-exposure clauses
- `Typing.v`      split-based session typing (≅-free; survived the pivot)
- `Adequacy.v`    UNCONDITIONAL `Δ ⊨ P -> safe P`
- `Fundamental.v` fundamental theorem + `safe_typed`, conditional on an
                  explicitly-listed inversion interface (13 items)
- `LTS.v`         the five visible-action transition families
- `Transfer.v`    ≅-transfer for four families + backward equivariance
                  (discharges one interface item; measures the ≅-tax)
- `Discharge.v`   four exposure-interface items proved from transfer
- `Bridge.v`      framed-communication normalized steps (part 1)

Score at freeze: 5/13 interface items discharged; an estimated
1500–1800 further lines (two of them high-risk) to unconditional
`safe_typed`.  The wall: every clause of the relation quantifies over
≅-classes, so each proof step pays a transfer lemma.

## Stratum 2: the double-binder LTS presentation

The ≅-free rebaseline.  A restriction bound BOTH endpoints
(`(ν) P : proc n -> proc n.+2`), so a session's two ends had no
syntactic connection, communication happened at the binder, and the
τ-rule descended under it.

- `Tau.v`         τ-transitions with communication at the binder
- `LogRelTau.v`   the logical relation over that calculus
- `TauInv.v`      inversion suite
- `TauEquiv.v`    equivariance stack (its `find_ch` survived: it is now
                  `Base.v` on the live line)
- `TauSem.v`      substitution/weakening for the relation

The wall, and it is the one worth narrating: under sync-descent the
cut clause has to read `exists S, ... cext S Δ ...`, and that `S`
depends on the observation depth `k`.  That non-uniformity blocks
consuming a synchronization inside nested restrictions — no local
ingenuity fixes it, because it is the *statement* that is wrong.
Polarized endpoints dissolve it: with a total syntactic co-endpoint
map, communication happens at `∥`, `ν` is inert, and the cut clause
becomes deterministic.

## `attic/Attic.v`

Lemmas of the LIVE line that are true, proved, and unreachable from
`error_free_typedP` — chiefly the forward equivariance stack (the
fundamental theorem is in substitution form, so it consumes renaming
*backwards*), the fully-injective τ-inversion (superseded by the
coverage-guarded one), and the closed-world compatibility lemmas
(superseded by their σ-parametric versions, which additionally handle
a merged subject).  Unlike the two strata above, this file is checked
against the CURRENT live line: copy it into `../error_freedom/cut/` and

    coqc -R . Tait Attic.v

It is deliberately absent from the live `_CoqProject`; nothing on the
live path may depend on it.

## Where Bob's note went

Harper's Tait-method note mechanized for STLC — the warm-up that
started the project — used to sit here.  It is not an abandoned
presentation of the session calculus at all, so it now has its own
directory, `../tait/`.  It depends on nothing in this development and
nothing here depends on it.
