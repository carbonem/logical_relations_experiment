# Logical relations for session types

A mechanization, in Rocq 9.1.1 + mathcomp 2.5, of a logical-relations
proof that well-typed processes of a session π-calculus never go wrong
— they never reach a state where two co-endpoints of a session offer
incompatible actions (output against output, input against input, a
close facing a delegation, a selection facing a delegation, …).

The headline theorem, in `error_freedom/PolFN.v`:

```coq
Theorem error_free_typedP m (Γ : pctx m) (P : procP m) :
  typedP Γ P -> error_freeP P.
```

No `Admitted`, and every result is audited: 16 `Print Assumptions`
across the development, all reporting *Closed under the global
context*.

## Building

Each directory is a self-contained development with its own
`_CoqProject`:

```sh
cd error_freedom
coqc -R . Tait PolBase.v      # …then the rest, in _CoqProject order
```

or generate a makefile:

```sh
coq_makefile -f _CoqProject -o Makefile && make
```

## Layout

The live development is `error_freedom/`, twelve `Pol*.v` files in
dependency order:

| file | contents |
|---|---|
| `PolBase.v`   | names, renamings, decidable finite search |
| `PolTypes.v`  | actions, compatibility, session types, duality |
| `PolProc.v`   | polarized process syntax, substitution |
| `PolLTS.v`    | seven visible-action families + τ; inversion suite |
| `PolErr.v`    | offers, the error predicate, error freedom |
| `PolTyping.v` | session typing |
| `PolLogRel.v` | the step-indexed logical relation; adequacy |
| `PolEquiv.v`  | backward equivariance of the LTS |
| `PolCompat.v` | offer determination; the ∅ rule |
| `PolSem.v`    | slot order, substitution lemma for the relation |
| `PolComb.v`   | the ν rule and the parallel cut |
| `PolFN.v`     | semantic typing, the fundamental theorem, error freedom |

Two things the calculus does deliberately:

- **Endpoints are polarized.** A name plus a polarity, so the
  co-endpoint of `(x, ρ)` is the total syntactic function
  `(x, flip ρ)`. Communication is therefore a rule of parallel
  composition and the restriction is inert.
- **The fundamental theorem is stated for open terms under name
  substitutions that may merge the two ends of a session.** This is
  what makes the delicate case of the receive rule — the received
  name's co-end is already owned, so the two fuse — fall out as the
  continuation's induction hypothesis rather than needing a
  contraction lemma.

`cemetery/` holds two earlier presentations of the same theorem that
were abandoned, each at the wall that killed it, together with an
`attic/` of lemmas from the live line that are true, proved, and
unreachable from `error_free_typedP`. Everything in there still compiles;
see `cemetery/README.md`.

`tait/` is Harper's *How to (Re)Invent Tait's Method* mechanized for
STLC — the warm-up that started the project, unrelated to the session
calculus.

`references/` holds the two papers the development follows.
