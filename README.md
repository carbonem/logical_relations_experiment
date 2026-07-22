# Logical relations for session types

A mechanization, in Rocq 9.1.1 + mathcomp 2.5, of a logical-relations
proof that well-typed processes of a session π-calculus never go wrong
— they never reach a state where two co-endpoints of a session offer
incompatible actions (output against output, input against input, a
close facing a delegation, a selection facing a delegation, …).

The headline theorem, in `error_freedom/cut/FN.v`:

```coq
Theorem error_free_typedP m (Γ : pctx m) (P : procP m) :
  typedP Γ P -> error_freeP P.
```

and in `error_freedom/split/FN.v`, over the standard
(context-splitting) session typing, where `balanced` says that a
context holding both ends of a session gives them dual protocols —
vacuous for a closed process:

```coq
Theorem error_free_typedP m (Γ : pctx m) (P : procP m) :
  typedP Γ P -> balanced Γ -> error_freeP P.
```

No `Admitted`, and every result is audited: 16 `Print Assumptions`
across the development, all reporting *Closed under the global
context*.

## Building

Each directory is a self-contained development with its own
`_CoqProject`:

```sh
cd error_freedom/cut          # or error_freedom/split
coqc -R . Tait Base.v      # …then the rest, in _CoqProject order
```

or generate a makefile:

```sh
coq_makefile -f _CoqProject -o Makefile && make
```

## Layout

`error_freedom/` holds two typing disciplines over the *same*
calculus, relation and proof infrastructure:

- **`cut/`** — parallel composition links exactly one session
  (propositions-as-sessions style). Typed processes form a tree, so
  deadlock is impossible by construction. Complete: 16 audits closed.
- **`split/`** — parallel composition splits the context
  (Honda–Vasconcelos–Kubo style). Two components may share any number
  of sessions, so cyclic dependencies — and deadlocks — are typable.
  Error freedom is exactly the property that survives the move.
  Complete: 13 files, 20 audits closed. Its `deadlock_error_free`
  proves a well-typed, genuinely stuck process error-free.

Both contain the same twelve files, in dependency order:

| file | contents |
|---|---|
| `Base.v`   | names, renamings, decidable finite search |
| `Types.v`  | actions, compatibility, session types, duality |
| `Proc.v`   | polarized process syntax, substitution |
| `LTS.v`    | seven visible-action families + τ; inversion suite |
| `Err.v`    | offers, the error predicate, error freedom |
| `Typing.v` | session typing |
| `LogRel.v` | the step-indexed logical relation; adequacy |
| `Equiv.v`  | backward equivariance of the LTS |
| `Compat.v` | offer determination; the ∅ rule |
| `Sem.v`    | slot order, substitution lemma for the relation |
| `Comb.v`   | the ν rule and the parallel cut |
| `FN.v`     | semantic typing, the fundamental theorem, error freedom |

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
