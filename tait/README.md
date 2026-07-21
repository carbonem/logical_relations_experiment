# Bob's note, mechanized

`Tait.v` is a mechanization of Robert Harper's *How to (Re)Invent
Tait's Method* (Spring 2026): the termination proof for a simply-typed
λ-calculus with answers, unit, products and functions, by hereditary
termination — the computability / logical-relations method.

This is the warm-up that started the project, kept because it is where
the shape of the argument (value interpretation by type, term
interpretation as "reduces to a good value", fundamental theorem by
induction on typing) was first written down. It is **not** part of the
session-types development: it depends on nothing there, and nothing
there depends on it.

Build:

```sh
coqc -R . Tait Tait.v
```

Main results: `fundamental`, `termination`, `preservation`.

One difference from the house style upstairs. This file uses
functional extensionality, so two of its four audits report

```
Axioms: functional_extensionality_dep
```

rather than *Closed under the global context*. The session-types
development is axiom-free; when it needed the same kind of reasoning
about substitutions it used pointwise-equality lemmas
(`psubst_ext` and friends) instead.
