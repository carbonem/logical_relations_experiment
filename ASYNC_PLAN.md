# Plan: mechanized operational preciseness of asynchronous session subtyping

Target theorem (LMCS'17 Def 1.1, async instance, semantic route):

```
⩽a  ⊆  ≤sem  ⊆  ≤ctx  ⊆  ⩽a
```

where `≤sem := ∀k, ⟦T⟧k ⊆ ⟦S⟧k` (LR-interpretation inclusion — the new middle
term), `≤ctx` = CDSY's largest-safe-substitution yardstick over the buffered
calculus, `⩽a` = the LMCS'17 asynchronous subtyping. Reference: Chen,
Dezani-Ciancaglini, Scalas, Yoshida, *On the Preciseness of Subtyping in
Session Types*, LMCS 2017 (`/Users/carbonem/probabilistic_subtyping/references/chen_et_al.pdf`).
Home: new `error_freedom/async/`, seeded by copying `split/`. `split/` and
`cut/` stay frozen.

**FOCUS PRINCIPLE (user, 2026-07-24): the contribution is the logical-
relations side.** Ekici–Yoshida, *Formalising Asynchronous Session Subtyping*
(ACM TOCL 27(3), June 2026, DOI 10.1145/3815176, ~32K lines Coq,
`/Users/carbonem/Downloads/3815176.pdf`, github.com/ekiciburak/async-mpst-st)
mechanizes the TYPE-LEVEL half for async MPST: session trees, SISO
decomposition, refinement, its 8-rule inductive negation, correctness
(no same-participant reordering), transitivity, and Cor 5.2
`¬(T ⩽ T′) ⟺ T ⩽̸ T′` — i.e. LMCS'17's Step 2 (negation bridge), machine-
checked. NO processes, NO operational semantics, NO error predicate (their
stated future work: type system + fairness/liveness). Consequences:
- Syntactic-subtyping mechanics are OFF our critical path: mirror their
  8-rule negation design (or port the binary instance; their
  autosubst2/paco/coseq stack vs our mathcomp well-scoped stack makes
  as-is import unlikely — decide at the A6 gate).
- Our identity: everything operational/semantic — ≤sem, anticipation as
  buffer-extension monotonicity, fundamental theorem over buffers,
  adequacy, error-parametrized family (orphans need processes — unstatable
  in their setting), duality-as-orthogonality, and the bridge theorem
  `⩽a ⊆ ≤sem` giving their mechanized relation an operational meaning for
  the first time (collaboration-shaped, not race-shaped).
- Operational preciseness (Step 3, discriminating contexts) remains
  unclaimed; both halves of its scaffolding now exist.

## Translation table: LMCS'17 → polarized calculus

| LMCS'17 | async/ |
|---|---|
| co-channels `a`,`b`, bound pairwise `(νab)` | one name, two polarities; single `ν`; co-endpoint = `pflip` |
| directed queue `ab ▶ h` (a writes, b reads); two per pair | `PQueue c h : procP n`, keyed by READER endpoint `c`; writer = `pflip c`; two inboxes per name |
| entries `l⟨a⟩`; `h` list modulo unit/assoc | `entry n := QClose \| QLbl bool \| QChan (pch n)`; `h : seq (entry n)` — lists on the nose, no quotient |
| `[R-SEND-ASYNC]` append at tail | output prefixes at `c` enqueue at tail of `PQueue (pflip c)`; non-blocking |
| `[R-RECEIVE-ASYNC]` read from head | input prefixes at `c` dequeue head of `PQueue c` |
| `[S-NULL]` GC of empty queue pair | cong axiom: `(ν)(two empty inboxes) ≡ ∅`-style rule in the Harmony rebuild |
| errors (Table 13): mismatch, input-lock (IN-IN, IN), orphan (via `φ(P)`) | `errP` extended: head-of-queue is an `offersP` at the reader (mismatch reuses offers machinery); input-lock + orphan as new clauses; **error predicate parametrized from day one** (record of enabled clauses) |
| queue types `τ`, remainder `T − τ`, balanced Δ, `Δ ⇒ Δ'` | Typing.v/Bridge.v additions; `T − τ` partial function; `[T-NEW-ASYNC]` duality of remainders |
| characteristic processes (Def 5.1), negation `⩽̸a` (Table 16), discriminator (Thm 5.7) | Phase A7/B4; note the load-bearing "`T′ = T` or `S′ = S̄`" strict-subtype invariant for orphan cases (Ex 5.8/5.9) |

Design decisions taken (revisit at phase gates):
- **Queues as runtime process constructors** (impact analysis rec): entries are
  binder-free, `psubst` = `pren` on key + `map` over entries; head-of-queue is
  literally an offer; cong/harmony extend by constructor cases.
- **Buffer type-state in `Δ` as residual protocol, contents in syntax** — the
  `sslot` records the protocol *after* buffered outputs; keeps the world a
  finite function, no step-index/size coupling.
- **Finite-first.** Phase A does the whole preciseness architecture on finite
  types (inductive `⩽a`, finite `A`-contexts, structural `φ`). Phase B adds
  μ-types + process recursion + coinduction. Rationale: every landmine the
  paper digest ranks hardest (coinductive `[SUB-PERM-ASYNC]` with finite-data
  contexts, negation bridge Lemma 5.3, `φ` termination, up-to-unfolding
  lemmas) is recursion-induced; the LR content (buffers, anticipation,
  fundamental theorem) is fully exercised finitely.
- **Skip transitivity of `⩽a`** (Thm 4.8 / Lemma B.3, the paper's heaviest
  port): the triangle never uses it; `≤sem` is transitive by construction.
  Document as intentional.
- `≤ctx` and adequacy stated on the LTS; reduction-semantics presentation via
  a Harmony rebuild deferred to Phase D (off the critical path — confirmed:
  FN.v never imports Harmony.v).

## Phases

**Phase 0 — scaffold (days).** Copy split/ → async/; `_CoqProject`, Makefile;
ASYNC design notes in header comments; freeze the LMCS'17 citation keys
(Def/Thm numbers from the digest) into file headers as the traceability spine.

**Phase A — finite async core.** The LR-learning phase; each item = one or
more Opus-agent campaigns with my specs, per-milestone `Print Assumptions`
audit; every milestone leaves the tree building.
- A1 Proc: `PQueue` + `entry`, `psubst` seq case, renaming laws. (small)
- A2 LTS: outputs→enqueue, inputs→dequeue, τ = process/queue synchronization
  at ∥; regenerate pinv grid; equivariance (Equiv.v deltas). (large)
- A3 Err: offers over queue heads; parametrized `errP` — clauses: mismatch,
  input-lock (their ERR-IN-IN/IN shapes), orphan (finite `φ`: structural
  δ-function, no memoization needed without recursion). (medium)
  NOTE (user, 2026-07-24): safety/error-freedom expected to simplify via a
  compatibility-based formulation from another paper — spec of A3 to be
  revisited with that reference before going operational.
- A4 Typing/Bridge: queue typing `[T-EMPTY-Q]/[T-MESSAGE-Q]`, remainder
  `T − τ`, balanced, `Δ ⇒ Δ'`. (medium)
- A5 LR: `sslot` residual-protocol redesign; `VsemP` outputs always fire
  (enqueue + advance), inputs fire on head; `sevolve` generalizes to buffer
  growth; **buffer-extension monotonicity = the semantic content of output
  anticipation** — the single most important new lemma; fundamental theorem
  rebuild (Comb.v `dmerge`/`combineP` thread buffers; FN.v `spush`/`vok`
  push buffers along σ-merges). (very large — the project's core risk)
- A6 Subtyping, soundness + adequacy arcs: finite `⩽a` (inductive, with
  `A`-contexts as finite data and the `& ∈` side conditions); `≤sem`;
  per-rule inclusion lemmas incl. `[SUB-PERM-ASYNC]` via buffer-extension
  monotonicity; adequacy from the fundamental theorem. (medium)
- A7 Completeness arc: finite `⩽̸a`, characteristic processes (Def 5.1 with
  polarized queue pairs), discriminating configurations (Thm 5.7 case table
  from the digest), incl. the strict-subtype orphan discriminators.
  **Milestone: finite async preciseness, machine-checked.** Plantable flag;
  standalone artifact paper if the race demands. (large)

**Phase B — recursion.** Gate: reassess after A7.
- B1 μ-types (decide then: μ-syntax + unfolding vs coinductive regular trees
  à la Ekici–Yoshida/paco) + process recursion (`def X(x)=P`, single-parameter
  — exactly what `φ`'s well-foundedness needs, per the digest).
- B2 LR deltas: step-indexing now load-bearing; fundamental theorem cases for
  recursion.
- B3 Coinductive `⩽a`: `[SUB-PERM-ASYNC]` as guarded cofix over finite
  contexts; `& ∈ / ⊕ ∈` predicates + up-to-unfolding (Prop B.1/C.1/C.2).
  Follow Ekici–Yoshida TOCL'26 designs (paco, gfp-of-lfp, their 8-rule
  negation reformulation) rather than LMCS'17's 18-rule original.
- B4 Negation bridge (their Cor 5.2 is the mechanized prior art — mirror,
  binary instance), memoized `φ`, full completeness.
  **Milestone: LMCS'17 async preciseness, machine-checked.**

**Phase C — the delta beyond the paper (cheap after A, because errP is
parametrized).** Same LR, drop the orphan clause: derive machine-checked
(i) Mostrous-thesis relation sound for mismatch+input-lock-only,
(ii) unsound once orphans count, (iii) the two induced `≤ctx` differ —
the pp. 5/46 story as theorems; the lattice-of-precise-relations payoff.

**Phase D — polish.** Harmony rebuild for async (reduction-semantics
presentation), boundary artifacts (k-truncations, non-continuity witness —
needs Phase B), paper.

## Risk register (merged, ranked)

1. **FN.v fundamental theorem: σ-merges × in-flight buffers** — delegation
   into a queue whose co-end gets merged fuses at *dequeue* time; `vok` needs
   new collision rules for queued endpoints. Mitigation: A5 gets the most
   careful spec + earliest start; try a merge-free fundamental theorem first
   if it stalls (weaker but sufficient for adequacy over closed programs —
   check before conceding).
2. **`sslot`/step-index vs buffer growth** — async τ changes buffers; the
   k-independent cut clause of split/ is threatened. Mitigation: residual-
   protocol design keeps buffer contents out of the world; prototype the cut
   clause on paper before A5 coding.
3. **Phase B coinduction cluster** (SUB-PERM as cofix, negation bridge, φ).
   Mitigation: finite-first makes B optional-but-desired; Ekici–Yoshida's
   Coq encoding is prior art to imitate for the trees.
4. **Error-notion boundary** (orphan clause must not flag legitimately
   in-flight messages; errP must stay the pointwise negation of conformD).
   Mitigation: A3 spec derived verbatim from Table 13 + digest.
5. **Race** (Ekici–Yoshida one increment from process-level; McDermott–
   Yoshida denotational). Mitigation: A7 flag early; the linear/orphan-
   parametrized angle (Phase C) is ours regardless.

## Effort

split/ is ~10k lines; impact analysis estimates async at +40–50% ⇒ ~14k
lines, concentrated in LTS/LogRel/Comb/FN. With the established Opus-agent
pipeline (spec → agent → independent audit): Phase A is a multi-week campaign
of sessions, not a single day; A5 alone is comparable to the entire original
split/ effort. Phase B comparable to A. Calendar: months, not weeks — but
every milestone is a standing artifact.

## Execution conventions

- Opus agents implement; main thread specs, sequences, and independently
  re-audits (grep Admitted/Axiom + scratch `Print Assumptions` per milestone).
- Every file keeps the `(Def X.Y, p. Z)` LMCS'17 citations from the digest.
- 20-audit convention from split/ carries: each headline lemma gets a
  `Print Assumptions` in-file.
- Commits at phase milestones only; tree always builds.
