(** * Communication errors and safety for the session calculus of [synsem.v]

    The dynamics of [synsem.v] communicates only at a restriction: the two
    endpoints [one] and [zero] of a session meet as a binary parallel
    composition directly under their [ResP], possibly after rearrangement
    by structural congruence ([R_Close], [R_Com]).

    A *runtime error* is the evil twin of those two rules: the same
    decomposition, but the two co-endpoint prefixes are incompatible --
    both outputs, both inputs, or a close facing a delegation (the
    "wrong sort of message" errors).

    Design notes.
    - [compat] is a boolean, so evidence of a mismatch is positive and
      decidable: a pair of actions plus [erefl].  No negated proposition
      occurs inside the error predicate.
    - [err] mirrors [reduce] rule for rule ([E_Res] ~ [R_Res], [E_Par] ~
      [R_Par], [E_Struct] ~ [R_Struct], [E_Mismatch] ~ [R_Close]/[R_Com]).
      Consequently [err] can see a mismatch exactly where [⇛] could have
      seen a redex: if [≅] cannot bring two prefixes together as a binary
      redex under their [ν], they could never have communicated either --
      such a process is deadlocked, not erroneous.  Deadlock is
      deliberately not an error here.
    - [safe P] (informally: P ⇏ err) quantifies over all reducts: no
      reachable process is in error.  This is the one genuinely negative
      notion in the development; the logical relation built on top will
      have positive, conditional clauses and will meet [err] only as the
      final contradiction in the composition (cut) lemma. *)

From mathcomp Require Import all_ssreflect.
From Tait Require Import synsem.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** Head actions

    The four capabilities a prefix can offer on its subject channel.  The
    delegated channel is irrelevant to compatibility (channels are the
    only values in this calculus), so actions carry no payload. *)
Inductive act : Set := AClose | AWait | ADelS | ADelR.

(** Compatibility of the actions at the two endpoints of one session:
    close meets wait, delegation send meets delegation receive.
    Everything else -- output/output, input/input, close vs delegation --
    is a communication mismatch. *)
Definition compat (a b : act) : bool :=
  match a, b with
  | AClose, AWait | AWait, AClose | ADelS, ADelR | ADelR, ADelS => true
  | _, _ => false
  end.

Lemma compat_sym a b : compat a b = compat b a.
Proof. by case: a; case: b. Qed.

(** [prefix_at a x P]: [P] is a communication prefix with subject [x]
    offering action [a]. *)
Inductive prefix_at {n : nat} : act -> ch n -> proc n -> Prop :=
| PA_Close : forall x P, prefix_at AClose x (CloseP x P)
| PA_Wait  : forall x P, prefix_at AWait  x (WaitP x P)
| PA_DelS  : forall x y P, prefix_at ADelS x (DelP x y P)
| PA_DelR  : forall x (P : proc n.+1), prefix_at ADelR x (InSP x P).

(** ** The error predicate

    [E_Mismatch] is the redex shape of [R_Close]/[R_Com] with an
    incompatible pair of head actions; the remaining rules are exactly the
    closure rules of [reduce].  In particular [E_Struct] gives closure
    under [≅], which also accounts for orientation: a mismatch written
    with [zero] on the left is carried to this canonical shape by
    [SC_Par_Com] and [SC_Res_SwapC]. *)
(** The scope [n] is an index (not a parameter): [E_Res]'s premise lives
    two binders deeper, and the induction principle must provide an
    induction hypothesis there (cf. [has_type] in [Tait.v]). *)
Inductive err : forall n : nat, proc n -> Prop :=
| E_Mismatch : forall n a b (P Q : proc n.+2),
    prefix_at a one P -> prefix_at b zero Q -> compat a b = false ->
    err ((ν) (P ∥ Q))
| E_Res : forall n (P : proc n.+2), err P -> err ((ν) P)
| E_Par : forall n (P Q : proc n), err P -> err (P ∥ Q)
| E_Struct : forall n (P Q : proc n), P ≅ Q -> err Q -> err P.

(** [err] absorbs parallel components on the right too (derivable). *)
Lemma err_ParR n (P Q : proc n) : err Q -> err (P ∥ Q).
Proof. move=> H. apply: E_Struct (SC_Par_Com P Q) _. exact: E_Par. Qed.

(** ** Multistep reduction *)
Reserved Notation "P '⇛*' Q" (at level 50, left associativity).
Inductive mreduce {n : nat} : proc n -> proc n -> Prop :=
| MR_refl : forall P, P ⇛* P
| MR_step : forall P Q R, P ⇛ Q -> Q ⇛* R -> P ⇛* R
where "P '⇛*' Q" := (mreduce P Q).

Lemma mreduce1 n (P Q : proc n) : P ⇛ Q -> P ⇛* Q.
Proof. move=> H. apply: MR_step H (MR_refl _). Qed.

Lemma mreduce_trans n (P Q R : proc n) : P ⇛* Q -> Q ⇛* R -> P ⇛* R.
Proof.
  move=> H; elim: H => [P0|P0 Q0 R0 Hs _ IH] HQR //. apply: MR_step Hs (IH HQR).
Qed.

(** Congruence of multistep with the reduction contexts. *)
Lemma mreduce_Res n (P Q : proc n.+2) : P ⇛* Q -> (ν) P ⇛* (ν) Q.
Proof.
  elim=> [P0|P0 Q0 R0 Hs _ IH]; first exact: MR_refl.
  apply: MR_step (R_Res Hs) IH.
Qed.

Lemma mreduce_ParL n (P Q R : proc n) : P ⇛* Q -> P ∥ R ⇛* Q ∥ R.
Proof.
  elim=> [P0|P0 Q0 R0 Hs _ IH]; first exact: MR_refl.
  apply: MR_step (R_Par R Hs) IH.
Qed.

(** A structurally congruent process has the same reducts, up to
    absorbing the congruence into the first step. *)
Lemma struct_mreduce n (P Q R : proc n) : P ≅ Q -> Q ⇛* R -> P ≅ R \/ P ⇛* R.
Proof.
  move=> Heq H; case: H Heq => [Q0|Q0 Q1 R0 Hs Hm] Heq; first by left.
  right. apply: MR_step Hm. apply: R_Struct Heq Hs (SC_Refl _).
Qed.

(** ** Safety: no reachable communication error.

    This is the target of the whole development: the logical relation
    will be sound for [safe], and well-typed processes will inhabit it. *)
Definition safe {n : nat} (P : proc n) : Prop := forall Q, P ⇛* Q -> ~ err Q.

Lemma safe_nerr n (P : proc n) : safe P -> ~ err P.
Proof. move=> Hs. exact: Hs (MR_refl _). Qed.

(** Safety is forward closed under reduction... *)
Lemma safe_step n (P Q : proc n) : safe P -> P ⇛ Q -> safe Q.
Proof. move=> Hs Hst R HQR. apply: Hs. exact: MR_step Hst HQR. Qed.

Lemma safe_mreduce n (P Q : proc n) : safe P -> P ⇛* Q -> safe Q.
Proof.
  move=> Hs H; elim: H Hs => [P0|P0 Q0 R0 Hst _ IH] Hs //.
  apply: IH. exact: safe_step Hs Hst.
Qed.

(** ...and invariant under structural congruence (both [reduce] and [err]
    are [≅]-closed, so [safe] is too). *)
Lemma safe_struct n (P Q : proc n) : safe P -> P ≅ Q -> safe Q.
Proof.
  move=> Hs Heq R HQR Herr.
  case: (struct_mreduce Heq HQR) => [HPR|HPR].
  - exact: safe_nerr Hs (E_Struct HPR Herr).
  - exact: Hs HPR Herr.
Qed.

(** ** Sanity checks

    The mismatches we set out to rule out are errors; the matching pair
    communicates.  (Proving that the matching pair is *not* an error
    needs inversion of [err] up to [≅] -- that is the machinery of the
    next step, not of this file.) *)

(** Both endpoints close: output meets output. *)
Example err_close_close :
  err ((ν) (CloseP one (EndP 2) ∥ CloseP zero (EndP 2))).
Proof.
  apply: (E_Mismatch (a := AClose) (b := AClose)) => //; exact: PA_Close.
Qed.

(** Both endpoints wait: input meets input. *)
Example err_wait_wait :
  err ((ν) (WaitP one (EndP 2) ∥ WaitP zero (EndP 2))).
Proof.
  apply: (E_Mismatch (a := AWait) (b := AWait)) => //; exact: PA_Wait.
Qed.

(** The "wrong type of message" error: one endpoint closes the session,
    the other expects to receive a channel. *)
Example err_close_delrecv :
  err ((ν) (CloseP one (EndP 2) ∥ InSP zero (EndP 3))).
Proof.
  apply: (E_Mismatch (a := AClose) (b := ADelR)) => //;
    [exact: PA_Close | exact: PA_DelR].
Qed.

(** An error in evaluation position (under a bystander) is still an
    error. *)
Example err_under_par :
  err ((ν) (CloseP one (EndP 2) ∥ CloseP zero (EndP 2)) ∥ EndP 0).
Proof. apply: E_Par. exact: err_close_close. Qed.

(** The compatible pair is a redex, not an error: it communicates. *)
Example red_close_wait :
  (ν) (CloseP one (EndP 2) ∥ WaitP zero (EndP 2)) ⇛ (ν) (EndP 2 ∥ EndP 2).
Proof. exact: R_Close. Qed.

(** ** Axiom audit (house style, cf. [Tait.v]) *)
Print Assumptions err_close_delrecv.
Print Assumptions safe_struct.
