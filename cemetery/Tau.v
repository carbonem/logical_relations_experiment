(** * The label-based calculus: dynamics, errors, safety — no ≅

    Pivot point.  The syntax, renamings and the five visible-action
    transition families ([LTS.v]) are kept; structural congruence and
    the reduction relation of [synsem.v] are replaced by:

    - [ltst]  : internal steps (τ), formed at parallel composition from
                complementary visible actions, closed under parallel and
                restriction.  Communication of a *bound* endpoint
                ([ltsb]/[ltsr] pair) re-binds the extruded session
                around both continuations -- the close rule of the
                π-calculus, in double-binder form.
    - [offers]: the observable capability of a process at a channel
                (the five families collapsed to the four actions;
                a bound send offers [ADelS] like a free one).
    - [errL]  : a communication mismatch, structurally: some restriction
                whose body offers incompatible actions at its two
                endpoints.  No ≅ -- syntax is rigid, so the error
                predicate descends through the syntax.
    - [safeL] : no reachable mismatch.

    Design notes.
    - Because no rule mentions ≅, reducts preserve syntactic shape:
      reducts of [P ∥ Q] are [P₁ ∥ Q₁], reducts of [(ν)P] are [(ν)P₁]
      (with one new [(ν)] created by each bound-send communication, at
      the τ-formation site).  Every decomposition lemma of the old
      development becomes a syntax-directed inversion.
    - [errL] is *stronger* than the old [err] on racy processes: three
      active prefixes on one session count as a mismatch here, whereas
      the reduction-granular [err] required an exact binary redex.  A
      safety theorem against [errL] is a stronger statement.
    - Relation to the old semantics ([cemetery/]): τ additionally
      allows communication at free subjects, which [⇛] reserved for
      bound sessions; on closed processes the two agree (no free
      subjects exist).  The harmony theorem is deferred. *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import synsem Errors LogRel Toolkit LTS Transfer.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** Re-binding an extruded session around the receiver

    The receiver's open continuation ([n.+1], received channel at
    [zero]) moves under the new binder: the received channel becomes the
    sent endpoint [zero] of the pair, everything else shifts past the
    two binders. *)
Definition open_recv {n : nat} : ren n.+1 n.+2 :=
  scons zero (fun w => shift (shift w)).

(** ** Synchronisation at a session

    Communication happens only at a restriction: the two participants
    hold the two endpoints of the session the binder created, i.e. the
    channels [one] and [zero] of the body's scope.  [sync*] locates the
    two complementary prefixes across the body's parallel structure --
    descending under nested binders shifts the tracked endpoints, which
    is what lets a deeply nested pair communicate without any hoisting.
    (First design used free-subject communication at parallel; that is
    unsound for the logical relation, whose reduct quantification keeps
    the context fixed: internal steps must not consume obligations on
    free channels.  Communication under the binder never does.)

    Convention: in [sync? x y], [x] is the channel of the output-ish
    side (close / send), [y] of the input-ish side. *)

Inductive syncC : forall n, ch n -> ch n -> proc n -> proc n -> Prop :=
| SYC_L : forall n (x y : ch n) P P' Q Q',
    ltsc x P P' -> ltsw y Q Q' -> syncC x y (P ∥ Q) (P' ∥ Q')
| SYC_R : forall n (x y : ch n) P P' Q Q',
    ltsw y P P' -> ltsc x Q Q' -> syncC x y (P ∥ Q) (P' ∥ Q')
| SYC_ParL : forall n (x y : ch n) P R Q,
    syncC x y P R -> syncC x y (P ∥ Q) (R ∥ Q)
| SYC_ParR : forall n (x y : ch n) P Q R,
    syncC x y Q R -> syncC x y (P ∥ Q) (P ∥ R)
| SYC_Res : forall n (x y : ch n) (P R : proc n.+2),
    syncC (shift (shift x)) (shift (shift y)) P R ->
    syncC x y ((ν) P) ((ν) R).

Inductive syncD : forall n, ch n -> ch n -> proc n -> proc n -> Prop :=
| SYD_L : forall n (x y z : ch n) P P' Q (Q' : proc n.+1),
    ltsf x z P P' -> ltsr y Q Q' ->
    syncD x y (P ∥ Q) (P' ∥ subst_proc (scons z id_ren) Q')
| SYD_R : forall n (x y z : ch n) P (P' : proc n.+1) Q Q',
    ltsr y P P' -> ltsf x z Q Q' ->
    syncD x y (P ∥ Q) (subst_proc (scons z id_ren) P' ∥ Q')
| SYD_ParL : forall n (x y : ch n) P R Q,
    syncD x y P R -> syncD x y (P ∥ Q) (R ∥ Q)
| SYD_ParR : forall n (x y : ch n) P Q R,
    syncD x y Q R -> syncD x y (P ∥ Q) (P ∥ R)
| SYD_Res : forall n (x y : ch n) (P R : proc n.+2),
    syncD (shift (shift x)) (shift (shift y)) P R ->
    syncD x y ((ν) P) ((ν) R).

Inductive syncB : forall n, ch n -> ch n -> proc n -> proc n -> Prop :=
| SYB_L : forall n (x y : ch n) P (P' : proc n.+2) Q (Q' : proc n.+1),
    ltsb x P P' -> ltsr y Q Q' ->
    syncB x y (P ∥ Q) ((ν) (P' ∥ subst_proc open_recv Q'))
| SYB_R : forall n (x y : ch n) P (P' : proc n.+1) Q (Q' : proc n.+2),
    ltsr y P P' -> ltsb x Q Q' ->
    syncB x y (P ∥ Q) ((ν) (subst_proc open_recv P' ∥ Q'))
| SYB_ParL : forall n (x y : ch n) P R Q,
    syncB x y P R -> syncB x y (P ∥ Q) (R ∥ Q)
| SYB_ParR : forall n (x y : ch n) P Q R,
    syncB x y Q R -> syncB x y (P ∥ Q) (P ∥ R)
| SYB_Res : forall n (x y : ch n) (P R : proc n.+2),
    syncB (shift (shift x)) (shift (shift y)) P R ->
    syncB x y ((ν) P) ((ν) R).

(** ** Internal steps *)
Inductive ltst : forall n, proc n -> proc n -> Prop :=
| LT_ParL : forall n (P P' Q : proc n),
    ltst P P' -> ltst (P ∥ Q) (P' ∥ Q)
| LT_ParR : forall n (P Q Q' : proc n),
    ltst Q Q' -> ltst (P ∥ Q) (P ∥ Q')
| LT_Res : forall n (P P' : proc n.+2),
    ltst P P' -> ltst ((ν) P) ((ν) P')
| LT_CommC1 : forall n (P R : proc n.+2),
    syncC one zero P R -> ltst ((ν) P) ((ν) R)
| LT_CommC2 : forall n (P R : proc n.+2),
    syncC zero one P R -> ltst ((ν) P) ((ν) R)
| LT_CommD1 : forall n (P R : proc n.+2),
    syncD one zero P R -> ltst ((ν) P) ((ν) R)
| LT_CommD2 : forall n (P R : proc n.+2),
    syncD zero one P R -> ltst ((ν) P) ((ν) R)
| LT_CommB1 : forall n (P R : proc n.+2),
    syncB one zero P R -> ltst ((ν) P) ((ν) R)
| LT_CommB2 : forall n (P R : proc n.+2),
    syncB zero one P R -> ltst ((ν) P) ((ν) R).

(** Reflexive-transitive closure. *)
Reserved Notation "P '—τ*→' Q" (at level 50).
Inductive ltsts : forall n, proc n -> proc n -> Prop :=
| TS_refl : forall n (P : proc n), P —τ*→ P
| TS_step : forall n (P Q R : proc n),
    ltst P Q -> Q —τ*→ R -> P —τ*→ R
where "P '—τ*→' Q" := (ltsts P Q).

Lemma ltsts1 n (P Q : proc n) : ltst P Q -> P —τ*→ Q.
Proof. move=> H. exact: TS_step H (TS_refl _). Qed.

Lemma ltsts_trans n (P Q R : proc n) : P —τ*→ Q -> Q —τ*→ R -> P —τ*→ R.
Proof.
  move=> H; elim: H R => [//|n' P0 Q0 R0 Hst _ IH] R HQR.
  exact: TS_step Hst (IH _ HQR).
Qed.

(** ** Offers: observable capability at a channel *)
Definition offers {n : nat} (a : act) (x : ch n) (P : proc n) : Prop :=
  match a with
  | AClose => exists P', ltsc x P P'
  | AWait  => exists P', ltsw x P P'
  | ADelS  => (exists y P', ltsf x y P P') \/ (exists P', ltsb x P P')
  | ADelR  => exists P', ltsr x P P'
  end.

(** ** Communication errors, structurally *)
Inductive errL : forall n, proc n -> Prop :=
| EL_Mismatch : forall n (P : proc n.+2) a b,
    offers a one P -> offers b zero P -> compat a b = false ->
    errL ((ν) P)
| EL_Res : forall n (P : proc n.+2), errL P -> errL ((ν) P)
| EL_ParL : forall n (P Q : proc n), errL P -> errL (P ∥ Q)
| EL_ParR : forall n (P Q : proc n), errL Q -> errL (P ∥ Q).

(** ** Safety *)
Definition safeL {n : nat} (P : proc n) : Prop :=
  forall Q, P —τ*→ Q -> ~ errL Q.

Lemma safeL_nerr n (P : proc n) : safeL P -> ~ errL P.
Proof. move=> Hs. exact: Hs (TS_refl _). Qed.

Lemma safeL_step n (P Q : proc n) : safeL P -> ltst P Q -> safeL Q.
Proof. move=> Hs Hst R HQR. apply: Hs. exact: TS_step Hst HQR. Qed.

Lemma safeL_ltsts n (P Q : proc n) : safeL P -> P —τ*→ Q -> safeL Q.
Proof.
  move=> Hs H; elim: H Hs => [//|n' P0 Q0 R0 Hst _ IH] Hs.
  apply: IH. exact: safeL_step Hs Hst.
Qed.

(** ** Sanity: the calculus runs, and errs where it should *)

(** The matching pair communicates: a τ at the bound session. *)
Example run_close_wait :
  ltst ((ν) (CloseP one (EndP 2) ∥ WaitP zero (EndP 2)))
       ((ν) (EndP 2 ∥ EndP 2)).
Proof.
  apply: LT_CommC1. apply: SYC_L.
  - exact: LC_Pfx.
  - exact: LW_Pfx.
Qed.

(** Delegation of a bound endpoint: the extruded session re-binds
    around sender and receiver -- the close rule in action. *)
Example run_bound_delegation (K : proc 4) (B : proc 3) :
  ltst ((ν) ((ν) (DelP (shift (shift one)) zero K) ∥ InSP zero B))
       ((ν) ((ν) (K ∥ subst_proc open_recv B))).
Proof.
  apply: LT_CommB1. apply: SYB_L.
  - apply: LB_Open0. exact: LF_Pfx.
  - exact: LR_Pfx.
Qed.

(** Both endpoints close: mismatch. *)
Example errL_close_close :
  errL ((ν) (CloseP one (EndP 2) ∥ CloseP zero (EndP 2))).
Proof.
  apply: (EL_Mismatch (a := AClose) (b := AClose)) => //=.
  - eexists. apply: LC_ParL. exact: LC_Pfx.
  - eexists. apply: LC_ParR. exact: LC_Pfx.
Qed.

(** The wrong sort of message: close meets delegation-receive. *)
Example errL_close_delrecv :
  errL ((ν) (CloseP one (EndP 2) ∥ InSP zero (EndP 3))).
Proof.
  apply: (EL_Mismatch (a := AClose) (b := ADelR)) => //=.
  - eexists. apply: LC_ParL. exact: LC_Pfx.
  - eexists. apply: LR_ParR. exact: LR_Pfx.
Qed.

(** A racy third prefix on the same session is already an error here
    (stronger than the reduction-granular [err] of [cemetery/]). *)
Example errL_racy :
  errL ((ν) (CloseP one (EndP 2) ∥ (WaitP zero (EndP 2) ∥ CloseP zero (EndP 2)))).
Proof.
  apply: (EL_Mismatch (a := AClose) (b := AClose)) => //=.
  - eexists. apply: LC_ParL. exact: LC_Pfx.
  - eexists. apply: LC_ParR. apply: LC_ParR. exact: LC_Pfx.
Qed.

(** Bound-send source inversions (local helpers). *)
Ltac tau_inv H :=
  inversion H; subst;
  repeat match goal with
  | [ E : existT _ ?k _ = existT _ ?k _ |- _ ] =>
      apply (inj_pair2_eq_dec _ Nat.eq_dec) in E; subst
  end.

Lemma ltsb_close_noT n (y x : ch n) K R : ltsb y (CloseP x K) R -> False.
Proof. move=> H. by tau_inv H. Qed.

Lemma ltsb_wait_noT n (y x : ch n) K R : ltsb y (WaitP x K) R -> False.
Proof. move=> H. by tau_inv H. Qed.

Lemma ltsb_par_inv n (y : ch n) P1 P2 R :
  ltsb y (P1 ∥ P2) R ->
  (exists P1', ltsb y P1 P1') \/ (exists P2', ltsb y P2 P2').
Proof.
  move=> H. tau_inv H.
  - left. eexists. eassumption.
  - right. eexists. eassumption.
Qed.

Lemma errL_close_noT n (x : ch n) K : errL (CloseP x K) -> False.
Proof. move=> H. by tau_inv H. Qed.

Lemma errL_wait_noT n (x : ch n) K : errL (WaitP x K) -> False.
Proof. move=> H. by tau_inv H. Qed.

(** Structural inversion of [errL]. *)
Lemma errL_res_inv n (P : proc n.+2) :
  errL ((ν) P) ->
  (exists a b, [/\ offers a one P, offers b zero P & compat a b = false])
  \/ errL P.
Proof.
  move=> H. tau_inv H.
  - left. exists a, b. by split.
  - by right.
Qed.

Lemma errL_par_inv n (P Q : proc n) : errL (P ∥ Q) -> errL P \/ errL Q.
Proof. move=> H. tau_inv H; [by left | by right]. Qed.

(** And the good pair is not an error: the only offers at [one]/[zero]
    are close and wait, which are compatible.  Pure inversion -- no ≅
    to fight, which is the point of the pivot. *)
Example not_errL_close_wait :
  ~ errL ((ν) (CloseP one (EndP 2) ∥ WaitP zero (EndP 2))).
Proof.
  move=> /errL_res_inv [[a [b [Ha Hb Hc]]]|/errL_par_inv [H|H]]; first last.
  - by case: (errL_wait_noT H).
  - by case: (errL_close_noT H).
  - have Ea : a = AClose.
      move: Hc. case: a Ha => //= Ha _.
      + case: Ha => P' /ltsw_par_inv
          [[Z [_ /ltsw_close_noT //]]|[Z [_ HZ]]].
        by case: (ltsw_wait_inv HZ) => E _.
      + case: Ha => [[y [P' HF]]|[P' HB]].
        * case: (ltsf_par_inv HF) =>
            [[Z [_ /ltsf_close_noT //]]|[Z [_ /ltsf_wait_noT //]]].
        * case: (ltsb_par_inv HB) =>
            [[Z /ltsb_close_noT //]|[Z /ltsb_wait_noT //]].
      + case: Ha => P' /ltsr_par_inv
          [[Z [_ /ltsr_close_noT //]]|[Z [_ /ltsr_wait_noT //]]].
    have Eb : b = AWait.
      move: Hc. case: b Hb => //= Hb _.
      + case: Hb => P' /ltsc_par_inv
          [[Z [_ HZ]]|[Z [_ /ltsc_wait_noT //]]].
        by case: (ltsc_close_inv HZ) => E _.
      + case: Hb => [[y [P' HF]]|[P' HB]].
        * case: (ltsf_par_inv HF) =>
            [[Z [_ /ltsf_close_noT //]]|[Z [_ /ltsf_wait_noT //]]].
        * case: (ltsb_par_inv HB) =>
            [[Z /ltsb_close_noT //]|[Z /ltsb_wait_noT //]].
      + case: Hb => P' /ltsr_par_inv
          [[Z [_ /ltsr_close_noT //]]|[Z [_ /ltsr_wait_noT //]]].
    by rewrite Ea Eb in Hc.
Qed.

Print Assumptions run_bound_delegation.
Print Assumptions not_errL_close_wait.
