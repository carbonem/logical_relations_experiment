(** * τ-inversions and the first compatibility lemmas

    Everything here is syntax-directed inversion on the rigid calculus:
    no ≅, no renaming.

    - prefixes and [∅] are τ-inert, and their visible transitions are
      exactly their own head: the four prefix compatibility lemmas and
      [SEMT_end] follow in a page each;
    - τ-steps of a parallel are componentwise; τ-steps of a restriction
      are body-steps or synchronisations at the binder ([hyb1]);
    - a close/wait synchronisation sequentialises into its two visible
      transitions ([syncC_seq]) -- the shape the semantic communication
      lemma consumes. *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import synsem Errors LogRel Toolkit LTS Transfer Typing
  Fundamental Tau LogRelTau.

Set Implicit Arguments.
Unset Strict Implicit.

Ltac ti_inv H :=
  inversion H; subst;
  repeat match goal with
  | [ E : existT _ ?k _ = existT _ ?k _ |- _ ] =>
      apply (inj_pair2_eq_dec _ Nat.eq_dec) in E; subst
  end.

(** ** Remaining no-transition lemmas for the bound-send family *)
Lemma ltsb_del_noT n (y x z : ch n) K R : ltsb y (DelP x z K) R -> False.
Proof. move=> H. by ti_inv H. Qed.

Lemma ltsb_ins_noT n (y x : ch n) (K : proc n.+1) R :
  ltsb y (InSP x K) R -> False.
Proof. move=> H. by ti_inv H. Qed.

(** ** τ-inertness of dead and prefixed processes *)
Lemma ltst_end_noT n R : ltst (EndP n) R -> False.
Proof. move=> H. by ti_inv H. Qed.

Lemma ltst_close_noT n (x : ch n) K R : ltst (CloseP x K) R -> False.
Proof. move=> H. by ti_inv H. Qed.

Lemma ltst_wait_noT n (x : ch n) K R : ltst (WaitP x K) R -> False.
Proof. move=> H. by ti_inv H. Qed.

Lemma ltst_del_noT n (x y : ch n) K R : ltst (DelP x y K) R -> False.
Proof. move=> H. by ti_inv H. Qed.

Lemma ltst_ins_noT n (x : ch n) (K : proc n.+1) R :
  ltst (InSP x K) R -> False.
Proof. move=> H. by ti_inv H. Qed.

Lemma ltsts_stuck n (P : proc n) :
  (forall R, ltst P R -> False) ->
  forall P', P —τ*→ P' -> P' = P.
Proof.
  move=> Hno P' H. case: H Hno => // n0 P0 Q0 R0 Hst _ Hno.
  by case: (Hno _ Hst).
Qed.

(** ** τ-steps of compounds *)
Inductive hyb1 : forall n, proc n.+2 -> proc n.+2 -> Prop :=
| HY_tau : forall n (P R : proc n.+2), ltst P R -> hyb1 P R
| HY_C1 : forall n (P R : proc n.+2), syncC one zero P R -> hyb1 P R
| HY_C2 : forall n (P R : proc n.+2), syncC zero one P R -> hyb1 P R
| HY_D1 : forall n (P R : proc n.+2), syncD one zero P R -> hyb1 P R
| HY_D2 : forall n (P R : proc n.+2), syncD zero one P R -> hyb1 P R
| HY_B1 : forall n (P R : proc n.+2), syncB one zero P R -> hyb1 P R
| HY_B2 : forall n (P R : proc n.+2), syncB zero one P R -> hyb1 P R.

Lemma ltst_par_inv n (P Q : proc n) R :
  ltst (P ∥ Q) R ->
  (exists P', R = P' ∥ Q /\ ltst P P') \/
  (exists Q', R = P ∥ Q' /\ ltst Q Q').
Proof.
  move=> H. ti_inv H.
  - left. eexists. split; [reflexivity | assumption].
  - right. eexists. split; [reflexivity | assumption].
Qed.

Lemma ltst_res_inv n (P : proc n.+2) R :
  ltst ((ν) P) R ->
  exists P', R = (ν) P' /\ hyb1 P P'.
Proof.
  move=> H. ti_inv H.
  - eexists. split; [reflexivity | exact: HY_tau].
  - eexists. split; [reflexivity | exact: HY_C1].
  - eexists. split; [reflexivity | exact: HY_C2].
  - eexists. split; [reflexivity | exact: HY_D1].
  - eexists. split; [reflexivity | exact: HY_D2].
  - eexists. split; [reflexivity | exact: HY_B1].
  - eexists. split; [reflexivity | exact: HY_B2].
Qed.

Lemma ltsts_par_inv n (X R : proc n) : X —τ*→ R ->
  forall P Q, X = P ∥ Q ->
  exists P1 Q1, [/\ P —τ*→ P1, Q —τ*→ Q1 & R = P1 ∥ Q1].
Proof.
  elim=> {X R} [n0 X|n0 X Y R Hst _ IH] P Q E; subst.
  - exists P, Q. by split; try exact: TS_refl.
  - case: (ltst_par_inv Hst) => [[P' [EY HP]]|[Q' [EY HQ]]].
    + case: (IH _ _ EY) => P1 [Q1 [Hp Hq HR]].
      exists P1, Q1. split=> //. exact: TS_step HP Hp.
    + case: (IH _ _ EY) => P1 [Q1 [Hp Hq HR]].
      exists P1, Q1. split=> //. exact: TS_step HQ Hq.
Qed.

(** Hybrid chains: how the body of a restriction evolves. *)
Inductive hybT : forall n, proc n.+2 -> proc n.+2 -> Prop :=
| HT_refl : forall n (P : proc n.+2), hybT P P
| HT_step : forall n (P Q R : proc n.+2),
    hyb1 P Q -> hybT Q R -> hybT P R.

Lemma ltsts_res_inv n (X R : proc n) : X —τ*→ R ->
  forall P : proc n.+2, X = (ν) P ->
  exists P1, hybT P P1 /\ R = (ν) P1.
Proof.
  elim=> {X R} [n0 X|n0 X Y R Hst _ IH] P E; subst.
  - exists P. by split; first exact: HT_refl.
  - case: (ltst_res_inv Hst) => P' [EY HP].
    case: (IH _ EY) => P1 [Hh HR].
    exists P1. split=> //. exact: HT_step HP Hh.
Qed.

(** ** Sequentialisation of close/wait synchronisation

    The two prefixes sit at disjoint parallel positions, so the joint
    step is the composition of the two visible transitions. *)
Lemma syncC_seq n (x y : ch n) (P R : proc n) (H : syncC x y P R) :
  exists Pc, ltsc x P Pc /\ ltsw y Pc R.
Proof.
  elim: H => {n x y P R}.
  - move=> n x y P P' Q Q' HC HW.
    exists (P' ∥ Q). split; [exact: LC_ParL HC | exact: LW_ParR HW].
  - move=> n x y P P' Q Q' HW HC.
    exists (P ∥ Q'). split; [exact: LC_ParR HC | exact: LW_ParL HW].
  - move=> n x y P R Q _ [Pc [H1 H2]].
    exists (Pc ∥ Q). split; [exact: LC_ParL H1 | exact: LW_ParL H2].
  - move=> n x y P Q R _ [Pc [H1 H2]].
    exists (P ∥ Pc). split; [exact: LC_ParR H1 | exact: LW_ParR H2].
  - move=> n x y P R _ [Pc [H1 H2]].
    exists ((ν) Pc). split; [exact: LC_Res H1 | exact: LW_Res H2].
Qed.

(** ** Compatibility: the four prefixes and the terminated process *)

Lemma compat_closeT n (Δ : sctx n) (x : ch n) K :
  Δ x = Some SClose -> cupd x None Δ ⊨τ K -> Δ ⊨τ CloseP x K.
Proof.
  move=> HxS HK k. case: k => [//|k]. split.
  - move=> a y Hof.
    case: a Hof => /= [[P'' HT]|[P'' HT]|[[z [P'' HT]]|[P'' HT]]|[P'' HT]].
    + case: (ltsc_close_inv HT) => -> _. exists SClose. by rewrite HxS.
    + by case: (ltsw_close_noT HT).
    + by case: (ltsf_close_noT HT).
    + by case: (ltsb_close_noT HT).
    + by case: (ltsr_close_noT HT).
  - move=> y S' HyS'.
    case: S' HyS' => [| |T S2|T S2] HyS' /=.
    + move=> P'' HT. case: (ltsc_close_inv HT) => Ey ->. subst y.
      exact (HK k).
    + move=> P'' HT. by case: (ltsw_close_noT HT).
    + split.
      * move=> z P'' HT. by case: (ltsf_close_noT HT).
      * move=> P'' HT. by case: (ltsb_close_noT HT).
    + move=> P'' HT. by case: (ltsr_close_noT HT).
  - by move=> P1 P2 E.
  - by move=> Q E.
  - move=> P' Hst. by case: (ltst_close_noT Hst).
Qed.

Lemma compat_waitT n (Δ : sctx n) (x : ch n) K :
  Δ x = Some SWait -> cupd x None Δ ⊨τ K -> Δ ⊨τ WaitP x K.
Proof.
  move=> HxS HK k. case: k => [//|k]. split.
  - move=> a y Hof.
    case: a Hof => /= [[P'' HT]|[P'' HT]|[[z [P'' HT]]|[P'' HT]]|[P'' HT]].
    + by case: (ltsc_wait_noT HT).
    + case: (ltsw_wait_inv HT) => -> _. exists SWait. by rewrite HxS.
    + by case: (ltsf_wait_noT HT).
    + by case: (ltsb_wait_noT HT).
    + by case: (ltsr_wait_noT HT).
  - move=> y S' HyS'.
    case: S' HyS' => [| |T S2|T S2] HyS' /=.
    + move=> P'' HT. by case: (ltsc_wait_noT HT).
    + move=> P'' HT. case: (ltsw_wait_inv HT) => Ey ->. subst y.
      exact (HK k).
    + split.
      * move=> z P'' HT. by case: (ltsf_wait_noT HT).
      * move=> P'' HT. by case: (ltsb_wait_noT HT).
    + move=> P'' HT. by case: (ltsr_wait_noT HT).
  - by move=> P1 P2 E.
  - by move=> Q E.
  - move=> P' Hst. by case: (ltst_wait_noT Hst).
Qed.

Lemma compat_delT n (Δ : sctx n) (x y : ch n) K T S2 :
  Δ x = Some (SSend T S2) -> Δ y = Some T ->
  cupd y None (cupd x (Some S2) Δ) ⊨τ K ->
  Δ ⊨τ DelP x y K.
Proof.
  move=> HxS HyS HK k. case: k => [//|k]. split.
  - move=> a w Hof.
    case: a Hof => /= [[P'' HT]|[P'' HT]|[[z [P'' HT]]|[P'' HT]]|[P'' HT]].
    + by case: (ltsc_del_noT HT).
    + by case: (ltsw_del_noT HT).
    + case: (ltsf_del_inv HT) => -> _ _. exists (SSend T S2). by rewrite HxS.
    + by case: (ltsb_del_noT HT).
    + by case: (ltsr_del_noT HT).
  - move=> w S' HwS'.
    case: S' HwS' => [| |T' S2'|T' S2'] HwS' /=.
    + move=> P'' HT. by case: (ltsc_del_noT HT).
    + move=> P'' HT. by case: (ltsw_del_noT HT).
    + split.
      * move=> z P'' HT. case: (ltsf_del_inv HT) => Ew Ez ->. subst w z.
        have [ET ES] : T' = T /\ S2' = S2.
          by move: HwS'; rewrite HxS => -[-> ->].
        subst T' S2'. split; [exact: HyS | exact (HK k)].
      * move=> P'' HT. by case: (ltsb_del_noT HT).
    + move=> P'' HT. by case: (ltsr_del_noT HT).
  - by move=> P1 P2 E.
  - by move=> Q E.
  - move=> P' Hst. by case: (ltst_del_noT Hst).
Qed.

Lemma compat_insT n (Δ : sctx n) (x : ch n) (K : proc n.+1) T S2 :
  Δ x = Some (SRecv T S2) ->
  scons (Some T) (cupd x (Some S2) Δ) ⊨τ K ->
  Δ ⊨τ InSP x K.
Proof.
  move=> HxS HK k. case: k => [//|k]. split.
  - move=> a w Hof.
    case: a Hof => /= [[P'' HT]|[P'' HT]|[[z [P'' HT]]|[P'' HT]]|[P'' HT]].
    + by case: (ltsc_ins_noT HT).
    + by case: (ltsw_ins_noT HT).
    + by case: (ltsf_ins_noT HT).
    + by case: (ltsb_ins_noT HT).
    + case: (ltsr_ins_inv HT) => -> _. exists (SRecv T S2). by rewrite HxS.
  - move=> w S' HwS'.
    case: S' HwS' => [| |T' S2'|T' S2'] HwS' /=.
    + move=> P'' HT. by case: (ltsc_ins_noT HT).
    + move=> P'' HT. by case: (ltsw_ins_noT HT).
    + split.
      * move=> z P'' HT. by case: (ltsf_ins_noT HT).
      * move=> P'' HT. by case: (ltsb_ins_noT HT).
    + move=> P'' HT. case: (ltsr_ins_inv HT) => Ew ->. subst w.
      have [ET ES] : T' = T /\ S2' = S2.
        by move: HwS'; rewrite HxS => -[-> ->].
      subst T' S2'. exact (HK k).
  - by move=> P1 P2 E.
  - by move=> Q E.
  - move=> P' Hst. by case: (ltst_ins_noT Hst).
Qed.

(** [∅] inhabits the relation at every context. *)
Lemma SEMT_end n (Δ : sctx n) : Δ ⊨τ EndP n.
Proof.
  move=> k. case: k => [//|k]. split.
  - move=> a y Hof.
    case: a Hof => /= [[P'' HT]|[P'' HT]|[[z [P'' HT]]|[P'' HT]]|[P'' HT]].
    + by case: (ltsc_end_inv HT).
    + by case: (ltsw_end_inv HT).
    + by case: (ltsf_end_inv HT).
    + by case: (ltsb_end_inv HT).
    + by case: (ltsr_end_inv HT).
  - move=> y S' HyS'.
    case: S' HyS' => [| |T S2|T S2] HyS' /=.
    + move=> P'' HT. by case: (ltsc_end_inv HT).
    + move=> P'' HT. by case: (ltsw_end_inv HT).
    + split.
      * move=> z P'' HT. by case: (ltsf_end_inv HT).
      * move=> P'' HT. by case: (ltsb_end_inv HT).
    + move=> P'' HT. by case: (ltsr_end_inv HT).
  - by move=> P1 P2 E.
  - by move=> Q E.
  - move=> P' Hst. by case: (ltst_end_noT Hst).
Qed.

Print Assumptions compat_closeT.
Print Assumptions SEMT_end.
