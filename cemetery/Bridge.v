(** * The reduction bridge, part 1: normalized steps

    [⇛] hides communications behind [R_Struct].  The bridge normalizes:
    every step is, up to [≅], a stack of parallel/restriction
    congruences over a *framed communication* at a binder ([commF] --
    the two prefixes in parallel with an arbitrary frame, the [≅]
    absorbed into the premise).  The frame is what makes the shape
    transferable along [≅] (a strict binary redex is not: [Res_Scope]
    pushes a bystander into the binder).

    [nstep] over-approximates [⇛]: a framed communication with a
    non-extrudable frame has no real redex.  Sound for safety -- the
    consumers only ever prove closure of the logical relation under
    *more* steps than exist.

    This file: definitions, the act-count guard, framing, forward
    equivariance, and syntax-directed inversion.  Part 2 (next):
    image-closure of [≅], backward equivariance, the [nstep] transfer,
    and [red_nstep : X ⇛ R -> exists R', nstep X R' /\ R' ≅ R]. *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import synsem Errors LogRel Toolkit LTS Transfer.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** Framed communication at a binder *)
Inductive commF : forall n, proc n.+2 -> proc n.+2 -> Prop :=
| CF_CW : forall n (P A B F : proc n.+2),
    P ≅ CloseP one A ∥ (WaitP zero B ∥ F) ->
    commF P (A ∥ (B ∥ F))
| CF_WC : forall n (P A B F : proc n.+2),
    P ≅ WaitP one A ∥ (CloseP zero B ∥ F) ->
    commF P (A ∥ (B ∥ F))
| CF_DR : forall n (P : proc n.+2) (x : ch n.+2) A (B : proc n.+3) F,
    P ≅ DelP one x A ∥ (InSP zero B ∥ F) ->
    commF P (A ∥ (subst_proc (scons x id_ren) B ∥ F))
| CF_RD : forall n (P : proc n.+2) (x : ch n.+2) (A : proc n.+3) B F,
    P ≅ InSP one A ∥ (DelP zero x B ∥ F) ->
    commF P (subst_proc (scons x id_ren) A ∥ (B ∥ F)).

(** ** Normalized steps *)
Inductive nstep : forall n, proc n -> proc n -> Prop :=
| NS_ParL : forall n (P P' Q : proc n),
    nstep P P' -> nstep (P ∥ Q) (P' ∥ Q)
| NS_ParR : forall n (P Q Q' : proc n),
    nstep Q Q' -> nstep (P ∥ Q) (P ∥ Q')
| NS_Res : forall n (P P' : proc n.+2),
    nstep P P' -> nstep ((ν) P) ((ν) P')
| NS_Comm : forall n (P P' : proc n.+2),
    commF P P' -> nstep ((ν) P) ((ν) P').

(** ** A communication needs two active prefixes *)
Lemma commF_act n (P P' : proc n.+2) : commF P P' -> 2 <= act_cnt P.
Proof.
  case=> {n P P'}.
  - by move=> n P A B F Heq; rewrite (act_cnt_struct Heq).
  - by move=> n P A B F Heq; rewrite (act_cnt_struct Heq).
  - by move=> n P x A B F Heq; rewrite (act_cnt_struct Heq).
  - by move=> n P x A B F Heq; rewrite (act_cnt_struct Heq).
Qed.

(** ** Framing: a communication survives a bystander inside the binder *)
Lemma commF_frame n (P P' : proc n.+2) (H : commF P P') :
  forall G : proc n.+2,
    exists P2, commF (P ∥ G) P2 /\ P2 ≅ P' ∥ G.
Proof.
  case: H => {n P P'}.
  - move=> n P A B F Heq G.
    exists (A ∥ (B ∥ (F ∥ G))). split.
    + apply: CF_CW.
      apply: SC_Trans (SC_Cong_Par Heq (SC_Refl G)) _.
      apply: SC_Trans (SC_Par_Assoc _ _ _) _.
      exact: SC_Cong_Par (SC_Refl _) (SC_Par_Assoc _ _ _).
    + apply: SC_Sym.
      apply: SC_Trans (SC_Par_Assoc _ _ _) _.
      exact: SC_Cong_Par (SC_Refl _) (SC_Par_Assoc _ _ _).
  - move=> n P A B F Heq G.
    exists (A ∥ (B ∥ (F ∥ G))). split.
    + apply: CF_WC.
      apply: SC_Trans (SC_Cong_Par Heq (SC_Refl G)) _.
      apply: SC_Trans (SC_Par_Assoc _ _ _) _.
      exact: SC_Cong_Par (SC_Refl _) (SC_Par_Assoc _ _ _).
    + apply: SC_Sym.
      apply: SC_Trans (SC_Par_Assoc _ _ _) _.
      exact: SC_Cong_Par (SC_Refl _) (SC_Par_Assoc _ _ _).
  - move=> n P x A B F Heq G.
    exists (A ∥ (subst_proc (scons x id_ren) B ∥ (F ∥ G))). split.
    + apply: CF_DR.
      apply: SC_Trans (SC_Cong_Par Heq (SC_Refl G)) _.
      apply: SC_Trans (SC_Par_Assoc _ _ _) _.
      exact: SC_Cong_Par (SC_Refl _) (SC_Par_Assoc _ _ _).
    + apply: SC_Sym.
      apply: SC_Trans (SC_Par_Assoc _ _ _) _.
      exact: SC_Cong_Par (SC_Refl _) (SC_Par_Assoc _ _ _).
  - move=> n P x A B F Heq G.
    exists (subst_proc (scons x id_ren) A ∥ (B ∥ (F ∥ G))). split.
    + apply: CF_RD.
      apply: SC_Trans (SC_Cong_Par Heq (SC_Refl G)) _.
      apply: SC_Trans (SC_Par_Assoc _ _ _) _.
      exact: SC_Cong_Par (SC_Refl _) (SC_Par_Assoc _ _ _).
    + apply: SC_Sym.
      apply: SC_Trans (SC_Par_Assoc _ _ _) _.
      exact: SC_Cong_Par (SC_Refl _) (SC_Par_Assoc _ _ _).
Qed.

(** ** Renaming the delegated channel through the received binder *)
Lemma scons_up m n (s : ren m n) (x : ch m.+2) (z : ch m.+3) :
  up_ch (up_ch s) (scons x id_ren z)
  = scons (up_ch (up_ch s) x) id_ren (up_ch (up_ch (up_ch s)) z).
Proof. by case: z. Qed.

(** ** Forward equivariance *)
Lemma commF_ren n (P P' : proc n.+2) (H : commF P P') :
  forall m (s : ren n m),
    commF (subst_proc (up_ch (up_ch s)) P)
          (subst_proc (up_ch (up_ch s)) P').
Proof.
  case: H => {n P P'}.
  - move=> n P A B F Heq m s.
    have HX := struct_eq_ren Heq (up_ch (up_ch s)).
    rewrite /= in HX.
    rewrite /=.
    exact: CF_CW HX.
  - move=> n P A B F Heq m s.
    have HX := struct_eq_ren Heq (up_ch (up_ch s)).
    rewrite /= in HX.
    rewrite /=.
    exact: CF_WC HX.
  - move=> n P x A B F Heq m s.
    have HX := struct_eq_ren Heq (up_ch (up_ch s)).
    rewrite /= in HX.
    rewrite /=.
    have -> : subst_proc (up_ch (up_ch s))
                (subst_proc (scons x id_ren) B)
            = subst_proc (scons (up_ch (up_ch s) x) id_ren)
                (subst_proc (up_ch (up_ch (up_ch s))) B).
      rewrite !subst_proc_comp. apply: subst_eqP => z.
      exact: scons_up.
    exact: CF_DR HX.
  - move=> n P x A B F Heq m s.
    have HX := struct_eq_ren Heq (up_ch (up_ch s)).
    rewrite /= in HX.
    rewrite /=.
    have -> : subst_proc (up_ch (up_ch s))
                (subst_proc (scons x id_ren) A)
            = subst_proc (scons (up_ch (up_ch s) x) id_ren)
                (subst_proc (up_ch (up_ch (up_ch s))) A).
      rewrite !subst_proc_comp. apply: subst_eqP => z.
      exact: scons_up.
    exact: CF_RD HX.
Qed.

Lemma nstep_ren n (P P' : proc n) (H : nstep P P') :
  forall m (s : ren n m), nstep (subst_proc s P) (subst_proc s P').
Proof.
  elim: H => {n P P'}.
  - move=> n P P' Q _ IH m s /=. exact: NS_ParL (IH _ _).
  - move=> n P Q Q' _ IH m s /=. exact: NS_ParR (IH _ _).
  - move=> n P P' _ IH m s /=. exact: NS_Res (IH _ _).
  - move=> n P P' HC m s /=. exact: NS_Comm (commF_ren HC s).
Qed.

(** ** Syntax-directed inversion *)
Ltac ns_inv H :=
  inversion H; subst;
  repeat match goal with
  | [ E : existT _ ?k _ = existT _ ?k _ |- _ ] =>
      apply (inj_pair2_eq_dec _ Nat.eq_dec) in E; subst
  end.

Lemma nstep_end_noT n R : nstep (EndP n) R -> False.
Proof. move=> H. by ns_inv H. Qed.

Lemma nstep_close_noT n (x : ch n) K R : nstep (CloseP x K) R -> False.
Proof. move=> H. by ns_inv H. Qed.

Lemma nstep_wait_noT n (x : ch n) K R : nstep (WaitP x K) R -> False.
Proof. move=> H. by ns_inv H. Qed.

Lemma nstep_del_noT n (x y : ch n) K R : nstep (DelP x y K) R -> False.
Proof. move=> H. by ns_inv H. Qed.

Lemma nstep_ins_noT n (x : ch n) (K : proc n.+1) R :
  nstep (InSP x K) R -> False.
Proof. move=> H. by ns_inv H. Qed.

Lemma nstep_par_inv n (P Q : proc n) R :
  nstep (P ∥ Q) R ->
  (exists P', R = P' ∥ Q /\ nstep P P') \/
  (exists Q', R = P ∥ Q' /\ nstep Q Q').
Proof.
  move=> H. ns_inv H.
  - left. eexists. split; [reflexivity | assumption].
  - right. eexists. split; [reflexivity | assumption].
Qed.

Lemma nstep_res_inv n (P : proc n.+2) R :
  nstep ((ν) P) R ->
  exists P', R = (ν) P' /\ (nstep P P' \/ commF P P').
Proof.
  move=> H. ns_inv H.
  - eexists. split; [reflexivity | by left].
  - eexists. split; [reflexivity | by right].
Qed.

Print Assumptions commF_frame.
Print Assumptions nstep_ren.
