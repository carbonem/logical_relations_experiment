(** * Inversion toolkit, stage 1: active prefixes and inert processes

    The compatibility lemmas of the fundamental theorem must control what
    [⇛*] and [≅] can do to each process shape.  The first, coarsest
    invariant: the number of *active* (unguarded) communication prefixes.

    - [act_cnt] is invariant under renaming and under [≅];
    - a reduction step requires at least two active prefixes, so
      processes with fewer are *inert*: their only reduct is themselves;
    - a process with no active prefix is semantically trivial: it
      inhabits the relation at every context and depth ([Esem_inact]).
      This discharges the [T_End] compatibility case -- and shows
      semantic weakening at work: [∅] is in the relation at *any*
      context, not just the empty one. *)

From mathcomp Require Import all_ssreflect.
From Tait Require Import synsem Errors LogRel.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** Active prefixes

    Prefixes guard their continuations: only the head counts. *)
Fixpoint act_cnt {n : nat} (P : proc n) : nat :=
  match P with
  | EndP => 0
  | WaitP _ _ => 1
  | CloseP _ _ => 1
  | ResP Q => act_cnt Q
  | ParP P1 P2 => act_cnt P1 + act_cnt P2
  | InSP _ _ => 1
  | DelP _ _ _ => 1
  end.

(** Renaming neither duplicates nor drops prefixes. *)
Lemma act_cnt_ren n (P : proc n) :
  forall m (s : ren n m), act_cnt (subst_proc s P) = act_cnt P.
Proof.
  elim: P =>
    [n'|n' x Q IH|n' x Q IH|n' Q IH|n' P1 IH1 P2 IH2|n' x Q IH|n' x y Q IH]
    m s //=.
  by rewrite IH1 IH2.
Qed.

(** Structural congruence preserves the count. *)
Lemma act_cnt_struct n (P Q : proc n) : P ≅ Q -> act_cnt P = act_cnt Q.
Proof.
  move=> H; elim: H => {n P Q} //=.
  - by move=> n P Q; rewrite addnC.
  - by move=> n P Q R; rewrite addnA.
  - by move=> n P; rewrite addn0.
  - by move=> n P Q; rewrite act_cnt_ren.
  - by move=> n P; rewrite act_cnt_ren.
  - by move=> n P; rewrite !act_cnt_ren.
  - by move=> n P Q R _ -> _ ->.
  - by move=> n P P' Q Q' _ -> _ ->.
Qed.

(** A reduction step needs a redex: at least two active prefixes. *)
Lemma act_cnt_step n (P Q : proc n) : P ⇛ Q -> 2 <= act_cnt P.
Proof.
  move=> H; elim: H => {n P Q}.
  - by move=> n P Q _ IH.
  - move=> n P Q R _ IH. exact: leq_trans IH (leq_addr _ _).
  - by move=> n P P' Q Q' Hpp _ IH _; rewrite (act_cnt_struct Hpp).
  - by move=> n P Q.
  - by move=> n x P Q.
Qed.

(** ** Inert processes *)
Lemma inert_step n (P Q : proc n) : act_cnt P < 2 -> P ⇛ Q -> False.
Proof. by move=> Hlt Hst; move: (act_cnt_step Hst); rewrite leqNgt Hlt. Qed.

Lemma inert_mreduce n (P Q : proc n) : act_cnt P < 2 -> P ⇛* Q -> Q = P.
Proof.
  move=> Hlt H; case: H Hlt => // P0 Q0 R0 Hst _ Hlt.
  by case: (inert_step Hlt Hst).
Qed.

(** A process with no active prefix is congruent to the inert [∅]. *)
Lemma act0_inact n (P : proc n) : act_cnt P = 0 -> P ≅ EndP n.
Proof.
  elim: P => //=.
  - move=> n' _. exact: SC_Refl.
  - move=> n' Q IH H.
    exact: SC_Trans (SC_Cong_Res (IH H)) SC_Res_Inact.
  - move=> n' P1 IH1 P2 IH2 /eqP; rewrite addn_eq0 => /andP[/eqP H1 /eqP H2].
    apply: SC_Trans (SC_Par_Inact _).
    exact: SC_Cong_Par (IH1 H1) (IH2 H2).
Qed.

(** ** Prefix-free processes are semantically trivial

    Nothing to expose, nothing to reduce, and every restriction it is
    congruent to hides another prefix-free process.  This is also the
    lemma that makes the never-vacuous semantic-cut clause harmless on
    junk wrappings of dead processes. *)
Lemma Esem_inact k : forall n (Δ : sctx n) (P : proc n),
  act_cnt P = 0 -> Esem k Δ P.
Proof.
  elim: k => [//|k IH] n Δ P H0 P' Hred.
  have Hlt2 : act_cnt P < 2 by rewrite H0.
  have HP' := inert_mreduce Hlt2 Hred; subst P'.
  have Hnoexp : forall a (x : ch n) F R, P ≅ F ∥ R -> prefix_at a x F -> False.
    move=> a x F R HFR Hpa.
    have Hact : act_cnt (F ∥ R) = 0 by rewrite -(act_cnt_struct HFR).
    by case: Hpa Hact => //=.
  split.
  - move=> a x F R HFR Hpa. by case: (Hnoexp _ _ _ _ HFR Hpa).
  - move=> x S _. case: S => [| |S1 S2|S1 S2] /=.
    + move=> K R HFR. by case: (Hnoexp _ _ _ _ HFR (PA_Close x K)).
    + move=> K R HFR. by case: (Hnoexp _ _ _ _ HFR (PA_Wait x K)).
    + move=> y K R HFR. by case: (Hnoexp _ _ _ _ HFR (PA_DelS x y K)).
    + move=> K R HFR. by case: (Hnoexp _ _ _ _ HFR (PA_DelR x K)).
  - move=> Q HQ. exists SClose. apply: IH.
    by have := act_cnt_struct HQ; rewrite H0 /= => <-.
Qed.

Lemma SEM_inact n (Δ : sctx n) (P : proc n) : act_cnt P = 0 -> Δ ⊨ P.
Proof. move=> H0 k. by apply: Esem_inact. Qed.

(** Compatibility lemma for [T_End] -- in fact stronger: any context. *)
Lemma SEM_end n (Δ : sctx n) : Δ ⊨ EndP n.
Proof. by apply: SEM_inact. Qed.

(** ** Renaming algebra (functoriality of [subst_proc], extensionally) *)
Lemma up_ch_ext n m (s t : ren n m) :
  (forall x, s x = t x) -> forall x, up_ch s x = up_ch t x.
Proof. by move=> H [i|] //=; rewrite /up_ch /= H. Qed.

Lemma subst_proc_ext n (P : proc n) :
  forall m (s t : ren n m),
  (forall x, s x = t x) -> subst_proc s P = subst_proc t P.
Proof.
  elim: P =>
    [n'|n' x Q IH|n' x Q IH|n' Q IH|n' P1 IH1 P2 IH2|n' x Q IH|n' x y Q IH]
    m s t H //=.
  - by rewrite H (IH _ _ _ H).
  - by rewrite H (IH _ _ _ H).
  - by rewrite (IH _ _ _ (up_ch_ext (up_ch_ext H))).
  - by rewrite (IH1 _ _ _ H) (IH2 _ _ _ H).
  - by rewrite H (IH _ _ _ (up_ch_ext H)).
  - by rewrite !H (IH _ _ _ H).
Qed.

Lemma up_ch_comp n m p (s : ren n m) (t : ren m p) (x : ch n.+1) :
  up_ch t (up_ch s x) = up_ch (t \o s) x.
Proof. by case: x. Qed.

Lemma subst_proc_comp n (P : proc n) :
  forall m p (s : ren n m) (t : ren m p),
  subst_proc t (subst_proc s P) = subst_proc (t \o s) P.
Proof.
  elim: P =>
    [n'|n' x Q IH|n' x Q IH|n' Q IH|n' P1 IH1 P2 IH2|n' x Q IH|n' x y Q IH]
    m p s t //=.
  - by rewrite IH.
  - by rewrite IH.
  - rewrite IH. congr ResP. apply: subst_proc_ext => z.
    transitivity (up_ch (up_ch t \o up_ch s) z); first exact: up_ch_comp.
    apply: up_ch_ext => w. exact: up_ch_comp.
  - by rewrite IH1 IH2.
  - rewrite IH. congr InSP. apply: subst_proc_ext => z.
    exact: up_ch_comp.
  - by rewrite IH.
Qed.

Lemma up_ch_id n (x : ch n.+1) : up_ch id_ren x = x.
Proof. by case: x. Qed.

Lemma subst_proc_id n (P : proc n) : subst_proc id_ren P = P.
Proof.
  elim: P =>
    [n'|n' x Q IH|n' x Q IH|n' Q IH|n' P1 IH1 P2 IH2|n' x Q IH|n' x y Q IH] //=.
  - by rewrite IH.
  - by rewrite IH.
  - rewrite -{2}IH. congr ResP. apply: subst_proc_ext => z.
    by rewrite (up_ch_ext (@up_ch_id _)) up_ch_id.
  - by rewrite IH1 IH2.
  - rewrite -{2}IH. congr InSP. apply: subst_proc_ext => z.
    exact: up_ch_id.
  - by rewrite IH.
Qed.

(** Prefixes rename to prefixes. *)
Lemma prefix_at_ren m n (s : ren m n) a (x : ch m) F :
  prefix_at a x F -> prefix_at a (s x) (subst_proc s F).
Proof. by case=> * /=; constructor. Qed.


(** The permutation exchanging the received-channel binder with a
    session's two binders (used to re-associate binder order when a
    receive happens under a restriction). *)
Definition rho3 {n : nat} : ren n.+3 n.+3 :=
  scons (shift (shift zero))
        (scons zero (scons (shift zero)
                           (fun w => shift (shift (shift w))))).

Print Assumptions SEM_end.
