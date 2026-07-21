(** * A visible-action labelled transition system for the calculus

    Five syntax-directed transition families, one per communication
    capability -- no [τ] (internal dynamics remains the reduction [⇛] of
    [synsem.v]).  Because no rule mentions [≅], transition inversion is
    trivial; the single place structural congruence will be fought is the
    transfer lemma (congruent processes have matching transitions),
    proved once, by one induction.

    Scoping conventions (well-scoped de Bruijn, double binders):
    - [ltsc x P P']    : [P] fires a close on [x];      [P' : proc n]
    - [ltsw x P P']    : wait on [x];                   [P' : proc n]
    - [ltsf x y P P']  : delegates the free [y] on [x]; [P' : proc n]
    - [ltsr x P P']    : receives on [x]; continuation OPEN, received
                         channel = [zero];              [P' : proc n.+1]
    - [ltsb x P P']    : delegates a BOUND endpoint on [x] (extrusion);
                         the dissolved session pair is exposed with
                         sent = [zero], kept = [one];   [P' : proc n.+2]

    Design notes.
    - Parallel frames shift along open continuations ([ltsr] by [shift],
      [ltsb] by [shift ∘ shift]) -- the same shapes the logical
      relation's receive clause and the reduction's scope extrusion use.
    - [LB_Open1] normalises which endpoint was sent via
      [swap_ch zero one]; [LB_Res] commutes the extruded pair past a
      passing binder via [swap_ch zero two]/[swap_ch one three] -- i.e.
      [SC_Res_SwapC]/[SC_Res_SwapB] are exactly the LTS's binder
      bookkeeping, which is why transfer can hope to hold.
    - [LR_Res] re-associates the received binder past a passing session
      binder via [rho3] -- the permutation already used by the semantic
      restriction lemma.

    This file: definitions, renaming commutation laws, and
    forward equivariance of all five families.  Transfer is next. *)

From mathcomp Require Import all_ssreflect.
From Tait Require Import synsem Errors LogRel Toolkit.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** The transition families *)

Inductive ltsc : forall n, ch n -> proc n -> proc n -> Prop :=
| LC_Pfx : forall n (x : ch n) K, ltsc x (CloseP x K) K
| LC_ParL : forall n (x : ch n) P P' Q,
    ltsc x P P' -> ltsc x (P ∥ Q) (P' ∥ Q)
| LC_ParR : forall n (x : ch n) P Q Q',
    ltsc x Q Q' -> ltsc x (P ∥ Q) (P ∥ Q')
| LC_Res : forall n (x : ch n) (P P' : proc n.+2),
    ltsc (shift (shift x)) P P' -> ltsc x ((ν) P) ((ν) P').

Inductive ltsw : forall n, ch n -> proc n -> proc n -> Prop :=
| LW_Pfx : forall n (x : ch n) K, ltsw x (WaitP x K) K
| LW_ParL : forall n (x : ch n) P P' Q,
    ltsw x P P' -> ltsw x (P ∥ Q) (P' ∥ Q)
| LW_ParR : forall n (x : ch n) P Q Q',
    ltsw x Q Q' -> ltsw x (P ∥ Q) (P ∥ Q')
| LW_Res : forall n (x : ch n) (P P' : proc n.+2),
    ltsw (shift (shift x)) P P' -> ltsw x ((ν) P) ((ν) P').

Inductive ltsf : forall n, ch n -> ch n -> proc n -> proc n -> Prop :=
| LF_Pfx : forall n (x y : ch n) K, ltsf x y (DelP x y K) K
| LF_ParL : forall n (x y : ch n) P P' Q,
    ltsf x y P P' -> ltsf x y (P ∥ Q) (P' ∥ Q)
| LF_ParR : forall n (x y : ch n) P Q Q',
    ltsf x y Q Q' -> ltsf x y (P ∥ Q) (P ∥ Q')
| LF_Res : forall n (x y : ch n) (P P' : proc n.+2),
    ltsf (shift (shift x)) (shift (shift y)) P P' ->
    ltsf x y ((ν) P) ((ν) P').

Inductive ltsr : forall n, ch n -> proc n -> proc n.+1 -> Prop :=
| LR_Pfx : forall n (x : ch n) (K : proc n.+1), ltsr x (InSP x K) K
| LR_ParL : forall n (x : ch n) P (P' : proc n.+1) Q,
    ltsr x P P' -> ltsr x (P ∥ Q) (P' ∥ subst_proc shift Q)
| LR_ParR : forall n (x : ch n) P Q (Q' : proc n.+1),
    ltsr x Q Q' -> ltsr x (P ∥ Q) (subst_proc shift P ∥ Q')
| LR_Res : forall n (x : ch n) (P : proc n.+2) (P' : proc n.+3),
    ltsr (shift (shift x)) P P' ->
    ltsr x ((ν) P) ((ν) (subst_proc rho3 P')).

Inductive ltsb : forall n, ch n -> proc n -> proc n.+2 -> Prop :=
| LB_Open0 : forall n (x : ch n) (P P' : proc n.+2),
    ltsf (shift (shift x)) zero P P' -> ltsb x ((ν) P) P'
| LB_Open1 : forall n (x : ch n) (P P' : proc n.+2),
    ltsf (shift (shift x)) one P P' ->
    ltsb x ((ν) P) (subst_proc (swap_ch zero one) P')
| LB_ParL : forall n (x : ch n) P (P' : proc n.+2) Q,
    ltsb x P P' -> ltsb x (P ∥ Q) (P' ∥ subst_proc (shift \o shift) Q)
| LB_ParR : forall n (x : ch n) P Q (Q' : proc n.+2),
    ltsb x Q Q' -> ltsb x (P ∥ Q) (subst_proc (shift \o shift) P ∥ Q')
| LB_Res : forall n (x : ch n) (P : proc n.+2) (P' : proc n.+4),
    ltsb (shift (shift x)) P P' ->
    ltsb x ((ν) P)
         ((ν) (subst_proc (swap_ch one three)
                          (subst_proc (swap_ch zero two) P'))).

(** ** Renaming commutation laws (all definitional case analyses) *)

Lemma up2_shift2 m n (s : ren m n) (z : ch m) :
  up_ch (up_ch s) (shift (shift z)) = shift (shift (s z)).
Proof. by []. Qed.

Lemma up_shift m n (s : ren m n) (z : ch m) :
  up_ch s (shift z) = shift (s z).
Proof. by []. Qed.

Lemma up2_zero m n (s : ren m n) :
  up_ch (up_ch s) zero = zero.
Proof. by []. Qed.

Lemma up2_one m n (s : ren m n) :
  up_ch (up_ch s) one = one.
Proof. by []. Qed.

Lemma rho3_up3 m n (s : ren m n) (z : ch m.+3) :
  rho3 (up_ch (up_ch (up_ch s)) z) = up_ch (up_ch (up_ch s)) (rho3 z).
Proof. by case: z => [[[w|]|]|]. Qed.

Lemma swap01_up2 m n (s : ren m n) (z : ch m.+2) :
  swap_ch zero one (up_ch (up_ch s) z) = up_ch (up_ch s) (swap_ch zero one z).
Proof. by case: z => [[w|]|]. Qed.

Lemma swap02_up4 m n (s : ren m n) (z : ch m.+4) :
  swap_ch zero two (up_ch (up_ch (up_ch (up_ch s))) z)
  = up_ch (up_ch (up_ch (up_ch s))) (swap_ch zero two z).
Proof. by case: z => [[[[w|]|]|]|]. Qed.

Lemma swap13_up4 m n (s : ren m n) (z : ch m.+4) :
  swap_ch one three (up_ch (up_ch (up_ch (up_ch s))) z)
  = up_ch (up_ch (up_ch (up_ch s))) (swap_ch one three z).
Proof. by case: z => [[[[w|]|]|]|]. Qed.

(** ** Forward equivariance: transitions are preserved by renaming *)

Lemma ltsc_ren n (x : ch n) (P P' : proc n) :
  ltsc x P P' ->
  forall m (s : ren n m), ltsc (s x) (subst_proc s P) (subst_proc s P').
Proof.
  elim=> {n x P P'}.
  - move=> n x K m s /=. exact: LC_Pfx.
  - move=> n x P P' Q _ IH m s /=. exact: LC_ParL (IH _ _).
  - move=> n x P Q Q' _ IH m s /=. exact: LC_ParR (IH _ _).
  - move=> n x P P' _ IH m s /=. apply: LC_Res.
    by have := IH _ (up_ch (up_ch s)); rewrite up2_shift2.
Qed.

Lemma ltsw_ren n (x : ch n) (P P' : proc n) :
  ltsw x P P' ->
  forall m (s : ren n m), ltsw (s x) (subst_proc s P) (subst_proc s P').
Proof.
  elim=> {n x P P'}.
  - move=> n x K m s /=. exact: LW_Pfx.
  - move=> n x P P' Q _ IH m s /=. exact: LW_ParL (IH _ _).
  - move=> n x P Q Q' _ IH m s /=. exact: LW_ParR (IH _ _).
  - move=> n x P P' _ IH m s /=. apply: LW_Res.
    by have := IH _ (up_ch (up_ch s)); rewrite up2_shift2.
Qed.

Lemma ltsf_ren n (x y : ch n) (P P' : proc n) :
  ltsf x y P P' ->
  forall m (s : ren n m), ltsf (s x) (s y) (subst_proc s P) (subst_proc s P').
Proof.
  elim=> {n x y P P'}.
  - move=> n x y K m s /=. exact: LF_Pfx.
  - move=> n x y P P' Q _ IH m s /=. exact: LF_ParL (IH _ _).
  - move=> n x y P Q Q' _ IH m s /=. exact: LF_ParR (IH _ _).
  - move=> n x y P P' _ IH m s /=. apply: LF_Res.
    by have := IH _ (up_ch (up_ch s)); rewrite !up2_shift2.
Qed.

Lemma ltsr_ren n (x : ch n) (P : proc n) (P' : proc n.+1) :
  ltsr x P P' ->
  forall m (s : ren n m),
    ltsr (s x) (subst_proc s P) (subst_proc (up_ch s) P').
Proof.
  elim=> {n x P P'}.
  - move=> n x K m s /=. exact: LR_Pfx.
  - move=> n x P P' Q _ IH m s /=.
    have -> : subst_proc (up_ch s) (subst_proc shift Q)
              = subst_proc shift (subst_proc s Q).
      rewrite !subst_proc_comp. apply: subst_proc_ext => z.
      exact: up_shift.
    exact: LR_ParL (IH _ _).
  - move=> n x P Q Q' _ IH m s /=.
    have -> : subst_proc (up_ch s) (subst_proc shift P)
              = subst_proc shift (subst_proc s P).
      rewrite !subst_proc_comp. apply: subst_proc_ext => z.
      exact: up_shift.
    exact: LR_ParR (IH _ _).
  - move=> n x P P' _ IH m s /=.
    have -> : subst_proc (up_ch (up_ch (up_ch s))) (subst_proc rho3 P')
              = subst_proc rho3 (subst_proc (up_ch (up_ch (up_ch s))) P').
      rewrite !subst_proc_comp. apply: subst_proc_ext => z.
      by rewrite /= rho3_up3.
    apply: LR_Res.
    by have := IH _ (up_ch (up_ch s)); rewrite up2_shift2.
Qed.

Lemma ltsb_ren n (x : ch n) (P : proc n) (P' : proc n.+2) :
  ltsb x P P' ->
  forall m (s : ren n m),
    ltsb (s x) (subst_proc s P) (subst_proc (up_ch (up_ch s)) P').
Proof.
  elim=> {n x P P'}.
  - move=> n x P P' Hf m s /=. apply: LB_Open0.
    have := ltsf_ren Hf (up_ch (up_ch s)).
    by rewrite up2_shift2 up2_zero.
  - move=> n x P P' Hf m s /=.
    have -> : subst_proc (up_ch (up_ch s)) (subst_proc (swap_ch zero one) P')
              = subst_proc (swap_ch zero one)
                           (subst_proc (up_ch (up_ch s)) P').
      rewrite !subst_proc_comp. apply: subst_proc_ext => z.
      by rewrite /= swap01_up2.
    apply: LB_Open1.
    have := ltsf_ren Hf (up_ch (up_ch s)).
    by rewrite up2_shift2 up2_one.
  - move=> n x P P' Q _ IH m s /=.
    have -> : subst_proc (up_ch (up_ch s)) (subst_proc (shift \o shift) Q)
              = subst_proc (shift \o shift) (subst_proc s Q).
      rewrite !subst_proc_comp. apply: subst_proc_ext => z.
      exact: up2_shift2.
    exact: LB_ParL (IH _ _).
  - move=> n x P Q Q' _ IH m s /=.
    have -> : subst_proc (up_ch (up_ch s)) (subst_proc (shift \o shift) P)
              = subst_proc (shift \o shift) (subst_proc s P).
      rewrite !subst_proc_comp. apply: subst_proc_ext => z.
      exact: up2_shift2.
    exact: LB_ParR (IH _ _).
  - move=> n x P P' _ IH m s /=.
    have -> : subst_proc (up_ch (up_ch (up_ch (up_ch s))))
                (subst_proc (swap_ch one three)
                   (subst_proc (swap_ch zero two) P'))
              = subst_proc (swap_ch one three)
                  (subst_proc (swap_ch zero two)
                     (subst_proc (up_ch (up_ch (up_ch (up_ch s)))) P')).
      rewrite !subst_proc_comp. apply: subst_proc_ext => z.
      by rewrite /= swap02_up4 swap13_up4.
    apply: LB_Res.
    by have := IH _ (up_ch (up_ch s)); rewrite up2_shift2.
Qed.

(** ** Sanity: the transition families see through binders *)
Example ltsc_under_binder n (x : ch n) K :
  ltsc x ((ν) (CloseP (shift (shift x)) K)) ((ν) K).
Proof. apply: LC_Res. exact: LC_Pfx. Qed.

Print Assumptions ltsb_ren.
