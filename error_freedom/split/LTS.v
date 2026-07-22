(** * Labelled semantics for the polarized calculus

    Five families of visible transitions (one per prefix kind), then
    internal steps [ltstP] formed AT PARALLEL COMPOSITION by
    synchronizing an action at [c] with the matching action at
    [pflip c].  No structural congruence, and -- unlike the τ-calculus
    over the double-binder syntax ([Tau.v]) -- no synchronization
    descent: the restriction rule of [ltstP] is plain congruence,
    because a redex is visible at the ∥ that separates the two
    participants.

    Visible families:

      ltscP c P P'      P --c!-->  P'     close
      ltswP c P P'      P --c?-->  P'     wait
      ltsfP c d P P'    P --c!d--> P'     free send of endpoint d
      ltsrP c d P P'    P --c?d--> P'     receive (EARLY: d is the
                                          received endpoint, already
                                          substituted into P')
      ltsbP c ρ P P'    P --c!(νρ)--> P'  bound send: P' lives at
                                          n.+1, the sent fresh name is
                                          [zero], the emitted endpoint
                                          is [(zero, ρ)]

    Early input pays off twice: the parallel frames of [ltsrP] need no
    shifting (the received object is at the outer scope already), and
    bound send needs no polarity-normalizing swap ([LB_Open0/Open1] of
    the old [LTS.v]): the two endpoints of the opened name are
    [(zero, pos)] and [(zero, neg)], one name, and the label's [ρ]
    remembers which one was sent.

    τ-formation (the six [PT_*] communication rules):

      close/wait   c! against (flip c)?
      free deleg   c!d against (flip c)?d
      bound deleg  c!(νρ) against input of the fresh endpoint:
                   the receiver is shifted into the opened scope and
                   receives [(zero, ρ)]; the result is rebound, (ν)(_∥_).

    Communication happens also at free channels: a par whose two sides
    hold co-endpoints of a free name steps.  (The logical relation
    will let the context advance along such steps; the old fixed-Δ
    reading was tied to communication-under-ν.) *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import Base Proc.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope pol_scope.

(** Lifting an endpoint into an opened scope. *)
Definition pshift {n : nat} (c : pch n) : pch n.+1 := pren shift c.

(** ** Close *)
Inductive ltscP : forall n, pch n -> procP n -> procP n -> Prop :=
| PC_Pfx : forall n (c : pch n) K,
    ltscP c (c !․ K) K
| PC_ParL : forall n (c : pch n) P P' Q,
    ltscP c P P' -> ltscP c (P ∥ Q) (P' ∥ Q)
| PC_ParR : forall n (c : pch n) P Q Q',
    ltscP c Q Q' -> ltscP c (P ∥ Q) (P ∥ Q')
| PC_Res : forall n (c : pch n) (P P' : procP n.+1),
    ltscP (pshift c) P P' -> ltscP c ((ν) P) ((ν) P').

(** ** Wait *)
Inductive ltswP : forall n, pch n -> procP n -> procP n -> Prop :=
| PW_Pfx : forall n (c : pch n) K,
    ltswP c (c ?․ K) K
| PW_ParL : forall n (c : pch n) P P' Q,
    ltswP c P P' -> ltswP c (P ∥ Q) (P' ∥ Q)
| PW_ParR : forall n (c : pch n) P Q Q',
    ltswP c Q Q' -> ltswP c (P ∥ Q) (P ∥ Q')
| PW_Res : forall n (c : pch n) (P P' : procP n.+1),
    ltswP (pshift c) P P' -> ltswP c ((ν) P) ((ν) P').

(** ** Free send *)
Inductive ltsfP : forall n, pch n -> pch n -> procP n -> procP n -> Prop :=
| PF_Pfx : forall n (c d : pch n) K,
    ltsfP c d (c ! d ․ K) K
| PF_ParL : forall n (c d : pch n) P P' Q,
    ltsfP c d P P' -> ltsfP c d (P ∥ Q) (P' ∥ Q)
| PF_ParR : forall n (c d : pch n) P Q Q',
    ltsfP c d Q Q' -> ltsfP c d (P ∥ Q) (P ∥ Q')
| PF_Res : forall n (c d : pch n) (P P' : procP n.+1),
    ltsfP (pshift c) (pshift d) P P' -> ltsfP c d ((ν) P) ((ν) P').

(** ** Receive (early) *)
Inductive ltsrP : forall n, pch n -> pch n -> procP n -> procP n -> Prop :=
| PR_Pfx : forall n (c : pch n) (y : ch n) (r : pol) (K : procP n.+1),
    ltsrP c (y, r) (c ?( r )․ K) (psubst (scons y id_ren) K)
| PR_ParL : forall n (c d : pch n) P P' Q,
    ltsrP c d P P' -> ltsrP c d (P ∥ Q) (P' ∥ Q)
| PR_ParR : forall n (c d : pch n) P Q Q',
    ltsrP c d Q Q' -> ltsrP c d (P ∥ Q) (P ∥ Q')
| PR_Res : forall n (c d : pch n) (P P' : procP n.+1),
    ltsrP (pshift c) (pshift d) P P' -> ltsrP c d ((ν) P) ((ν) P').

(** ** Bound send: delegating an endpoint of one's own restriction *)
Inductive ltsbP : forall n, pch n -> pol -> procP n -> procP n.+1 -> Prop :=
| PB_Open : forall n (c : pch n) (r : pol) (P P' : procP n.+1),
    ltsfP (pshift c) (zero, r) P P' ->
    ltsbP c r ((ν) P) P'
| PB_ParL : forall n (c : pch n) (r : pol) P (P' : procP n.+1) Q,
    ltsbP c r P P' -> ltsbP c r (P ∥ Q) (P' ∥ psubst shift Q)
| PB_ParR : forall n (c : pch n) (r : pol) P Q (Q' : procP n.+1),
    ltsbP c r Q Q' -> ltsbP c r (P ∥ Q) (psubst shift P ∥ Q')
| PB_Res : forall n (c : pch n) (r : pol) (P : procP n.+1)
    (P' : procP n.+2),
    ltsbP (pshift c) r P P' ->
    ltsbP c r ((ν) P) ((ν) (psubst (swap_ch zero one) P')).

(** ** Select: emit a label at an endpoint *)
Inductive ltsselP : forall n, pch n -> bool -> procP n -> procP n -> Prop :=
| PS_Pfx : forall n (c : pch n) (b : bool) K,
    ltsselP c b (c ◁ b ․ K) K
| PS_ParL : forall n (c : pch n) b P P' Q,
    ltsselP c b P P' -> ltsselP c b (P ∥ Q) (P' ∥ Q)
| PS_ParR : forall n (c : pch n) b P Q Q',
    ltsselP c b Q Q' -> ltsselP c b (P ∥ Q) (P ∥ Q')
| PS_Res : forall n (c : pch n) b (P P' : procP n.+1),
    ltsselP (pshift c) b P P' -> ltsselP c b ((ν) P) ((ν) P').

(** ** Branch: receive a label at an endpoint (both labels offered) *)
Inductive ltsbrP : forall n, pch n -> bool -> procP n -> procP n -> Prop :=
| PBR_Pfx : forall n (c : pch n) (b : bool) K1 K2,
    ltsbrP c b (c ▷ ( K1 | K2 )) (if b then K1 else K2)
| PBR_ParL : forall n (c : pch n) b P P' Q,
    ltsbrP c b P P' -> ltsbrP c b (P ∥ Q) (P' ∥ Q)
| PBR_ParR : forall n (c : pch n) b P Q Q',
    ltsbrP c b Q Q' -> ltsbrP c b (P ∥ Q) (P ∥ Q')
| PBR_Res : forall n (c : pch n) b (P P' : procP n.+1),
    ltsbrP (pshift c) b P P' -> ltsbrP c b ((ν) P) ((ν) P').

(** ** Internal steps: synchronization at ∥ *)
Inductive ltstP : forall n, procP n -> procP n -> Prop :=
(* congruence *)
| PT_ParL : forall n (P P' Q : procP n),
    ltstP P P' -> ltstP (P ∥ Q) (P' ∥ Q)
| PT_ParR : forall n (P Q Q' : procP n),
    ltstP Q Q' -> ltstP (P ∥ Q) (P ∥ Q')
| PT_Res : forall n (P P' : procP n.+1),
    ltstP P P' -> ltstP ((ν) P) ((ν) P')
(* close against wait *)
| PT_CW : forall n (c : pch n) P P' Q Q',
    ltscP c P P' -> ltswP (pflip c) Q Q' ->
    ltstP (P ∥ Q) (P' ∥ Q')
| PT_WC : forall n (c : pch n) P P' Q Q',
    ltswP (pflip c) P P' -> ltscP c Q Q' ->
    ltstP (P ∥ Q) (P' ∥ Q')
(* free delegation *)
| PT_DR : forall n (c d : pch n) P P' Q Q',
    ltsfP c d P P' -> ltsrP (pflip c) d Q Q' ->
    ltstP (P ∥ Q) (P' ∥ Q')
| PT_RD : forall n (c d : pch n) P P' Q Q',
    ltsrP (pflip c) d P P' -> ltsfP c d Q Q' ->
    ltstP (P ∥ Q) (P' ∥ Q')
(* bound delegation: open on one side, receive the fresh endpoint on
   the other, rebind *)
| PT_BR : forall n (c : pch n) (r : pol) P (P' : procP n.+1) Q Q',
    ltsbP c r P P' ->
    ltsrP (pshift (pflip c)) (zero, r) (psubst shift Q) Q' ->
    ltstP (P ∥ Q) ((ν) (P' ∥ Q'))
| PT_RB : forall n (c : pch n) (r : pol) P P' Q (Q' : procP n.+1),
    ltsrP (pshift (pflip c)) (zero, r) (psubst shift P) P' ->
    ltsbP c r Q Q' ->
    ltstP (P ∥ Q) ((ν) (P' ∥ Q'))
(* selection against branching *)
| PT_SB : forall n (c : pch n) (b : bool) P P' Q Q',
    ltsselP c b P P' -> ltsbrP (pflip c) b Q Q' ->
    ltstP (P ∥ Q) (P' ∥ Q')
| PT_BS : forall n (c : pch n) (b : bool) P P' Q Q',
    ltsbrP (pflip c) b P P' -> ltsselP c b Q Q' ->
    ltstP (P ∥ Q) (P' ∥ Q').

(** Reflexive-transitive closure. *)
Reserved Notation "P '—τ*→' Q" (at level 50).
Inductive ltstsP : forall n, procP n -> procP n -> Prop :=
| PTS_refl : forall n (P : procP n), P —τ*→ P
| PTS_step : forall n (P Q R : procP n),
    ltstP P Q -> Q —τ*→ R -> P —τ*→ R
where "P '—τ*→' Q" := (ltstsP P Q).

(** Dependent-family inversion: [inversion] plus [existT] cleanup. *)
Ltac pinv H :=
  inversion H; subst;
  repeat match goal with
  | [ E : existT _ ?k _ = existT _ ?k _ |- _ ] =>
      apply (inj_pair2_eq_dec _ Nat.eq_dec) in E; subst
  end.

(** ** Inversion suite: prefixes determine their transitions *)

Lemma pinv_c_close n (c e : pch n) K R : ltscP c (PClose e K) R -> c = e.
Proof. move=> H. by pinv H. Qed.

Lemma pinv_c_wait n (c e : pch n) K R : ltscP c (PWait e K) R -> False.
Proof. move=> H. by pinv H. Qed.

Lemma pinv_w_wait n (c e : pch n) K R : ltswP c (PWait e K) R -> c = e.
Proof. move=> H. by pinv H. Qed.

Lemma pinv_w_close n (c e : pch n) K R : ltswP c (PClose e K) R -> False.
Proof. move=> H. by pinv H. Qed.

Lemma pinv_f_close n (c d e : pch n) K R :
  ltsfP c d (PClose e K) R -> False.
Proof. move=> H. by pinv H. Qed.

Lemma pinv_f_wait n (c d e : pch n) K R :
  ltsfP c d (PWait e K) R -> False.
Proof. move=> H. by pinv H. Qed.

Lemma pinv_r_close n (c d e : pch n) K R :
  ltsrP c d (PClose e K) R -> False.
Proof. move=> H. by pinv H. Qed.

Lemma pinv_r_wait n (c d e : pch n) K R :
  ltsrP c d (PWait e K) R -> False.
Proof. move=> H. by pinv H. Qed.

Lemma pinv_b_close n (c e : pch n) r K (R : procP n.+1) :
  ltsbP c r (PClose e K) R -> False.
Proof. move=> H. by pinv H. Qed.

Lemma pinv_b_wait n (c e : pch n) r K (R : procP n.+1) :
  ltsbP c r (PWait e K) R -> False.
Proof. move=> H. by pinv H. Qed.

(** Weak parallel inversions: the action came from one side. *)
Lemma pinv_c_par n (c : pch n) A B R :
  ltscP c (PPar A B) R ->
  (exists R', ltscP c A R') \/ (exists R', ltscP c B R').
Proof. move=> H. pinv H; [left | right]; by eexists; eassumption. Qed.

Lemma pinv_w_par n (c : pch n) A B R :
  ltswP c (PPar A B) R ->
  (exists R', ltswP c A R') \/ (exists R', ltswP c B R').
Proof. move=> H. pinv H; [left | right]; by eexists; eassumption. Qed.

Lemma pinv_f_par n (c d : pch n) A B R :
  ltsfP c d (PPar A B) R ->
  (exists R', ltsfP c d A R') \/ (exists R', ltsfP c d B R').
Proof. move=> H. pinv H; [left | right]; by eexists; eassumption. Qed.

Lemma pinv_r_par n (c d : pch n) A B R :
  ltsrP c d (PPar A B) R ->
  (exists R', ltsrP c d A R') \/ (exists R', ltsrP c d B R').
Proof. move=> H. pinv H; [left | right]; by eexists; eassumption. Qed.

Lemma pinv_b_par n (c : pch n) r A B (R : procP n.+1) :
  ltsbP c r (PPar A B) R ->
  (exists R', ltsbP c r A R') \/ (exists R', ltsbP c r B R').
Proof. move=> H. pinv H; [left | right]; by eexists; eassumption. Qed.

(** Early input is uniform in the received NAME (the polarity is
    pinned by the prefix annotation): if a receive fires at one
    object, it fires at every name. *)
Lemma ltsrP_any_name n (c d : pch n) P R (H : ltsrP c d P R) :
  forall y' : ch n, exists R', ltsrP c (y', d.2) P R'.
Proof.
  elim: H => {n c d P R}.
  - move=> n c y r K y' /=. eexists. exact: PR_Pfx.
  - move=> n c d P P' Q _ IH y'.
    case: (IH y') => R' H'. eexists. exact: PR_ParL H'.
  - move=> n c d P Q Q' _ IH y'.
    case: (IH y') => R' H'. eexists. exact: PR_ParR H'.
  - move=> n c d P P' _ IH y'.
    case: (IH (shift y')) => R' H'. eexists. apply: PR_Res.
    exact: H'.
Qed.

(** Full grid: every family on every prefix shape.  [F] variants
    return the forced components; bare variants refute. *)

Lemma pinv_c_closeF n (c e : pch n) K R :
  ltscP c (PClose e K) R -> c = e /\ R = K.
Proof. move=> H. by pinv H. Qed.

Lemma pinv_w_waitF n (c e : pch n) K R :
  ltswP c (PWait e K) R -> c = e /\ R = K.
Proof. move=> H. by pinv H. Qed.

Lemma pinv_f_delF n (c d e p : pch n) K R :
  ltsfP c d (PDel e p K) R -> [/\ c = e, d = p & R = K].
Proof. move=> H. by pinv H. Qed.

Lemma pinv_r_insF n (c d e : pch n) (r : pol) (K : procP n.+1) R :
  ltsrP c d (PIns e r K) R ->
  [/\ c = e, d.2 = r & R = psubst (scons d.1 id_ren) K].
Proof. move=> H. by pinv H. Qed.

Lemma pinv_c_end n (c : pch n) R : ltscP c PEnd R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_w_end n (c : pch n) R : ltswP c PEnd R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_f_end n (c d : pch n) R : ltsfP c d PEnd R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_r_end n (c d : pch n) R : ltsrP c d PEnd R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_b_end n (c : pch n) r (R : procP n.+1) :
  ltsbP c r PEnd R -> False.
Proof. move=> H. by pinv H. Qed.

Lemma pinv_c_del n (c e p : pch n) K R : ltscP c (PDel e p K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_w_del n (c e p : pch n) K R : ltswP c (PDel e p K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_r_del n (c d e p : pch n) K R :
  ltsrP c d (PDel e p K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_b_del n (c e p : pch n) r K (R : procP n.+1) :
  ltsbP c r (PDel e p K) R -> False.
Proof. move=> H. by pinv H. Qed.

Lemma pinv_c_ins n (c e : pch n) r (K : procP n.+1) R :
  ltscP c (PIns e r K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_w_ins n (c e : pch n) r (K : procP n.+1) R :
  ltswP c (PIns e r K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_f_ins n (c d e : pch n) r (K : procP n.+1) R :
  ltsfP c d (PIns e r K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_b_ins n (c e : pch n) r r' (K : procP n.+1) (R : procP n.+1) :
  ltsbP c r (PIns e r' K) R -> False.
Proof. move=> H. by pinv H. Qed.

(** No prefix (nor ∅) performs an internal step. *)
Lemma pinv_t_end n (R : procP n) : ltstP PEnd R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_t_close n (c : pch n) K R : ltstP (PClose c K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_t_wait n (c : pch n) K R : ltstP (PWait c K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_t_del n (c d : pch n) K R : ltstP (PDel c d K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_t_ins n (c : pch n) r (K : procP n.+1) R :
  ltstP (PIns c r K) R -> False.
Proof. move=> H. by pinv H. Qed.

(** ** Sanity: the semantics in action *)
Section Examples.

(** Close meets wait under its ν: the canonical session end.
    [(ν)((0⁺)!․∅ ∥ (0⁻)?․∅) —τ→ (ν)(∅ ∥ ∅)] *)
Example run_close_wait :
  ltstP ((ν) (((zero, pos) !․ ∅) ∥ ((zero, neg) ?․ ∅)))
        ((ν) (∅ ∥ ∅) : procP 0).
Proof.
  apply: PT_Res.
  exact: PT_CW (PC_Pfx (zero, pos) ∅) (PW_Pfx (zero, neg) ∅).
Qed.

(** Communication at a FREE channel: no ν anywhere.  This is the
    rule the double-binder syntax could not even state. *)
Example run_free_comm (n : nat) (x : ch n) :
  ltstP (((x, pos) !․ ∅) ∥ ((x, neg) ?․ ∅)) (∅ ∥ ∅).
Proof. exact: PT_CW (PC_Pfx (x, pos) ∅) (PW_Pfx (x, neg) ∅). Qed.

(** Free delegation: send endpoint [(y, neg)] over [(x, pos)]; the
    receiver expects a [neg] endpoint and continues by waiting on it.
    The receiver's bound name gets instantiated to [y]. *)
Example run_free_deleg (n : nat) (x y : ch n) :
  ltstP (((x, pos) ! (y, neg) ․ ∅) ∥ ((x, neg) ?( neg )․ ((zero, neg) ?․ ∅)))
        (∅ ∥ ((y, neg) ?․ ∅)).
Proof.
  have H := PT_DR (PF_Pfx (x, pos) (y, neg) ∅)
                  (PR_Pfx (x, neg) y neg ((zero, neg) ?․ ∅)).
  by rewrite /= in H.
Qed.

(** Bound delegation (scope extrusion): the sender delegates the
    [pos] endpoint of its OWN restriction over free [(x, pos)]; the
    receiver is outside.  The restriction moves out to enclose both:

    [(ν)((sh x)⁺ ! (0⁺) ․ (0⁻)?․∅)  ∥  x⁻?(pos)․ (0⁺)!․∅
       —τ→  (ν)( (0⁻)?․∅ ∥ (0⁺)!․∅ )]

    Sender keeps the [neg] end, receiver got the [pos] end; they can
    then close the delegated session. *)
Example run_bound_deleg (n : nat) (x : ch n) :
  ltstP (((ν) ((pshift (x, pos)) ! (zero, pos) ․ ((zero, neg) ?․ ∅)))
           ∥ ((x, neg) ?( pos )․ ((zero, pos) !․ ∅)))
        ((ν) (((zero, neg) ?․ ∅) ∥ ((zero, pos) !․ ∅))).
Proof.
  have HB : ltsbP (x, pos) pos
              ((ν) ((pshift (x, pos)) ! (zero, pos) ․ ((zero, neg) ?․ ∅)))
              ((zero, neg) ?․ ∅).
    exact: PB_Open (PF_Pfx _ _ _).
  have HR : ltsrP (pshift (pflip (x, pos))) (zero, pos)
              (psubst shift ((x, neg) ?( pos )․ ((zero, pos) !․ ∅)))
              ((zero, pos) !․ ∅).
    exact (PR_Pfx (pshift (x, neg)) zero pos ((zero, pos) !․ ∅)).
  exact: PT_BR HB HR.
Qed.

(** Mismatch does NOT step: two closes on co-endpoints have no τ.
    (The error predicate will catch exactly these.) *)

Example no_step_close_close (x : ch 1) K1 K2 R :
  ~ ltstP (((x, pos) !․ K1) ∥ ((x, neg) !․ K2)) R.
Proof.
  move=> H. pinv H;
  repeat match goal with
  | [ HX : ltstP (PClose _ _) _ |- _ ] => by pinv HX
  | [ HX : ltswP _ (PClose _ _) _ |- _ ] => by pinv HX
  | [ HX : ltsfP _ _ (PClose _ _) _ |- _ ] => by pinv HX
  | [ HX : ltsrP _ _ (PClose _ _) _ |- _ ] => by pinv HX
  | [ HX : ltsbP _ _ (PClose _ _) _ |- _ ] => by pinv HX
  | [ HX : ltsselP _ _ (PClose _ _) _ |- _ ] => by pinv HX
  | [ HX : ltsbrP _ _ (PClose _ _) _ |- _ ] => by pinv HX
  | [ HX : ltscP _ (PClose _ _) _ |- _ ] => pinv HX
  end.
Qed.

End Examples.

(** ** Inversion grid: choice *)

(* determinations at the new prefixes *)
Lemma pinv_sel_selF n (c e : pch n) (b b' : bool) K R :
  ltsselP c b (e ◁ b' ․ K) R -> [/\ c = e, b = b' & R = K].
Proof. move=> H. by pinv H. Qed.

Lemma pinv_br_braF n (c e : pch n) (b : bool) K1 K2 R :
  ltsbrP c b (e ▷ ( K1 | K2 )) R ->
  c = e /\ R = (if b then K1 else K2).
Proof. move=> H. by pinv H. Qed.

(* old families at the new prefixes: nothing fires *)
Lemma pinv_c_sel n (c e : pch n) b K R :
  ltscP c (e ◁ b ․ K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_w_sel n (c e : pch n) b K R :
  ltswP c (e ◁ b ․ K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_f_sel n (c d e : pch n) b K R :
  ltsfP c d (e ◁ b ․ K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_r_sel n (c d e : pch n) b K R :
  ltsrP c d (e ◁ b ․ K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_b_sel n (c e : pch n) r b K (R : procP n.+1) :
  ltsbP c r (e ◁ b ․ K) R -> False.
Proof. move=> H. by pinv H. Qed.

Lemma pinv_c_bra n (c e : pch n) K1 K2 R :
  ltscP c (e ▷ ( K1 | K2 )) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_w_bra n (c e : pch n) K1 K2 R :
  ltswP c (e ▷ ( K1 | K2 )) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_f_bra n (c d e : pch n) K1 K2 R :
  ltsfP c d (e ▷ ( K1 | K2 )) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_r_bra n (c d e : pch n) K1 K2 R :
  ltsrP c d (e ▷ ( K1 | K2 )) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_b_bra n (c e : pch n) r K1 K2 (R : procP n.+1) :
  ltsbP c r (e ▷ ( K1 | K2 )) R -> False.
Proof. move=> H. by pinv H. Qed.

(* new families at the old prefixes: nothing fires *)
Lemma pinv_sel_end n (c : pch n) b R :
  ltsselP c b PEnd R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_sel_close n (c e : pch n) b K R :
  ltsselP c b (PClose e K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_sel_wait n (c e : pch n) b K R :
  ltsselP c b (PWait e K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_sel_del n (c e p : pch n) b K R :
  ltsselP c b (PDel e p K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_sel_ins n (c e : pch n) b r (K : procP n.+1) R :
  ltsselP c b (PIns e r K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_sel_bra n (c e : pch n) b K1 K2 R :
  ltsselP c b (e ▷ ( K1 | K2 )) R -> False.
Proof. move=> H. by pinv H. Qed.

Lemma pinv_br_end n (c : pch n) b R :
  ltsbrP c b PEnd R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_br_close n (c e : pch n) b K R :
  ltsbrP c b (PClose e K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_br_wait n (c e : pch n) b K R :
  ltsbrP c b (PWait e K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_br_del n (c e p : pch n) b K R :
  ltsbrP c b (PDel e p K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_br_ins n (c e : pch n) b r (K : procP n.+1) R :
  ltsbrP c b (PIns e r K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_br_sel n (c e : pch n) b b' K R :
  ltsbrP c b (e ◁ b' ․ K) R -> False.
Proof. move=> H. by pinv H. Qed.

(* τ at the new prefixes: nothing fires *)
Lemma pinv_t_sel n (c : pch n) b K R :
  ltstP (c ◁ b ․ K) R -> False.
Proof. move=> H. by pinv H. Qed.
Lemma pinv_t_bra n (c : pch n) K1 K2 R :
  ltstP (c ▷ ( K1 | K2 )) R -> False.
Proof. move=> H. by pinv H. Qed.

(* par existence splits *)
Lemma pinv_sel_par n (c : pch n) b A B R :
  ltsselP c b (PPar A B) R ->
  (exists R', ltsselP c b A R') \/ (exists R', ltsselP c b B R').
Proof. move=> H. pinv H; [left | right]; by eexists; eassumption. Qed.
Lemma pinv_br_par n (c : pch n) b A B R :
  ltsbrP c b (PPar A B) R ->
  (exists R', ltsbrP c b A R') \/ (exists R', ltsbrP c b B R').
Proof. move=> H. pinv H; [left | right]; by eexists; eassumption. Qed.
