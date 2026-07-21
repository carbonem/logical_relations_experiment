(** * Equivariance of the τ-calculus

    Internal steps and synchronisations are preserved by renaming
    (forward) and, for renamings injective on the relevant channels,
    reflected (backward).  All proofs are syntax-directed inductions;
    the visible-transition equivariance lemmas come from [LTS.v]
    (forward) and [Transfer.v] (backward).

    This is the machinery that makes the relation's renaming-closure
    lemma *provable* -- in the ≅-development it was an interface
    hypothesis. *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import synsem Errors LogRel Toolkit LTS Transfer Typing
  Fundamental Tau LogRelTau TauInv.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** Commutation of the communication substitutions with renaming *)

Lemma scons_up1 m n (s : ren m n) (z : ch m) (w : ch m.+1) :
  s (scons z id_ren w) = scons (s z) id_ren (up_ch s w).
Proof. by case: w. Qed.

Lemma open_recv_up m n (s : ren m n) (w : ch m.+1) :
  up_ch (up_ch s) (open_recv w) = open_recv (up_ch s w).
Proof. by case: w. Qed.

(** ** Forward equivariance of synchronisation *)

Lemma syncC_ren n (x y : ch n) (P R : proc n) (H : syncC x y P R) :
  forall m (s : ren n m),
    syncC (s x) (s y) (subst_proc s P) (subst_proc s R).
Proof.
  elim: H => {n x y P R}.
  - move=> n x y P P' Q Q' HC HW m s /=.
    exact: SYC_L (ltsc_ren HC s) (ltsw_ren HW s).
  - move=> n x y P P' Q Q' HW HC m s /=.
    exact: SYC_R (ltsw_ren HW s) (ltsc_ren HC s).
  - move=> n x y P R Q _ IH m s /=. exact: SYC_ParL (IH _ _).
  - move=> n x y P Q R _ IH m s /=. exact: SYC_ParR (IH _ _).
  - move=> n x y P R _ IH m s /=. apply: SYC_Res.
    by have := IH _ (up_ch (up_ch s)); rewrite !up2_shift2.
Qed.

Lemma syncD_ren n (x y : ch n) (P R : proc n) (H : syncD x y P R) :
  forall m (s : ren n m),
    syncD (s x) (s y) (subst_proc s P) (subst_proc s R).
Proof.
  elim: H => {n x y P R}.
  - move=> n x y z P P' Q Q' HF HR m s /=.
    have -> : subst_proc s (subst_proc (scons z id_ren) Q')
            = subst_proc (scons (s z) id_ren) (subst_proc (up_ch s) Q').
      rewrite !subst_proc_comp. apply: subst_eqP => w.
      exact: scons_up1.
    exact: SYD_L (ltsf_ren HF s) (ltsr_ren HR s).
  - move=> n x y z P P' Q Q' HR HF m s /=.
    have -> : subst_proc s (subst_proc (scons z id_ren) P')
            = subst_proc (scons (s z) id_ren) (subst_proc (up_ch s) P').
      rewrite !subst_proc_comp. apply: subst_eqP => w.
      exact: scons_up1.
    exact: SYD_R (ltsr_ren HR s) (ltsf_ren HF s).
  - move=> n x y P R Q _ IH m s /=. exact: SYD_ParL (IH _ _).
  - move=> n x y P Q R _ IH m s /=. exact: SYD_ParR (IH _ _).
  - move=> n x y P R _ IH m s /=. apply: SYD_Res.
    by have := IH _ (up_ch (up_ch s)); rewrite !up2_shift2.
Qed.

Lemma syncB_ren n (x y : ch n) (P R : proc n) (H : syncB x y P R) :
  forall m (s : ren n m),
    syncB (s x) (s y) (subst_proc s P) (subst_proc s R).
Proof.
  elim: H => {n x y P R}.
  - move=> n x y P P' Q Q' HB HR m s /=.
    have -> : subst_proc (up_ch (up_ch s)) (subst_proc open_recv Q')
            = subst_proc open_recv (subst_proc (up_ch s) Q').
      rewrite !subst_proc_comp. apply: subst_eqP => w.
      exact: open_recv_up.
    exact: SYB_L (ltsb_ren HB s) (ltsr_ren HR s).
  - move=> n x y P P' Q Q' HR HB m s /=.
    have -> : subst_proc (up_ch (up_ch s)) (subst_proc open_recv P')
            = subst_proc open_recv (subst_proc (up_ch s) P').
      rewrite !subst_proc_comp. apply: subst_eqP => w.
      exact: open_recv_up.
    exact: SYB_R (ltsr_ren HR s) (ltsb_ren HB s).
  - move=> n x y P R Q _ IH m s /=. exact: SYB_ParL (IH _ _).
  - move=> n x y P Q R _ IH m s /=. exact: SYB_ParR (IH _ _).
  - move=> n x y P R _ IH m s /=. apply: SYB_Res.
    by have := IH _ (up_ch (up_ch s)); rewrite !up2_shift2.
Qed.

(** ** Forward equivariance of internal steps *)
Lemma ltst_ren n (P R : proc n) (H : ltst P R) :
  forall m (s : ren n m), ltst (subst_proc s P) (subst_proc s R).
Proof.
  elim: H => {n P R}.
  - move=> n P P' Q _ IH m s /=. exact: LT_ParL (IH _ _).
  - move=> n P Q Q' _ IH m s /=. exact: LT_ParR (IH _ _).
  - move=> n P P' _ IH m s /=. exact: LT_Res (IH _ _).
  - move=> n P R HS m s /=. apply: LT_CommC1.
    by have := syncC_ren HS (up_ch (up_ch s)).
  - move=> n P R HS m s /=. apply: LT_CommC2.
    by have := syncC_ren HS (up_ch (up_ch s)).
  - move=> n P R HS m s /=. apply: LT_CommD1.
    by have := syncD_ren HS (up_ch (up_ch s)).
  - move=> n P R HS m s /=. apply: LT_CommD2.
    by have := syncD_ren HS (up_ch (up_ch s)).
  - move=> n P R HS m s /=. apply: LT_CommB1.
    by have := syncB_ren HS (up_ch (up_ch s)).
  - move=> n P R HS m s /=. apply: LT_CommB2.
    by have := syncB_ren HS (up_ch (up_ch s)).
Qed.

Print Assumptions ltst_ren.

(** ** Backward equivariance (injective renamings)

    A synchronisation or internal step of a renamed process comes from
    one of the original.  The visible-transition backward lemmas are
    [Transfer.v]'s [lts*_ren_inv]; the payload of a delegation uses the
    existential form [ltsf_ren_inv2]. *)

Lemma syncC_ren_inv n' (x y : ch n') Q R (H : syncC x y Q R) :
  forall m (s : ren m n') (x0 y0 : ch m) P,
    ren_inj s -> s x0 = x -> s y0 = y -> subst_proc s P = Q ->
    exists R0, R = subst_proc s R0 /\ syncC x0 y0 P R0.
Proof.
  elim: H => {n' x y Q R}.
  - move=> n' x y A A' B B' HC HW m s x0 y0 P Hinj Ex Ey EP.
    case: (subst_inv_par EP) => A0 [B0 [E1 E2 E3]]. subst.
    case: (ltsc_ren_inv HC Hinj erefl erefl) => A0' [-> HA].
    case: (ltsw_ren_inv HW Hinj erefl erefl) => B0' [-> HB].
    exists (A0' ∥ B0'). split=> //=. exact: SYC_L HA HB.
  - move=> n' x y A A' B B' HW HC m s x0 y0 P Hinj Ex Ey EP.
    case: (subst_inv_par EP) => A0 [B0 [E1 E2 E3]]. subst.
    case: (ltsw_ren_inv HW Hinj erefl erefl) => A0' [-> HA].
    case: (ltsc_ren_inv HC Hinj erefl erefl) => B0' [-> HB].
    exists (A0' ∥ B0'). split=> //=. exact: SYC_R HA HB.
  - move=> n' x y A R B _ IH m s x0 y0 P Hinj Ex Ey EP.
    case: (subst_inv_par EP) => A0 [B0 [E1 E2 E3]]. subst.
    case: (IH _ _ _ _ _ Hinj erefl erefl erefl) => R0 [-> HR].
    exists (R0 ∥ B0). split=> //=. exact: SYC_ParL HR.
  - move=> n' x y A B R _ IH m s x0 y0 P Hinj Ex Ey EP.
    case: (subst_inv_par EP) => A0 [B0 [E1 E2 E3]]. subst.
    case: (IH _ _ _ _ _ Hinj erefl erefl erefl) => R0 [-> HR].
    exists (A0 ∥ R0). split=> //=. exact: SYC_ParR HR.
  - move=> n' x y A R _ IH m s x0 y0 P Hinj Ex Ey EP.
    case: (subst_inv_res EP) => A0 [E1 E2]. subst.
    case: (IH _ _ _ _ _ (up_inj (up_inj Hinj))
             (up2_shift2 s x0) (up2_shift2 s y0) erefl) => R0 [-> HR].
    exists ((ν) R0). split=> //=. exact: SYC_Res HR.
Qed.

Lemma syncD_ren_inv n' (x y : ch n') Q R (H : syncD x y Q R) :
  forall m (s : ren m n') (x0 y0 : ch m) P,
    ren_inj s -> s x0 = x -> s y0 = y -> subst_proc s P = Q ->
    exists R0, R = subst_proc s R0 /\ syncD x0 y0 P R0.
Proof.
  elim: H => {n' x y Q R}.
  - move=> n' x y z A A' B B' HF HR m s x0 y0 P Hinj Ex Ey EP.
    case: (subst_inv_par EP) => A0 [B0 [E1 E2 E3]]. subst.
    case: (ltsf_ren_inv2 HF Hinj erefl) => x1 [z1 [A0' [Ex1 Ez1 -> HA]]].
    have Exx : x1 = x0 by apply: Hinj; rewrite Ex1.
    subst x1 z.
    case: (ltsr_ren_inv HR Hinj erefl erefl) => B0' [-> HB].
    exists (A0' ∥ subst_proc (scons z1 id_ren) B0'). split.
      rewrite /= !subst_proc_comp. congr (_ ∥ _).
      apply: subst_eqP => w. by rewrite /= scons_up1.
    exact: SYD_L HA HB.
  - move=> n' x y z A A' B B' HR HF m s x0 y0 P Hinj Ex Ey EP.
    case: (subst_inv_par EP) => A0 [B0 [E1 E2 E3]]. subst.
    case: (ltsf_ren_inv2 HF Hinj erefl) => x1 [z1 [B0' [Ex1 Ez1 -> HB]]].
    have Exx : x1 = x0 by apply: Hinj; rewrite Ex1.
    subst x1 z.
    case: (ltsr_ren_inv HR Hinj erefl erefl) => A0' [-> HA].
    exists (subst_proc (scons z1 id_ren) A0' ∥ B0'). split.
      rewrite /= !subst_proc_comp. congr (_ ∥ _).
      apply: subst_eqP => w. by rewrite /= scons_up1.
    exact: SYD_R HA HB.
  - move=> n' x y A R B _ IH m s x0 y0 P Hinj Ex Ey EP.
    case: (subst_inv_par EP) => A0 [B0 [E1 E2 E3]]. subst.
    case: (IH _ _ _ _ _ Hinj erefl erefl erefl) => R0 [-> HR].
    exists (R0 ∥ B0). split=> //=. exact: SYD_ParL HR.
  - move=> n' x y A B R _ IH m s x0 y0 P Hinj Ex Ey EP.
    case: (subst_inv_par EP) => A0 [B0 [E1 E2 E3]]. subst.
    case: (IH _ _ _ _ _ Hinj erefl erefl erefl) => R0 [-> HR].
    exists (A0 ∥ R0). split=> //=. exact: SYD_ParR HR.
  - move=> n' x y A R _ IH m s x0 y0 P Hinj Ex Ey EP.
    case: (subst_inv_res EP) => A0 [E1 E2]. subst.
    case: (IH _ _ _ _ _ (up_inj (up_inj Hinj))
             (up2_shift2 s x0) (up2_shift2 s y0) erefl) => R0 [-> HR].
    exists ((ν) R0). split=> //=. exact: SYD_Res HR.
Qed.

Lemma syncB_ren_inv n' (x y : ch n') Q R (H : syncB x y Q R) :
  forall m (s : ren m n') (x0 y0 : ch m) P,
    ren_inj s -> s x0 = x -> s y0 = y -> subst_proc s P = Q ->
    exists R0, R = subst_proc s R0 /\ syncB x0 y0 P R0.
Proof.
  elim: H => {n' x y Q R}.
  - move=> n' x y A A' B B' HB HR m s x0 y0 P Hinj Ex Ey EP.
    case: (subst_inv_par EP) => A0 [B0 [E1 E2 E3]]. subst.
    case: (ltsb_ren_inv HB Hinj erefl erefl) => A0' [-> HA].
    case: (ltsr_ren_inv HR Hinj erefl erefl) => B0' [-> HB'].
    exists ((ν) (A0' ∥ subst_proc open_recv B0')). split.
      rewrite /= !subst_proc_comp. congr ResP. congr (_ ∥ _).
      apply: subst_eqP => w. by rewrite /= open_recv_up.
    exact: SYB_L HA HB'.
  - move=> n' x y A A' B B' HR HB m s x0 y0 P Hinj Ex Ey EP.
    case: (subst_inv_par EP) => A0 [B0 [E1 E2 E3]]. subst.
    case: (ltsr_ren_inv HR Hinj erefl erefl) => A0' [-> HA].
    case: (ltsb_ren_inv HB Hinj erefl erefl) => B0' [-> HB'].
    exists ((ν) (subst_proc open_recv A0' ∥ B0')). split.
      rewrite /= !subst_proc_comp. congr ResP. congr (_ ∥ _).
      apply: subst_eqP => w. by rewrite /= open_recv_up.
    exact: SYB_R HA HB'.
  - move=> n' x y A R B _ IH m s x0 y0 P Hinj Ex Ey EP.
    case: (subst_inv_par EP) => A0 [B0 [E1 E2 E3]]. subst.
    case: (IH _ _ _ _ _ Hinj erefl erefl erefl) => R0 [-> HR].
    exists (R0 ∥ B0). split=> //=. exact: SYB_ParL HR.
  - move=> n' x y A B R _ IH m s x0 y0 P Hinj Ex Ey EP.
    case: (subst_inv_par EP) => A0 [B0 [E1 E2 E3]]. subst.
    case: (IH _ _ _ _ _ Hinj erefl erefl erefl) => R0 [-> HR].
    exists (A0 ∥ R0). split=> //=. exact: SYB_ParR HR.
  - move=> n' x y A R _ IH m s x0 y0 P Hinj Ex Ey EP.
    case: (subst_inv_res EP) => A0 [E1 E2]. subst.
    case: (IH _ _ _ _ _ (up_inj (up_inj Hinj))
             (up2_shift2 s x0) (up2_shift2 s y0) erefl) => R0 [-> HR].
    exists ((ν) R0). split=> //=. exact: SYB_Res HR.
Qed.

Lemma ltst_ren_inv n' (Q R : proc n') (H : ltst Q R) :
  forall m (s : ren m n') P,
    ren_inj s -> subst_proc s P = Q ->
    exists R0, R = subst_proc s R0 /\ ltst P R0.
Proof.
  elim: H => {n' Q R}.
  - move=> n' A A' B _ IH m s P Hinj EP.
    case: (subst_inv_par EP) => A0 [B0 [E1 E2 E3]]. subst.
    case: (IH _ _ _ Hinj erefl) => R0 [-> HR].
    exists (R0 ∥ B0). split=> //=. exact: LT_ParL HR.
  - move=> n' A B B' _ IH m s P Hinj EP.
    case: (subst_inv_par EP) => A0 [B0 [E1 E2 E3]]. subst.
    case: (IH _ _ _ Hinj erefl) => R0 [-> HR].
    exists (A0 ∥ R0). split=> //=. exact: LT_ParR HR.
  - move=> n' A A' _ IH m s P Hinj EP.
    case: (subst_inv_res EP) => A0 [E1 E2]. subst.
    case: (IH _ _ _ (up_inj (up_inj Hinj)) erefl) => R0 [-> HR].
    exists ((ν) R0). split=> //=. exact: LT_Res HR.
  - move=> n' A R HS m s P Hinj EP.
    case: (subst_inv_res EP) => A0 [E1 E2]. subst.
    case: (syncC_ren_inv HS (up_inj (up_inj Hinj))
             (@up2_one _ _ s) (@up2_zero _ _ s) erefl) => R0 [-> HR].
    exists ((ν) R0). split=> //=. exact: LT_CommC1 HR.
  - move=> n' A R HS m s P Hinj EP.
    case: (subst_inv_res EP) => A0 [E1 E2]. subst.
    case: (syncC_ren_inv HS (up_inj (up_inj Hinj))
             (@up2_zero _ _ s) (@up2_one _ _ s) erefl) => R0 [-> HR].
    exists ((ν) R0). split=> //=. exact: LT_CommC2 HR.
  - move=> n' A R HS m s P Hinj EP.
    case: (subst_inv_res EP) => A0 [E1 E2]. subst.
    case: (syncD_ren_inv HS (up_inj (up_inj Hinj))
             (@up2_one _ _ s) (@up2_zero _ _ s) erefl) => R0 [-> HR].
    exists ((ν) R0). split=> //=. exact: LT_CommD1 HR.
  - move=> n' A R HS m s P Hinj EP.
    case: (subst_inv_res EP) => A0 [E1 E2]. subst.
    case: (syncD_ren_inv HS (up_inj (up_inj Hinj))
             (@up2_zero _ _ s) (@up2_one _ _ s) erefl) => R0 [-> HR].
    exists ((ν) R0). split=> //=. exact: LT_CommD2 HR.
  - move=> n' A R HS m s P Hinj EP.
    case: (subst_inv_res EP) => A0 [E1 E2]. subst.
    case: (syncB_ren_inv HS (up_inj (up_inj Hinj))
             (@up2_one _ _ s) (@up2_zero _ _ s) erefl) => R0 [-> HR].
    exists ((ν) R0). split=> //=. exact: LT_CommB1 HR.
  - move=> n' A R HS m s P Hinj EP.
    case: (subst_inv_res EP) => A0 [E1 E2]. subst.
    case: (syncB_ren_inv HS (up_inj (up_inj Hinj))
             (@up2_zero _ _ s) (@up2_one _ _ s) erefl) => R0 [-> HR].
    exists ((ν) R0). split=> //=. exact: LT_CommB2 HR.
Qed.

Lemma ltsts_ren_inv n' (Q R : proc n') (H : Q —τ*→ R) :
  forall m (s : ren m n') P,
    ren_inj s -> subst_proc s P = Q ->
    exists R0, R = subst_proc s R0 /\ P —τ*→ R0.
Proof.
  elim: H => {n' Q R} [n0 X|n0 X Y R Hst _ IH] m s P Hinj EP; subst.
  - exists P. by split; last exact: TS_refl.
  - case: (ltst_ren_inv Hst Hinj erefl) => Y0 [EY HY].
    case: (IH _ _ _ Hinj (esym EY)) => R0 [-> HR].
    exists R0. split=> //. exact: TS_step HY HR.
Qed.

Print Assumptions ltsts_ren_inv.

(** ** Searching the finite channel space, and context pushforward

    [ch m] has [m] inhabitants; a decidable search over them makes the
    pushforward of a context along a renaming computable, which the
    renaming closure of the relation needs for its parallel-descent
    clause. *)
Fixpoint find_ch (m : nat) : (ch m -> bool) -> option (ch m) :=
  match m as m0 return (ch m0 -> bool) -> option (ch m0) with
  | 0 => fun _ => None
  | m'.+1 => fun p =>
      if p None then Some None
      else omap Some (find_ch (fun z => p (Some z)))
  end.

Lemma find_ch_complete m (p : ch m -> bool) z :
  p z -> exists z', find_ch p = Some z'.
Proof.
  elim: m p z => [//|m IH] p [w|] /= Hp.
  - case E: (p None); first by exists None.
    case: (IH (fun z => p (Some z)) w Hp) => z' ->.
    by exists (Some z').
  - by exists None; rewrite Hp.
Qed.

Lemma find_ch_sound m (p : ch m -> bool) z' :
  find_ch p = Some z' -> p z'.
Proof.
  elim: m p z' => [//|m IH] p z' /=.
  case E: (p None).
  - move=> [Ez]. by rewrite -Ez E.
  - case F: (find_ch (fun z => p (Some z))) => [w|] //= [Ez].
    rewrite -Ez. exact: IH F.
Qed.

Definition pfwd m n (s : ren m n) (Δm : sctx m) : sctx n :=
  fun w =>
    if find_ch (fun z => (s z == w) && isSome (Δm z)) is Some z
    then Δm z else None.

Lemma pfwd_agree m n (s : ren m n) (Δm : sctx m) :
  (forall z1 z2, Δm z1 <> None -> Δm z2 <> None -> s z1 = s z2 -> z1 = z2) ->
  forall z, Δm z = None \/ pfwd s Δm (s z) = Δm z.
Proof.
  move=> Hinj z.
  case E : (Δm z) => [S|]; last by left.
  right. rewrite /pfwd.
  have Hp : (s z == s z) && isSome (Δm z) by rewrite eqxx E.
  case: (@find_ch_complete _ (fun z0 => (s z0 == s z) && isSome (Δm z0)) _ Hp) => z1 F. rewrite F.
  move: (find_ch_sound F) => /andP[/eqP Es Ho].
  have Ez : z1 = z.
    apply: Hinj => //.
    by move=> E1; rewrite E1 in Ho.
    by rewrite E.
  by rewrite Ez E.
Qed.

(** ** Existential backward equivariance: subjects pull back too *)

(** Free-send backward, hypothesis-free ([Transfer.v]'s existential form
    never used its injectivity assumption). *)
Lemma ltsf_ren_inv3 n' (y z : ch n') Q R (H : ltsf y z Q R) :
  forall m (s : ren m n') P,
    subst_proc s P = Q ->
    exists x w P',
      [/\ y = s x, z = s w, R = subst_proc s P' & ltsf x w P P'].
Proof.
  elim: H => {n' y z Q R}.
  - move=> n' y z K m s P EP.
    case: (subst_inv_del EP) => x0 [w0 [K0 [E1 E2 E3 E4]]]. subst.
    exists x0, w0, K0. split=> //. exact: LF_Pfx.
  - move=> n' y z P1 P1' Q1 _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => x0 [w0 [Pa' [E1 E2 -> Ha]]].
    exists x0, w0, (Pa' ∥ Pb). split=> //=. exact: LF_ParL Ha.
  - move=> n' y z P1 Q1 Q1' _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => x0 [w0 [Pb' [E1 E2 -> Hb]]].
    exists x0, w0, (Pa ∥ Pb'). split=> //=. exact: LF_ParR Hb.
  - move=> n' y z P1 P1' _ IH m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (IH _ _ _ erefl) => x0 [w0 [P0' [E1 E2 -> H0]]].
    case: (up2_image_shift2 (esym E1)) => x1 [Ex1 Ex2].
    case: (up2_image_shift2 (esym E2)) => w1 [Ew1 Ew2].
    subst. exists x1, w1, ((ν) P0'). split=> //=. exact: LF_Res H0.
Qed.

Lemma ltsc_ren_inv2 n' (y : ch n') Q R (H : ltsc y Q R) :
  forall m (s : ren m n') P,
    subst_proc s P = Q ->
    exists x0 P', [/\ y = s x0, R = subst_proc s P' & ltsc x0 P P'].
Proof.
  elim: H => {n' y Q R}.
  - move=> n' y K m s P EP.
    case: (subst_inv_close EP) => x0 [K0 [E1 E2 E3]]. subst.
    exists x0, K0. split=> //. exact: LC_Pfx.
  - move=> n' y P1 P1' Q1 _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => x0 [Pa' [E1 -> HA]].
    exists x0, (Pa' ∥ Pb). split=> //=. exact: LC_ParL HA.
  - move=> n' y P1 Q1 Q1' _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => x0 [Pb' [E1 -> HB]].
    exists x0, (Pa ∥ Pb'). split=> //=. exact: LC_ParR HB.
  - move=> n' y P1 P1' _ IH m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (IH _ _ _ erefl) => x0 [P0' [E1 -> H0]].
    case: (up2_image_shift2 (esym E1)) => x1 [Ex1 Ex2]. subst.
    exists x1, ((ν) P0'). split=> //=. exact: LC_Res H0.
Qed.

Lemma ltsw_ren_inv2 n' (y : ch n') Q R (H : ltsw y Q R) :
  forall m (s : ren m n') P,
    subst_proc s P = Q ->
    exists x0 P', [/\ y = s x0, R = subst_proc s P' & ltsw x0 P P'].
Proof.
  elim: H => {n' y Q R}.
  - move=> n' y K m s P EP.
    case: (subst_inv_wait EP) => x0 [K0 [E1 E2 E3]]. subst.
    exists x0, K0. split=> //. exact: LW_Pfx.
  - move=> n' y P1 P1' Q1 _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => x0 [Pa' [E1 -> HA]].
    exists x0, (Pa' ∥ Pb). split=> //=. exact: LW_ParL HA.
  - move=> n' y P1 Q1 Q1' _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => x0 [Pb' [E1 -> HB]].
    exists x0, (Pa ∥ Pb'). split=> //=. exact: LW_ParR HB.
  - move=> n' y P1 P1' _ IH m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (IH _ _ _ erefl) => x0 [P0' [E1 -> H0]].
    case: (up2_image_shift2 (esym E1)) => x1 [Ex1 Ex2]. subst.
    exists x1, ((ν) P0'). split=> //=. exact: LW_Res H0.
Qed.

Lemma ltsr_ren_inv2 n' (y : ch n') Q (R : proc n'.+1) (H : ltsr y Q R) :
  forall m (s : ren m n') P,
    subst_proc s P = Q ->
    exists x0 P',
      [/\ y = s x0, R = subst_proc (up_ch s) P' & ltsr x0 P P'].
Proof.
  elim: H => {n' y Q R}.
  - move=> n' y K m s P EP.
    case: (subst_inv_ins EP) => x0 [K0 [E1 E2 E3]]. subst.
    exists x0, K0. split=> //. exact: LR_Pfx.
  - move=> n' y P1 P1' Q1 _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => x0 [Pa' [E1 -> HA]].
    exists x0, (Pa' ∥ subst_proc shift Pb). split=> //; last exact: LR_ParL HA.
    by rewrite /= !subst_proc_comp; congr (_ ∥ _);
       apply: subst_eqP => -[w|].
  - move=> n' y P1 Q1 Q1' _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => x0 [Pb' [E1 -> HB]].
    exists x0, (subst_proc shift Pa ∥ Pb'). split=> //; last exact: LR_ParR HB.
    by rewrite /= !subst_proc_comp; congr (_ ∥ _);
       apply: subst_eqP => -[w|].
  - move=> n' y P1 P1' _ IH m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (IH _ _ _ erefl) => x0 [P0' [E1 -> H0]].
    case: (up2_image_shift2 (esym E1)) => x1 [Ex1 Ex2]. subst.
    exists x1, ((ν) (subst_proc rho3 P0')). split=> //; last exact: LR_Res H0.
    by rewrite /= !subst_proc_comp; congr ResP;
       apply: subst_eqP => -[[[w|]|]|].
Qed.

Lemma ltsb_ren_inv2 n' (y : ch n') Q (R : proc n'.+2) (H : ltsb y Q R) :
  forall m (s : ren m n') P,
    subst_proc s P = Q ->
    exists x0 P',
      [/\ y = s x0, R = subst_proc (up_ch (up_ch s)) P' & ltsb x0 P P'].
Proof.
  elim: H => {n' y Q R}.
  - move=> n' y P1 P1' Hf m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (ltsf_ren_inv3 Hf erefl)
      => x0 [w0 [P0' [E1 E2 -> Hff]]].
    case: (up2_image_shift2 (esym E1)) => x1 [Ex1 Ex2].
    have Ew : w0 = zero by apply: up2_image_zero (esym E2).
    subst. exists x1, P0'. split=> //. exact: LB_Open0.
  - move=> n' y P1 P1' Hf m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (ltsf_ren_inv3 Hf erefl)
      => x0 [w0 [P0' [E1 E2 -> Hff]]].
    case: (up2_image_shift2 (esym E1)) => x1 [Ex1 Ex2].
    have Ew : w0 = one by apply: up2_image_one (esym E2).
    subst. exists x1, (subst_proc (swap_ch zero one) P0').
    split=> //; last exact: LB_Open1.
    by rewrite !subst_proc_comp; apply: subst_eqP => z;
       rewrite /= swap01_up2.
  - move=> n' y P1 P1' Q1 _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => x0 [Pa' [E1 -> HA]].
    exists x0, (Pa' ∥ subst_proc (shift \o shift) Pb).
    split=> //; last exact: LB_ParL HA.
    by rewrite /= !subst_proc_comp; congr (_ ∥ _);
       apply: subst_eqP => -[w|].
  - move=> n' y P1 Q1 Q1' _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => x0 [Pb' [E1 -> HB]].
    exists x0, (subst_proc (shift \o shift) Pa ∥ Pb').
    split=> //; last exact: LB_ParR HB.
    by rewrite /= !subst_proc_comp; congr (_ ∥ _);
       apply: subst_eqP => -[w|].
  - move=> n' y P1 P1' _ IH m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (IH _ _ _ erefl) => x0 [P0' [E1 -> H0]].
    case: (up2_image_shift2 (esym E1)) => x1 [Ex1 Ex2]. subst.
    exists x1, ((ν) (subst_proc (swap_ch one three)
                       (subst_proc (swap_ch zero two) P0'))).
    split=> //; last exact: LB_Res H0.
    by rewrite /= !subst_proc_comp; congr ResP;
       apply: subst_eqP => -[[[[w|]|]|]|].
Qed.

(** Offers pull back along any renaming. *)
Lemma offers_ren_inv m n (s : ren m n) a (w : ch n) (P : proc m) :
  offers a w (subst_proc s P) ->
  exists x0, w = s x0 /\ offers a x0 P.
Proof.
  case: a => /=.
  - move=> [P'' HT]. case: (ltsc_ren_inv2 HT erefl) => x0 [P' [E1 _ H0]].
    exists x0. split=> //. by exists P'.
  - move=> [P'' HT]. case: (ltsw_ren_inv2 HT erefl) => x0 [P' [E1 _ H0]].
    exists x0. split=> //. by exists P'.
  - move=> [[z [P'' HT]]|[P'' HT]].
    + case: (ltsf_ren_inv3 HT erefl)
        => x0 [w0 [P' [E1 E2 _ H0]]].
      exists x0. split=> //. left. by exists w0, P'.
    + case: (ltsb_ren_inv2 HT erefl) => x0 [P' [E1 _ H0]].
      exists x0. split=> //. right. by exists P'.
  - move=> [P'' HT]. case: (ltsr_ren_inv2 HT erefl) => x0 [P' [E1 _ H0]].
    exists x0. split=> //. by exists P'.
Qed.

Print Assumptions offers_ren_inv.
