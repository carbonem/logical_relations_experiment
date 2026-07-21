(** * The attic: true, proved, and unused

    Every lemma below was proved on the live line and is no longer
    reachable from [error_free_typedP].  They are kept because each records
    a design decision, not because anything needs them:

    - the FORWARD equivariance stack ([lts*P_ren], [pren_flip],
      [pren_inj]).  The fundamental theorem is stated in
      substitution form, so it consumes renaming BACKWARDS
      ([lts*P_ren_inv], which stay live); the forward direction is
      the sanity property "the LTS is equivariant" and is used
      nowhere.  Two forward lemmas did survive on the live line
      ([ltsfP_ren] is unused too but [ltsrP_ren] is needed by
      [compat_resP]'s binder-tunnelling step).
    - [ltstP_ren_inv]: backward τ-inversion under FULL injectivity,
      superseded by [PolSem.ltstP_ren_inv_cov], whose coverage guard
      is what the substitution lemma can actually supply (a collapse
      [scons y id] is never injective).
    - [compat_closeP], [compat_waitP], [compat_delP]: the closed-world
      compatibility lemmas, superseded by the σ-parametric
      [fcompat_close], [fcompat_wait], [fcompat_del] of [PolFN.v],
      which must additionally handle a MERGED subject.  [compat_endP]
      is not here: it survived, [fcompat_end] still calls it.
    - the [error_freeP] and [pcupd] APIs, and assorted scaffolding
      ([sle_econsume], [spush_both_inv], [srecv_neqT], ...) built
      while a design was being searched for and abandoned when the
      design changed.

    To check this file: copy it into the parent directory (the live
    development) and run

        coqc -R . Tait PolAttic.v

    It is not part of [_CoqProject]; nothing on the live path may
    ever depend on it. *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import PolBase PolTypes PolProc PolLTS PolErr PolTyping
  PolLogRel PolEquiv PolCompat PolSem PolComb PolFN.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope pol_scope.

(** ** Polarities and endpoints *)

Lemma pol_eqP : Equality.axiom pol_eqb.
Proof. by case=> [] []; constructor. Qed.

Lemma pflip_invol n (c : pch n) : pflip (pflip c) = c.
Proof. case: c => x r. by rewrite /pflip /= flipp_invol. Qed.

Lemma pren_flip m n (s : ren m n) (c : pch m) :
  pren s (pflip c) = pflip (pren s c).
Proof. by case: c. Qed.

Lemma pren_inj m n (s : ren m n) :
  (forall z1 z2, s z1 = s z2 -> z1 = z2) ->
  forall c d : pch m, pren s c = pren s d -> c = d.
Proof.
  move=> Hinj [c1 c2] [d1 d2] /= [E1 E2].
  by rewrite (Hinj _ _ E1) E2.
Qed.

(** ** Actions and protocols *)

Lemma compat_sym a b : compat a b = compat b a.
Proof. by case: a; case: b. Qed.

(** Dual protocols prescribe compatible actions. *)
Lemma compat_dual S :
  compat (head_act S) (head_act (dual S)).
Proof. by case: S. Qed.

(** ** The τ* closure *)

Lemma ltstsP1 n (P Q : procP n) : ltstP P Q -> P —τ*→ Q.
Proof. move=> H. exact: PTS_step H (PTS_refl _). Qed.

Lemma ltstsP_trans n (P Q R : procP n) :
  P —τ*→ Q -> Q —τ*→ R -> P —τ*→ R.
Proof.
  move=> H; elim: H R => [//|n' X Y Z Hst _ IH] R HQR.
  exact: PTS_step Hst (IH _ HQR).
Qed.

(** ** The safety API *)

Lemma error_freeP_nerr n (P : procP n) : error_freeP P -> ~ errP P.
Proof. move=> H. exact: H (PTS_refl _). Qed.

Lemma error_freeP_step n (P Q : procP n) : error_freeP P -> ltstP P Q -> error_freeP Q.
Proof.
  move=> HS Hst R HQR. apply: HS. exact: PTS_step Hst HQR.
Qed.

Lemma error_freeP_ltsts n (P Q : procP n) : error_freeP P -> P —τ*→ Q -> error_freeP Q.
Proof.
  move=> HS Hred R HQR. apply: HS. exact: ltstsP_trans Hred HQR.
Qed.

(** ** Typing-context updates *)

Lemma pcupd_eq n (x : ch n) e (Δ : pctx n) : pcupd x e Δ x = e.
Proof. by rewrite /pcupd eqxx. Qed.

Lemma pcupd_neq n (x y : ch n) e (Δ : pctx n) :
  y != x -> pcupd x e Δ y = Δ y.
Proof. rewrite /pcupd. by case: eqP. Qed.

(** ** Forward equivariance *)

Lemma pren_up_zero m n (s : ren m n) (r : pol) :
  pren (up_ch s) ((zero, r) : pch m.+1) = (zero, r).
Proof. by []. Qed.

Lemma ltsfP_ren n (c d : pch n) P P' (H : ltsfP c d P P') :
  forall m (s : ren n m),
    ltsfP (pren s c) (pren s d) (psubst s P) (psubst s P').
Proof.
  elim: H => {n c d P P'}.
  - move=> n c d K m s /=. exact: PF_Pfx.
  - move=> n c d P P' Q _ IH m s /=. exact: PF_ParL (IH _ _).
  - move=> n c d P Q Q' _ IH m s /=. exact: PF_ParR (IH _ _).
  - move=> n c d P P' _ IH m s /=.
    apply: PF_Res. rewrite -!pren_up_pshift. exact: IH.
Qed.

Lemma ltscP_ren n (c : pch n) P P' (H : ltscP c P P') :
  forall m (s : ren n m),
    ltscP (pren s c) (psubst s P) (psubst s P').
Proof.
  elim: H => {n c P P'}.
  - move=> n c K m s /=. exact: PC_Pfx.
  - move=> n c P P' Q _ IH m s /=. exact: PC_ParL (IH _ _).
  - move=> n c P Q Q' _ IH m s /=. exact: PC_ParR (IH _ _).
  - move=> n c P P' _ IH m s /=.
    apply: PC_Res. rewrite -pren_up_pshift. exact: IH.
Qed.

Lemma ltswP_ren n (c : pch n) P P' (H : ltswP c P P') :
  forall m (s : ren n m),
    ltswP (pren s c) (psubst s P) (psubst s P').
Proof.
  elim: H => {n c P P'}.
  - move=> n c K m s /=. exact: PW_Pfx.
  - move=> n c P P' Q _ IH m s /=. exact: PW_ParL (IH _ _).
  - move=> n c P Q Q' _ IH m s /=. exact: PW_ParR (IH _ _).
  - move=> n c P P' _ IH m s /=.
    apply: PW_Res. rewrite -pren_up_pshift. exact: IH.
Qed.

Lemma ltsbP_ren n (c : pch n) (r : pol) P (P' : procP n.+1)
    (H : ltsbP c r P P') :
  forall m (s : ren n m),
    ltsbP (pren s c) r (psubst s P) (psubst (up_ch s) P').
Proof.
  elim: H => {n c r P P'}.
  - move=> n c r P P' Hf m s /=.
    have HF := ltsfP_ren Hf (up_ch s).
    rewrite pren_up_pshift pren_up_zero in HF.
    exact: PB_Open HF.
  - move=> n c r P P' Q _ IH m s /=.
    rewrite psubst_shift_comm. exact: PB_ParL (IH _ _).
  - move=> n c r P Q Q' _ IH m s /=.
    rewrite psubst_shift_comm. exact: PB_ParR (IH _ _).
  - move=> n c r P P' _ IH m s /=.
    rewrite psubst_swap01_comm.
    apply: PB_Res. rewrite -pren_up_pshift. exact: IH.
Qed.

Lemma ltsselP_ren n (c : pch n) b P P' (H : ltsselP c b P P') :
  forall m (s : ren n m),
    ltsselP (pren s c) b (psubst s P) (psubst s P').
Proof.
  elim: H => {n c b P P'}.
  - move=> n c b K m s /=. exact: PS_Pfx.
  - move=> n c b P P' Q _ IH m s /=. exact: PS_ParL (IH _ _).
  - move=> n c b P Q Q' _ IH m s /=. exact: PS_ParR (IH _ _).
  - move=> n c b P P' _ IH m s /=.
    apply: PS_Res. rewrite -pren_up_pshift. exact: IH.
Qed.

Lemma ltsbrP_ren n (c : pch n) b P P' (H : ltsbrP c b P P') :
  forall m (s : ren n m),
    ltsbrP (pren s c) b (psubst s P) (psubst s P').
Proof.
  elim: H => {n c b P P'}.
  - move=> n c b K1 K2 m s /=.
    have := PBR_Pfx (pren s c) b (psubst s K1) (psubst s K2).
    by case: b.
  - move=> n c b P P' Q _ IH m s /=. exact: PBR_ParL (IH _ _).
  - move=> n c b P Q Q' _ IH m s /=. exact: PBR_ParR (IH _ _).
  - move=> n c b P P' _ IH m s /=.
    apply: PBR_Res. rewrite -pren_up_pshift. exact: IH.
Qed.

Lemma ltstP_ren n (P P' : procP n) (H : ltstP P P') :
  forall m (s : ren n m), ltstP (psubst s P) (psubst s P').
Proof.
  elim: H => {n P P'}.
  - move=> n P P' Q _ IH m s /=. exact: PT_ParL (IH _ _).
  - move=> n P Q Q' _ IH m s /=. exact: PT_ParR (IH _ _).
  - move=> n P P' _ IH m s /=. exact: PT_Res (IH _ _).
  - move=> n c P P' Q Q' Hc Hw m s /=.
    have HW := ltswP_ren Hw s. rewrite pren_flip in HW.
    exact: PT_CW (ltscP_ren Hc s) HW.
  - move=> n c P P' Q Q' Hw Hc m s /=.
    have HW := ltswP_ren Hw s. rewrite pren_flip in HW.
    exact: PT_WC HW (ltscP_ren Hc s).
  - move=> n c d P P' Q Q' Hf Hr m s /=.
    have HR := ltsrP_ren Hr s. rewrite pren_flip in HR.
    exact: PT_DR (ltsfP_ren Hf s) HR.
  - move=> n c d P P' Q Q' Hr Hf m s /=.
    have HR := ltsrP_ren Hr s. rewrite pren_flip in HR.
    exact: PT_RD HR (ltsfP_ren Hf s).
  - move=> n c r P P' Q Q' Hb Hr m s /=.
    have HR := ltsrP_ren Hr (up_ch s).
    rewrite pren_up_pshift pren_flip pren_up_zero psubst_shift_comm in HR.
    exact: PT_BR (ltsbP_ren Hb s) HR.
  - move=> n c r P P' Q Q' Hr Hb m s /=.
    have HR := ltsrP_ren Hr (up_ch s).
    rewrite pren_up_pshift pren_flip pren_up_zero psubst_shift_comm in HR.
    exact: PT_RB HR (ltsbP_ren Hb s).
  - move=> n c b P P' Q Q' Hs Hbr m s /=.
    have HB := ltsbrP_ren Hbr s. rewrite pren_flip in HB.
    exact: PT_SB (ltsselP_ren Hs s) HB.
  - move=> n c b P P' Q Q' Hbr Hs m s /=.
    have HB := ltsbrP_ren Hbr s. rewrite pren_flip in HB.
    exact: PT_BS HB (ltsselP_ren Hs s).
Qed.

Lemma ltstsP_ren n (P P' : procP n) (H : P —τ*→ P') :
  forall m (s : ren n m), psubst s P —τ*→ psubst s P'.
Proof.
  elim: H => [n0 X|n0 X Y R Hst _ IH] m s.
  - exact: PTS_refl.
  - exact: PTS_step (ltstP_ren Hst s) (IH _ _).
Qed.

(** ** Backward inversion: the superseded variants *)

Lemma psubst_inv_end m n (s : ren m n) P :
  psubst s P = ∅ -> P = ∅.
Proof. by case: P. Qed.

Lemma ltstP_ren_inv n' X R (H : ltstP X R) :
  forall m (s : ren m n') (P : procP m),
    (forall z1 z2, s z1 = s z2 -> z1 = z2) ->
    psubst s P = X ->
    exists P0, R = psubst s P0 /\ ltstP P P0.
Proof.
  elim: H => {n' X R}.
  - move=> n' A A' B _ IH m s P Hinj EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]]. rewrite EB.
    case: (IH _ _ _ Hinj (esym EA)) => P0 [-> H0].
    exists (P0 ∥ B0). split=> //=. exact: PT_ParL H0.
  - move=> n' A B B' _ IH m s P Hinj EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]]. rewrite EA.
    case: (IH _ _ _ Hinj (esym EB)) => P0 [-> H0].
    exists (A0 ∥ P0). split=> //=. exact: PT_ParR H0.
  - move=> n' B B' _ IH m s P Hinj EP.
    case: (psubst_inv_res EP) => B0 [-> EB]. 
    have Hinj' : forall z1 z2 : ch m.+1, up_ch s z1 = up_ch s z2 -> z1 = z2.
      move=> [z1|] [z2|] //= E.
      by rewrite (Hinj z1 z2
        (f_equal (fun c : ch n'.+1 => if c is Some u then u else s z1) E)).
    case: (IH _ _ _ Hinj' (esym EB)) => P0 [-> H0].
    exists ((ν) P0). split=> //=. exact: PT_Res H0.
  - move=> n' C A A' B B' Hc Hw m s P Hinj EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]].
    case: (ltscP_ren_inv Hc (esym EA)) => c [PA [E1 -> HA]].
    case: (ltswP_ren_inv Hw (esym EB)) => w [PB [E2 -> HB]].
    have E2' : pren s w = pren s (pflip c) by rewrite -E2 E1 pren_flip.
    have Ew := pren_inj Hinj E2'. subst w.
    exists (PA ∥ PB). split=> //=. exact: PT_CW HA HB.
  - move=> n' C A A' B B' Hw Hc m s P Hinj EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]].
    case: (ltswP_ren_inv Hw (esym EA)) => w [PA [E2 -> HA]].
    case: (ltscP_ren_inv Hc (esym EB)) => c [PB [E1 -> HB]].
    have E2' : pren s w = pren s (pflip c) by rewrite -E2 E1 pren_flip.
    have Ew := pren_inj Hinj E2'. subst w.
    exists (PA ∥ PB). split=> //=. exact: PT_WC HA HB.
  - move=> n' C D A A' B B' Hf Hr m s P Hinj EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]].
    case: (ltsfP_ren_inv Hf (esym EA)) => c [d [PA [E1 ED -> HA]]].
    case: (ltsrP_ren_inv Hr (esym EB)) => w [PB [E2 ER Hu]].
    have E2' : pren s w = pren s (pflip c) by rewrite -E2 E1 pren_flip.
    have Ew := pren_inj Hinj E2'. subst w.
    exists (PA ∥ psubst (scons d.1 id_ren) PB). split=> /=.
    + congr (_ ∥ _). rewrite ER ED !psubst_comp.
      by apply: psubst_ext => -[z|].
    + apply: PT_DR HA _.
      have Ed : D.2 = d.2 by rewrite ED.
      have Hu' := Hu d.1. rewrite Ed -surjective_pairing in Hu'.
      exact: Hu'.
  - move=> n' C D A A' B B' Hr Hf m s P Hinj EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]].
    case: (ltsrP_ren_inv Hr (esym EA)) => w [PA [E2 ER Hu]].
    case: (ltsfP_ren_inv Hf (esym EB)) => c [d [PB [E1 ED -> HB]]].
    have E2' : pren s w = pren s (pflip c) by rewrite -E2 E1 pren_flip.
    have Ew := pren_inj Hinj E2'. subst w.
    exists (psubst (scons d.1 id_ren) PA ∥ PB). split=> /=.
    + congr (_ ∥ _). rewrite ER ED !psubst_comp.
      by apply: psubst_ext => -[z|].
    + apply: PT_RD _ HB.
      have Ed : D.2 = d.2 by rewrite ED.
      have Hu' := Hu d.1. rewrite Ed -surjective_pairing in Hu'.
      exact: Hu'.
  - move=> n' C r A A' B B' Hb Hr m s P Hinj EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]].
    case: (ltsbP_ren_inv Hb (esym EA)) => c [PA [E1 -> HA]].
    have EBs : psubst shift B = psubst (up_ch s) (psubst shift B0).
      by rewrite EB psubst_shift_comm.
    move: Hr. rewrite EBs => Hr.
    case: (ltsrP_ren_inv Hr erefl) => w [PB [E2 ER Hu]].
    have Hinj' : forall z1 z2 : ch m.+1, up_ch s z1 = up_ch s z2 -> z1 = z2.
      move=> [z1|] [z2|] //= E.
      by rewrite (Hinj z1 z2
        (f_equal (fun cc : ch n'.+1 => if cc is Some u then u else s z1) E)).
    have E2' : pren (up_ch s) w = pren (up_ch s) (pshift (pflip c)).
      by rewrite -E2 E1 pren_up_pshift pren_flip.
    have Ew := pren_inj Hinj' E2'. subst w.
    exists ((ν) (PA ∥ psubst (scons zero id_ren) PB)). split=> /=.
    + congr PRes. congr (_ ∥ _). rewrite ER /= !psubst_comp.
      by apply: psubst_ext => -[z|].
    + apply: PT_BR HA _.
      exact: (Hu zero).
  - move=> n' C r A A' B B' Hr Hb m s P Hinj EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]].
    case: (ltsbP_ren_inv Hb (esym EB)) => c [PB [E1 -> HB]].
    have EAs : psubst shift A = psubst (up_ch s) (psubst shift A0).
      by rewrite EA psubst_shift_comm.
    move: Hr. rewrite EAs => Hr.
    case: (ltsrP_ren_inv Hr erefl) => w [PA [E2 ER Hu]].
    have Hinj' : forall z1 z2 : ch m.+1, up_ch s z1 = up_ch s z2 -> z1 = z2.
      move=> [z1|] [z2|] //= E.
      by rewrite (Hinj z1 z2
        (f_equal (fun cc : ch n'.+1 => if cc is Some u then u else s z1) E)).
    have E2' : pren (up_ch s) w = pren (up_ch s) (pshift (pflip c)).
      by rewrite -E2 E1 pren_up_pshift pren_flip.
    have Ew := pren_inj Hinj' E2'. subst w.
    exists ((ν) (psubst (scons zero id_ren) PA ∥ PB)). split=> /=.
    + congr PRes. congr (_ ∥ _). rewrite ER /= !psubst_comp.
      by apply: psubst_ext => -[z|].
    + apply: PT_RB _ HB.
      exact: (Hu zero).
  - move=> n' C b A A' B B' Hs Hbr m s P Hinj EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]].
    case: (ltsselP_ren_inv Hs (esym EA)) => c [PA [E1 -> HA]].
    case: (ltsbrP_ren_inv Hbr (esym EB)) => w [PB [E2 -> HB]].
    have E2' : pren s w = pren s (pflip c) by rewrite -E2 E1 pren_flip.
    have Ew := pren_inj Hinj E2'. subst w.
    exists (PA ∥ PB). split=> //=. exact: PT_SB HA HB.
  - move=> n' C b A A' B B' Hbr Hs m s P Hinj EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]].
    case: (ltsbrP_ren_inv Hbr (esym EA)) => w [PA [E2 -> HA]].
    case: (ltsselP_ren_inv Hs (esym EB)) => c [PB [E1 -> HB]].
    have E2' : pren s w = pren s (pflip c) by rewrite -E2 E1 pren_flip.
    have Ew := pren_inj Hinj E2'. subst w.
    exists (PA ∥ PB). split=> //=. exact: PT_BS HA HB.
Qed.

(** ** Closed-world compatibility lemmas *)

Lemma compat_closeP n (Δ : sctxP n) (x : ch n) (r : pol) K :
  Δ x = Some (SSep r SClose) ->
  SEMP (scupd x None Δ) K ->
  SEMP Δ ((x, r) !․ K).
Proof.
  move=> HxS HK k. case: k => [//|k]. split.
  - split=> //.
    move=> a c Hof. case: (offers_close Hof) => -> ->.
    exists SClose. by rewrite /sat /= HxS /= pol_eqb_refl.
  - move=> w rw S HwS.
    case: S HwS => [| |T S2|T S2|S1 S2|S1 S2] HwS /=.
    + move=> P' HT. case: (pinv_c_closeF HT) => Ec ->.
      move: Ec => -[E1 E2]. subst.
      exact (HK k).
    + move=> P' HT. by case: (pinv_w_close HT).
    + split.
      * move=> y rd P' HT. by case: (pinv_f_close2 HT).
      * move=> r' P' HT. by case: (pinv_b_close HT).
    + split.
      * move=> y rd P' HT. by case: (pinv_r_close2 HT).
      * move=> rd P'' HT. by case: (pinv_r_close2 HT).
    + move=> b P' HT. by case: (pinv_sel_close HT).
    + move=> b P' HT. by case: (pinv_br_close HT).
  - move=> P' Hst. by case: (pinv_t_close Hst).
Qed.

Lemma compat_waitP n (Δ : sctxP n) (x : ch n) (r : pol) K :
  Δ x = Some (SSep r SWait) ->
  SEMP (scupd x None Δ) K ->
  SEMP Δ ((x, r) ?․ K).
Proof.
  move=> HxS HK k. case: k => [//|k]. split.
  - split=> //.
    move=> a c Hof. case: (offers_wait Hof) => -> ->.
    exists SWait. by rewrite /sat /= HxS /= pol_eqb_refl.
  - move=> w rw S HwS.
    case: S HwS => [| |T S2|T S2|S1 S2|S1 S2] HwS /=.
    + move=> P' HT. by case: (pinv_c_wait HT).
    + move=> P' HT. case: (pinv_w_waitF HT) => Ec ->.
      move: Ec => -[E1 E2]. subst.
      exact (HK k).
    + split.
      * move=> y rd P' HT. by case: (pinv_f_wait2 HT).
      * move=> r' P' HT. by case: (pinv_b_wait HT).
    + split.
      * move=> y rd P' HT. by case: (pinv_r_wait2 HT).
      * move=> rd P'' HT. by case: (pinv_r_wait2 HT).
    + move=> b P' HT. by case: (pinv_sel_wait HT).
    + move=> b P' HT. by case: (pinv_br_wait HT).
  - move=> P' Hst. by case: (pinv_t_wait Hst).
Qed.

Lemma compat_delP n (Δ : sctxP n) (x y : ch n) (r rd : pol) T S2 K :
  Δ x = Some (SSep r (SSend T S2)) ->
  Δ y = Some (SSep rd T) ->
  SEMP (scupd y None (scupd x (Some (SSep r S2)) Δ)) K ->
  SEMP Δ ((x, r) ! (y, rd) ․ K).
Proof.
  move=> HxS HyS HK k. case: k => [//|k]. split.
  - split=> //.
    move=> a c Hof. case: (offers_del Hof) => -> ->.
    exists (SSend T S2). by rewrite /sat /= HxS /= pol_eqb_refl.
  - move=> w rw S HwS.
    case: S HwS => [| |T' S2'|T' S2'|S1' S2'|S1' S2'] HwS /=.
    + move=> P' HT. by case: (pinv_c_del HT).
    + move=> P' HT. by case: (pinv_w_del HT).
    + split.
      * move=> y' rd' P' HT.
        case: (pinv_f_delF HT) => Ec Ed ->.
        move: Ec Ed => -[E1 E2] -[E3 E4]. subst.
        move: HwS. rewrite HxS => -[ET ES2]. rewrite -ET -ES2.
        exists (SSep rd T).
        split; [exact: HyS | by rewrite /= pol_eqb_refl | exact (HK k)].
      * move=> r' P' HT. by case: (pinv_b_del HT).
    + split.
      * move=> y' rd' P' HT. by case: (pinv_r_del HT).
      * move=> rd' P'' HT. by case: (pinv_r_del HT).
    + move=> b P' HT. by case: (pinv_sel_del HT).
    + move=> b P' HT. by case: (pinv_br_del HT).
  - move=> P' Hst. by case: (pinv_t_del Hst).
Qed.

(** ** Assorted scaffolding *)

Lemma sle_econsume o1 o2 r T :
  sle o1 o2 ->
  (if o1 is Some e then esat r e else None) = Some T ->
  sle (if o1 is Some e then econsume r e else None)
      (if o2 is Some e then econsume r e else None).
Proof.
  case=> [->|[->|[r' [T' [-> ->]]]]] //=.
  - move=> _. exact: sle_refl.
  - move=> _. exact: sle_none.
Qed.

Lemma spush_both_inv m n (σ : ren m n) (Δs : sctxP m) w S0 :
  vok σ Δs ->
  spush σ Δs w = Some (SBoth S0) ->
  (exists x,
    [/\ σ x = w, Δs x = Some (SBoth S0)
      & forall x', σ x' = w -> Δs x' <> None -> x' = x])
  \/ (exists x0 x1 ρ T,
       [/\ σ x0 = w, σ x1 = w, x0 <> x1,
           Δs x0 = Some (SSep ρ T) /\ Δs x1 = Some (SSep (flipp ρ) (dual T))
         & S0 = pole ρ T]).
Proof.
  move=> Hv. rewrite /spush.
  case F : (find_ch (fun x => (σ x == w) && ~~ oslot_eqb (Δs x) None))
    => [x0|] //.
  move: (find_ch_sound F) => /spush_p1 [E0 Ho0].
  case F2 : (find_ch (fun x' => [&& σ x' == w,
                ~~ oslot_eqb (Δs x') None & x' != x0])) => [x1|].
  - move: (find_ch_sound F2) => /and3P[/eqP E1 Ho1 Hne1].
    have Hox1 : Δs x1 <> None.
      by case: (oslot_eqP (Δs x1) None) Ho1.
    have Hne : x0 <> x1.
      by move=> E; move: Hne1; rewrite E eqxx.
    case: (Hv x0 x1 Ho0 Hox1 _).
      by rewrite E0 E1.
      by move=> E; case: (Hne E).
    move=> [ρ [T [D0 D1]]].
    rewrite D0. move=> [ES0].
    right. exists x0, x1, ρ, T. by split.
  - move=> ED. left. exists x0. split=> //.
    move=> x' Ex' Hox'.
    case Enx : (x' == x0); first by move/eqP: Enx.
    have Hp : [&& σ x' == w, ~~ oslot_eqb (Δs x') None & x' != x0].
      rewrite Ex' eqxx Enx andbT /=.
      by case: (oslot_eqP (Δs x') None).
    case: (find_ch_complete (p := fun x' => [&& σ x' == w,
              ~~ oslot_eqb (Δs x') None & x' != x0]) Hp) => x'' F''.
    by rewrite F'' in F2.
Qed.

Lemma spush_shift_zero m n (σ : ren m n) (Δs : sctxP m) :
  spush (fun x => shift (σ x)) Δs zero = None.
Proof. by apply: spush_none_fwd. Qed.

Lemma srecv_neqT T S2 : T = SRecv T S2 -> False.
Proof.
  move=> E. have := f_equal stysz E. rewrite /= => /eqP.
  by rewrite -[X in X == _]addn0 -addnS eqn_add2l.
Qed.

Lemma psubst_recv_shift_collapse m n (σ : ren m n) (K : procP m.+1) :
  psubst (scons zero id_ren)
    (psubst (up_ch (fun z => shift (σ z))) K)
  = psubst (up_ch σ) K.
Proof. rewrite psubst_comp. by apply: psubst_ext => -[z|]. Qed.
