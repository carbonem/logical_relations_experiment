(** * Semantic combinators for the step-indexed logical relation

    The lemmas that assemble [EsemT] proofs of compound processes from
    proofs of their parts:

    - [EsemT_weaken]   -- unused owned channels are harmless
    - [ltst_ren_inv2]  -- τ-steps of a renamed process come from the
                          original, along *any* renaming (subjects of a
                          sync are forced to the binder, so no
                          injectivity is needed)
    - [EsemT_ren]      -- the relation is closed under renaming, given
                          agreement of the two contexts along the
                          renaming and injectivity on owned channels;
                          the parallel-descent clause transports by a
                          computable pushforward of the split
    - [par_combineT]   -- semantic parallel composition over [split]
    - [syncC_sem]      -- a close/wait synchronization consumes two
                          value clauses and two units of budget

    Everything is by induction on the step budget [k]; no structural
    congruence anywhere. *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import synsem Errors LogRel Toolkit LTS Transfer Typing
  Fundamental Tau LogRelTau TauInv TauEquiv.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** Widening a split along a context extension

    Extra channels of the larger context ride on the left component. *)
Section SplitWiden.
Variables (n : nat) (Δ1 Δ2 Δa Δb : sctx n).
Hypothesis Hle : ctx_le Δ1 Δ2.
Hypothesis Hs : split Δ1 Δa Δb.

Definition wider : sctx n :=
  fun w => if Δb w is Some _ then None else Δ2 w.

Lemma split_widen : split Δ2 wider Δb.
Proof.
  move=> w. rewrite /wider.
  case Eb : (Δb w) => [S|].
  - right.
    have Hb : Δ1 w = Some S.
      case: (Hs w) => [[_ Hb]|[Hb _]]; first by rewrite Eb in Hb.
      by rewrite -Hb.
    have H2 : Δ2 w = Some S by apply: Hle Hb.
    by rewrite H2.
  - by left.
Qed.

Lemma ctx_le_wider : ctx_le Δa wider.
Proof.
  move=> w S Ha. rewrite /wider.
  case: (Hs w) => [[Ha' Hb]|[_ Hb]]; last by rewrite Hb in Ha.
  rewrite Hb. apply: Hle. by rewrite -Ha'.
Qed.
End SplitWiden.

(** ** Weakening *)
Lemma EsemT_weaken k : forall n (Δ1 Δ2 : sctx n) (P : proc n),
  ctx_le Δ1 Δ2 -> EsemT k Δ1 P -> EsemT k Δ2 P.
Proof.
  elim: k => [//|k IH] n Δ1 Δ2 P Hle [C V D X St]. split.
  - move=> a x Hof. case: (C _ _ Hof) => S [HS Ha].
    exists S. split=> //. exact: Hle.
  - move=> x S HxS.
    case E1 : (Δ1 x) => [S'|].
    + have ES : S' = S by move: (Hle _ _ E1); rewrite HxS => -[].
      subst S'. move: (V _ _ E1). clear E1.
      case: S HxS => [| |T S2|T S2] HxS /= HV.
      * move=> P'' HT. apply: IH (HV _ HT). exact: ctx_le_cupd.
      * move=> P'' HT. apply: IH (HV _ HT). exact: ctx_le_cupd.
      * case: HV => HVf HVb. split.
        -- move=> y P'' HT. case: (HVf _ _ HT) => Hy HE'.
           split; first exact: Hle.
           apply: IH HE'. do 2 apply: ctx_le_cupd. exact: Hle.
        -- move=> P'' HT. apply: IH (HVb _ HT).
           do 2 apply: ctx_le_scons. exact: ctx_le_cupd.
      * move=> P'' HT. apply: IH (HV _ HT).
        apply: ctx_le_scons. exact: ctx_le_cupd.
    + case: S HxS => [| |T S2|T S2] HxS /=.
      * move=> P'' HT. exfalso.
        case: (C AClose x (ex_intro _ _ HT)) => S' [HS' _].
        by rewrite E1 in HS'.
      * move=> P'' HT. exfalso.
        case: (C AWait x (ex_intro _ _ HT)) => S' [HS' _].
        by rewrite E1 in HS'.
      * split.
        -- move=> y P'' HT. exfalso.
           case: (C ADelS x (or_introl (ex_intro _ y (ex_intro _ _ HT))))
             => S' [HS' _]. by rewrite E1 in HS'.
        -- move=> P'' HT. exfalso.
           case: (C ADelS x (or_intror (ex_intro _ _ HT)))
             => S' [HS' _]. by rewrite E1 in HS'.
      * move=> P'' HT. exfalso.
        case: (C ADelR x (ex_intro _ _ HT)) => S' [HS' _].
        by rewrite E1 in HS'.
  - move=> P1 P2 E12. case: (D _ _ E12) => ΔA [ΔB [Hsp H1 H2]].
    exists (wider Δ2 ΔB), ΔB.
    split.
    + exact: split_widen Hle Hsp.
    + apply: IH H1. exact: ctx_le_wider Hle Hsp.
    + exact: H2.
  - move=> Q HQ. case: (X _ HQ) => S HS. exists S.
    apply: IH HS. exact: ctx_le_cext.
  - move=> P' Hst. apply: IH (St _ Hst). exact: Hle.
Qed.

Lemma EsemT_ext k n (Δ Δ' : sctx n) (P : proc n) :
  (forall x, Δ x = Δ' x) -> EsemT k Δ P -> EsemT k Δ' P.
Proof. move=> H. apply: EsemT_weaken. exact: ctx_le_of_ext. Qed.

(** ** Existential backward equivariance for synchronizations

    A sync of a renamed process pulls back along *any* renaming: the
    subjects come out existentially, and the residue is an image.  The
    consumers instantiate at [up_ch (up_ch s)] with subjects [one] and
    [zero], where [up2_image_one]/[up2_image_zero] then pin the
    preimage subjects to the binder -- injectivity of [s] never
    enters. *)
Lemma syncC_ren_inv2 n' (x y : ch n') Q R (H : syncC x y Q R) :
  forall m (s : ren m n') P,
    subst_proc s P = Q ->
    exists x0 y0 R0,
      [/\ x = s x0, y = s y0, R = subst_proc s R0 & syncC x0 y0 P R0].
Proof.
  elim: H => {n' x y Q R}.
  - move=> n' x y P1 P1' Q1 Q1' Hc Hw m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (ltsc_ren_inv2 Hc erefl) => x0 [Pa' [Ex -> Ha]].
    case: (ltsw_ren_inv2 Hw erefl) => y0 [Pb' [Ey -> Hb]].
    exists x0, y0, (Pa' ∥ Pb'). split=> //=. exact: SYC_L Ha Hb.
  - move=> n' x y P1 P1' Q1 Q1' Hw Hc m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (ltsw_ren_inv2 Hw erefl) => y0 [Pa' [Ey -> Ha]].
    case: (ltsc_ren_inv2 Hc erefl) => x0 [Pb' [Ex -> Hb]].
    exists x0, y0, (Pa' ∥ Pb'). split=> //=. exact: SYC_R Ha Hb.
  - move=> n' x y P1 R1 Q1 _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => x0 [y0 [R0 [Ex Ey -> HS]]].
    exists x0, y0, (R0 ∥ Pb). split=> //=. exact: SYC_ParL HS.
  - move=> n' x y P1 Q1 R1 _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => x0 [y0 [R0 [Ex Ey -> HS]]].
    exists x0, y0, (Pa ∥ R0). split=> //=. exact: SYC_ParR HS.
  - move=> n' x y P1 R1 _ IH m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (IH _ _ _ erefl) => x0 [y0 [R0 [Ex Ey -> HS]]].
    case: (up2_image_shift2 (esym Ex)) => x1 [Ex1 Ex2].
    case: (up2_image_shift2 (esym Ey)) => y1 [Ey1 Ey2]. subst.
    exists x1, y1, ((ν) R0). split=> //=. exact: SYC_Res HS.
Qed.

Lemma syncD_ren_inv2 n' (x y : ch n') Q R (H : syncD x y Q R) :
  forall m (s : ren m n') P,
    subst_proc s P = Q ->
    exists x0 y0 R0,
      [/\ x = s x0, y = s y0, R = subst_proc s R0 & syncD x0 y0 P R0].
Proof.
  elim: H => {n' x y Q R}.
  - move=> n' x y z P1 P1' Q1 Q1' Hf Hr m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (ltsf_ren_inv3 Hf erefl) => x0 [z0 [Pa' [Ex Ez -> Ha]]].
    case: (ltsr_ren_inv2 Hr erefl) => y0 [Pb' [Ey -> Hb]].
    exists x0, y0, (Pa' ∥ subst_proc (scons z0 id_ren) Pb').
    split=> //=; last exact: SYD_L Ha Hb.
    congr (_ ∥ _). rewrite !subst_proc_comp Ez.
    apply: subst_eqP => w. by rewrite /= scons_up1.
  - move=> n' x y z P1 P1' Q1 Q1' Hr Hf m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (ltsr_ren_inv2 Hr erefl) => y0 [Pa' [Ey -> Ha]].
    case: (ltsf_ren_inv3 Hf erefl) => x0 [z0 [Pb' [Ex Ez -> Hb]]].
    exists x0, y0, (subst_proc (scons z0 id_ren) Pa' ∥ Pb').
    split=> //=; last exact: SYD_R Ha Hb.
    congr (_ ∥ _). rewrite !subst_proc_comp Ez.
    apply: subst_eqP => w. by rewrite /= scons_up1.
  - move=> n' x y P1 R1 Q1 _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => x0 [y0 [R0 [Ex Ey -> HS]]].
    exists x0, y0, (R0 ∥ Pb). split=> //=. exact: SYD_ParL HS.
  - move=> n' x y P1 Q1 R1 _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => x0 [y0 [R0 [Ex Ey -> HS]]].
    exists x0, y0, (Pa ∥ R0). split=> //=. exact: SYD_ParR HS.
  - move=> n' x y P1 R1 _ IH m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (IH _ _ _ erefl) => x0 [y0 [R0 [Ex Ey -> HS]]].
    case: (up2_image_shift2 (esym Ex)) => x1 [Ex1 Ex2].
    case: (up2_image_shift2 (esym Ey)) => y1 [Ey1 Ey2]. subst.
    exists x1, y1, ((ν) R0). split=> //=. exact: SYD_Res HS.
Qed.

Lemma syncB_ren_inv2 n' (x y : ch n') Q R (H : syncB x y Q R) :
  forall m (s : ren m n') P,
    subst_proc s P = Q ->
    exists x0 y0 R0,
      [/\ x = s x0, y = s y0, R = subst_proc s R0 & syncB x0 y0 P R0].
Proof.
  elim: H => {n' x y Q R}.
  - move=> n' x y P1 P1' Q1 Q1' Hb Hr m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (ltsb_ren_inv2 Hb erefl) => x0 [Pa' [Ex -> Ha]].
    case: (ltsr_ren_inv2 Hr erefl) => y0 [Pb' [Ey -> Hb']].
    exists x0, y0, ((ν) (Pa' ∥ subst_proc open_recv Pb')).
    split=> //=; last exact: SYB_L Ha Hb'.
    congr ResP. congr (_ ∥ _). rewrite !subst_proc_comp.
    apply: subst_eqP => w. by rewrite /= open_recv_up.
  - move=> n' x y P1 P1' Q1 Q1' Hr Hb m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (ltsr_ren_inv2 Hr erefl) => y0 [Pa' [Ey -> Ha]].
    case: (ltsb_ren_inv2 Hb erefl) => x0 [Pb' [Ex -> Hb']].
    exists x0, y0, ((ν) (subst_proc open_recv Pa' ∥ Pb')).
    split=> //=; last exact: SYB_R Ha Hb'.
    congr ResP. congr (_ ∥ _). rewrite !subst_proc_comp.
    apply: subst_eqP => w. by rewrite /= open_recv_up.
  - move=> n' x y P1 R1 Q1 _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => x0 [y0 [R0 [Ex Ey -> HS]]].
    exists x0, y0, (R0 ∥ Pb). split=> //=. exact: SYB_ParL HS.
  - move=> n' x y P1 Q1 R1 _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => x0 [y0 [R0 [Ex Ey -> HS]]].
    exists x0, y0, (Pa ∥ R0). split=> //=. exact: SYB_ParR HS.
  - move=> n' x y P1 R1 _ IH m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (IH _ _ _ erefl) => x0 [y0 [R0 [Ex Ey -> HS]]].
    case: (up2_image_shift2 (esym Ex)) => x1 [Ex1 Ex2].
    case: (up2_image_shift2 (esym Ey)) => y1 [Ey1 Ey2]. subst.
    exists x1, y1, ((ν) R0). split=> //=. exact: SYB_Res HS.
Qed.

Lemma ltst_ren_inv2 n' Q R (H : ltst Q R) :
  forall m (s : ren m n') P,
    subst_proc s P = Q ->
    exists R0, R = subst_proc s R0 /\ ltst P R0.
Proof.
  elim: H => {n' Q R}.
  - move=> n' P1 P1' Q1 _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => R0 [-> H0].
    exists (R0 ∥ Pb). split=> //=. exact: LT_ParL H0.
  - move=> n' P1 Q1 Q1' _ IH m s P EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ erefl) => R0 [-> H0].
    exists (Pa ∥ R0). split=> //=. exact: LT_ParR H0.
  - move=> n' P1 P1' _ IH m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (IH _ _ _ erefl) => R0 [-> H0].
    exists ((ν) R0). split=> //=. exact: LT_Res H0.
  - move=> n' P1 R1 HS m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (syncC_ren_inv2 HS erefl) => x0 [y0 [R0 [Ex Ey -> H0]]].
    have Ex1 : x0 = one by apply: up2_image_one (esym Ex).
    have Ey1 : y0 = zero by apply: up2_image_zero (esym Ey).
    subst. exists ((ν) R0). split=> //. exact: LT_CommC1 H0.
  - move=> n' P1 R1 HS m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (syncC_ren_inv2 HS erefl) => x0 [y0 [R0 [Ex Ey -> H0]]].
    have Ex1 : x0 = zero by apply: up2_image_zero (esym Ex).
    have Ey1 : y0 = one by apply: up2_image_one (esym Ey).
    subst. exists ((ν) R0). split=> //. exact: LT_CommC2 H0.
  - move=> n' P1 R1 HS m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (syncD_ren_inv2 HS erefl) => x0 [y0 [R0 [Ex Ey -> H0]]].
    have Ex1 : x0 = one by apply: up2_image_one (esym Ex).
    have Ey1 : y0 = zero by apply: up2_image_zero (esym Ey).
    subst. exists ((ν) R0). split=> //. exact: LT_CommD1 H0.
  - move=> n' P1 R1 HS m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (syncD_ren_inv2 HS erefl) => x0 [y0 [R0 [Ex Ey -> H0]]].
    have Ex1 : x0 = zero by apply: up2_image_zero (esym Ex).
    have Ey1 : y0 = one by apply: up2_image_one (esym Ey).
    subst. exists ((ν) R0). split=> //. exact: LT_CommD2 H0.
  - move=> n' P1 R1 HS m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (syncB_ren_inv2 HS erefl) => x0 [y0 [R0 [Ex Ey -> H0]]].
    have Ex1 : x0 = one by apply: up2_image_one (esym Ex).
    have Ey1 : y0 = zero by apply: up2_image_zero (esym Ey).
    subst. exists ((ν) R0). split=> //. exact: LT_CommB1 H0.
  - move=> n' P1 R1 HS m s P EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (syncB_ren_inv2 HS erefl) => x0 [y0 [R0 [Ex Ey -> H0]]].
    have Ex1 : x0 = zero by apply: up2_image_zero (esym Ex).
    have Ey1 : y0 = one by apply: up2_image_one (esym Ey).
    subst. exists ((ν) R0). split=> //. exact: LT_CommB2 H0.
Qed.

Lemma ltsts_ren_inv2 n' Q (R : proc n') (H : Q —τ*→ R) :
  forall m (s : ren m n') (P : proc m),
    subst_proc s P = Q ->
    exists R0, R = subst_proc s R0 /\ P —τ*→ R0.
Proof.
  elim: H => [n0 X|n0 X Y R0 Hst _ IH] m s P EP.
  - exists P. split; by [rewrite EP | exact: TS_refl].
  - case: (ltst_ren_inv2 Hst EP) => Q0 [EQ HPQ].
    case: (IH _ _ _ (esym EQ)) => R1 [ER HQR].
    exists R1. split=> //. exact: TS_step HPQ HQR.
Qed.

(** ** Context agreement along a renaming, and its stability *)

Definition agree m n (s : ren m n) (Δm : sctx m) (Δn : sctx n) : Prop :=
  forall z, Δm z = None \/ Δn (s z) = Δm z.

Definition inj_on m n (s : ren m n) (Δm : sctx m) : Prop :=
  forall z1 z2, Δm z1 <> None -> Δm z2 <> None -> s z1 = s z2 -> z1 = z2.

Lemma inj_on_sub m n (s : ren m n) (ΔA ΔB : sctx m) :
  (forall z, ΔA z <> None -> ΔB z <> None) ->
  inj_on s ΔB -> inj_on s ΔA.
Proof. move=> Hsub Hinj z1 z2 H1 H2. exact: Hinj (Hsub _ H1) (Hsub _ H2). Qed.

Lemma owned_cupd_sub m (Δ : sctx m) (x0 : ch m) o :
  Δ x0 <> None ->
  forall z, cupd x0 o Δ z <> None -> Δ z <> None.
Proof.
  move=> Hx z. rewrite /cupd.
  by case: (z =P x0) => [->|_].
Qed.

Lemma agree_cupd m n (s : ren m n) (Δm : sctx m) (Δn : sctx n)
    (x0 : ch m) o :
  agree s Δm Δn -> inj_on s Δm -> Δm x0 <> None ->
  agree s (cupd x0 o Δm) (cupd (s x0) o Δn).
Proof.
  move=> Hag Hinj Hx z. rewrite /cupd.
  case: (z =P x0) => [-> | Hne].
  - by rewrite eqxx; right.
  - case E : (Δm z) => [S|]; last by left.
    right.
    have Hne2 : (s z == s x0) = false.
      apply/eqP => Es. apply: Hne. apply: Hinj Es => //.
      by rewrite E.
    rewrite Hne2.
    by case: (Hag z); rewrite E.
Qed.

Lemma agree_scons m n (s : ren m n) (Δm : sctx m) (Δn : sctx n) o :
  agree s Δm Δn ->
  agree (up_ch s) (scons o Δm) (scons o Δn).
Proof.
  move=> Hag [z|] /=.
  - by case: (Hag z) => [E|E]; [left | right].
  - by right.
Qed.

Lemma inj_scons m n (s : ren m n) (Δm : sctx m) o :
  inj_on s Δm -> inj_on (up_ch s) (scons o Δm).
Proof.
  move=> Hinj [z1|] [z2|] //= H1 H2 E.
  have Es := f_equal (fun c : option (ch n) => if c is Some u then u else s z1) E.
  by rewrite (Hinj _ _ H1 H2 Es).
Qed.

Lemma agree_cext m n (s : ren m n) (Δm : sctx m) (Δn : sctx n) S :
  agree s Δm Δn ->
  agree (up_ch (up_ch s)) (cext S Δm) (cext S Δn).
Proof. move=> H. apply: agree_scons. exact: agree_scons. Qed.

Lemma inj_cext m n (s : ren m n) (Δm : sctx m) S :
  inj_on s Δm -> inj_on (up_ch (up_ch s)) (cext S Δm).
Proof. move=> H. apply: inj_scons. exact: inj_scons. Qed.


(** ** Pushing a split forward along a renaming

    The right component moves by the computable pushforward; whatever
    the pushforward does not claim stays left.  Both components then
    agree with their sources along [s]. *)
Section PfwdSplit.
Variables (m n : nat) (s : ren m n).
Variables (Δm : sctx m) (Δn : sctx n) (Δa Δb : sctx m).
Hypothesis Hag : agree s Δm Δn.
Hypothesis Hinj : inj_on s Δm.
Hypothesis Hs : split Δm Δa Δb.

Let ownA z := Δa z <> None.
Let ownB z := Δb z <> None.

Lemma split_ownL z : Δa z <> None -> Δm z <> None.
Proof.
  move=> Ha. case: (Hs z) => [[E _]|[_ E]]; last by rewrite E in Ha.
  by rewrite -E.
Qed.

Lemma split_ownR z : Δb z <> None -> Δm z <> None.
Proof.
  move=> Hb. case: (Hs z) => [[_ E]|[E _]]; first by rewrite E in Hb.
  by rewrite -E.
Qed.

Definition pleft : sctx n :=
  fun w => if pfwd s Δb w is Some _ then None else Δn w.

Lemma pfwd_split : split Δn pleft (pfwd s Δb).
Proof.
  move=> w. rewrite /pleft.
  case Eb : (pfwd s Δb w) => [S|]; last by left.
  right. split=> //.
  move: Eb. rewrite /pfwd.
  case F : (find_ch (fun z => (s z == w) && isSome (Δb z))) => [z|] // Ez.
  move: (find_ch_sound F) => /andP[/eqP Es Ho].
  have HmB : Δm z = Δb z.
    case: (Hs z) => [[_ E]|[E _]]; last by rewrite E.
    by rewrite E in Ho.
  case: (Hag z) => [E|E].
  - by rewrite -HmB E in Ho.
  - by rewrite -Es E HmB Ez.
Qed.

Lemma agree_pfwdR : agree s Δb (pfwd s Δb).
Proof.
  apply: pfwd_agree => z1 z2 H1 H2.
  exact: Hinj (split_ownR H1) (split_ownR H2).
Qed.

Lemma inj_onR : inj_on s Δb.
Proof. exact: inj_on_sub split_ownR Hinj. Qed.

Lemma inj_onL : inj_on s Δa.
Proof. exact: inj_on_sub split_ownL Hinj. Qed.

Lemma agree_pleft : agree s Δa pleft.
Proof.
  move=> z. case Ea : (Δa z) => [S|]; last by left.
  right. rewrite /pleft.
  have HmA : Δm z = Some S.
    case: (Hs z) => [[E _]|[_ E]]; last by rewrite E in Ea.
    by rewrite -E.
  case Eb : (pfwd s Δb (s z)) => [S'|].
  - exfalso. move: Eb. rewrite /pfwd.
    case F : (find_ch (fun z0 => (s z0 == s z) && isSome (Δb z0)))
      => [z'|] // Ez.
    move: (find_ch_sound F) => /andP[/eqP Es Ho].
    have Ez' : z' = z.
      apply: Hinj Es.
      - apply: split_ownR. by move: Ho; case: (Δb z').
      - by rewrite HmA.
    rewrite Ez' in Ho.
    case: (Hs z) => [[_ E]|[_ E]]; first by move: Ho; rewrite E.
    by rewrite E in Ea.
  - case: (Hag z) => [E|E]; first by rewrite HmA in E.
    by rewrite E HmA.
Qed.
End PfwdSplit.

(** ** Renaming closure

    The two side conditions are exactly what communication needs:
    [agree] lets owned obligations transport ([None]-slots of the
    source may collapse), [inj_on] keeps distinct owned channels from
    aliasing.  Conformance of the source excludes every transition at
    a channel outside the owned image, via [offers_ren_inv]. *)
Lemma EsemT_ren k : forall m n (s : ren m n) (Δm : sctx m) (Δn : sctx n)
    (P : proc m),
  agree s Δm Δn -> inj_on s Δm ->
  EsemT k Δm P -> EsemT k Δn (subst_proc s P).
Proof.
  elim: k => [//|k IH] m n s Δm Δn P Hag Hinj [C V D X St].
  have det : forall (x0 : ch m) S', Δm x0 = Some S' ->
      forall S, Δn (s x0) = Some S -> S' = S.
    move=> x0 S' HS' S0 HnS.
    case: (Hag x0) => [E|E]; first by rewrite E in HS'.
    rewrite HS' in E. rewrite E in HnS. by case: HnS.
  split.
  - (* conformance *)
    move=> a w Hof.
    case: (offers_ren_inv Hof) => x0 [-> Hof0].
    case: (C _ _ Hof0) => S [HS Ha].
    exists S. split=> //.
    case: (Hag x0) => [E|E]; first by rewrite E in HS.
    by rewrite E.
  - (* value clauses *)
    move=> w S HwS.
    case: S HwS => [| |T S2|T S2] HwS /=.
    + (* SClose *)
      move=> P'' HT.
      case: (ltsc_ren_inv2 HT erefl) => x0 [P0'' [Ew -> H0]].
      have Hof0 : offers AClose x0 P by exists P0''.
      case: (C _ _ Hof0) => S' [HS' _].
      rewrite Ew in HwS. have ES' := det _ _ HS' _ HwS. subst S'.
      move: (V _ _ HS') => /= HV.
      have HE0 := HV _ H0.
      rewrite Ew. apply: IH HE0.
      * apply: agree_cupd => //. by rewrite HS'.
      * apply: inj_on_sub Hinj. apply: owned_cupd_sub. by rewrite HS'.
    + (* SWait *)
      move=> P'' HT.
      case: (ltsw_ren_inv2 HT erefl) => x0 [P0'' [Ew -> H0]].
      have Hof0 : offers AWait x0 P by exists P0''.
      case: (C _ _ Hof0) => S' [HS' _].
      rewrite Ew in HwS. have ES' := det _ _ HS' _ HwS. subst S'.
      move: (V _ _ HS') => /= HV.
      have HE0 := HV _ H0.
      rewrite Ew. apply: IH HE0.
      * apply: agree_cupd => //. by rewrite HS'.
      * apply: inj_on_sub Hinj. apply: owned_cupd_sub. by rewrite HS'.
    + (* SSend: free and bound delegation *)
      split.
      * move=> y P'' HT.
        case: (ltsf_ren_inv3 HT erefl) => x0 [w0 [P0'' [Ew Ey -> H0]]].
        have Hof0 : offers ADelS x0 P by left; exists w0, P0''.
        case: (C _ _ Hof0) => S' [HS' _].
        rewrite Ew in HwS. have ES' := det _ _ HS' _ HwS. subst S'.
        move: (V _ _ HS') => /= [HVf _].
        case: (HVf _ _ H0) => HwT HE0.
        have Hown : cupd x0 (Some S2) Δm w0 <> None.
          rewrite /cupd. case: (w0 =P x0) => _ //. by rewrite HwT.
        have Hsub := owned_cupd_sub (Δ := Δm) (x0 := x0) (o := Some S2).
        split.
        -- rewrite Ey. case: (Hag w0) => [E|E]; first by rewrite E in HwT.
           by rewrite E.
        -- rewrite Ew Ey. apply: IH HE0.
           ++ apply: agree_cupd => //.
              ** apply: agree_cupd => //. by rewrite HS'.
              ** apply: inj_on_sub Hinj. apply: Hsub. by rewrite HS'.
           ++ apply: inj_on_sub (inj_on_sub _ Hinj).
              ** apply: owned_cupd_sub. exact: Hown.
              ** apply: Hsub. by rewrite HS'.
      * move=> P'' HT.
        case: (ltsb_ren_inv2 HT erefl) => x0 [P0'' [Ew -> H0]].
        have Hof0 : offers ADelS x0 P by right; exists P0''.
        case: (C _ _ Hof0) => S' [HS' _].
        rewrite Ew in HwS. have ES' := det _ _ HS' _ HwS. subst S'.
        move: (V _ _ HS') => /= [_ HVb].
        have HE0 := HVb _ H0.
        rewrite Ew. apply: IH HE0.
        -- do 2 apply: agree_scons. apply: agree_cupd => //. by rewrite HS'.
        -- do 2 apply: inj_scons. apply: inj_on_sub Hinj.
           apply: owned_cupd_sub. by rewrite HS'.
    + (* SRecv *)
      move=> P'' HT.
      case: (ltsr_ren_inv2 HT erefl) => x0 [P0'' [Ew -> H0]].
      have Hof0 : offers ADelR x0 P by exists P0''.
      case: (C _ _ Hof0) => S' [HS' _].
      rewrite Ew in HwS. have ES' := det _ _ HS' _ HwS. subst S'.
      move: (V _ _ HS') => /= HV.
      have HE0 := HV _ H0.
      rewrite Ew. apply: IH HE0.
      * apply: agree_scons. apply: agree_cupd => //. by rewrite HS'.
      * apply: inj_scons. apply: inj_on_sub Hinj.
        apply: owned_cupd_sub. by rewrite HS'.
  - (* parallel descent: push the split forward *)
    move=> A B EAB.
    case: (subst_inv_par EAB) => A0 [B0 [E1 E2 E3]]. subst.
    case: (D _ _ erefl) => Δa [Δb [Hsp H1 H2]].
    exists (pleft s Δn Δb), (pfwd s Δb).
    split; first exact: pfwd_split Hag Hsp.
    + apply: IH H1; first exact: agree_pleft Hag Hinj Hsp.
      exact: inj_onL Hinj Hsp.
    + apply: IH H2; first exact: agree_pfwdR Hinj Hsp.
      exact: inj_onR Hinj Hsp.
  - (* cut *)
    move=> Q EQ.
    case: (subst_inv_res EQ) => Q0 [E1 E2]. subst.
    case: (X _ erefl) => S HS.
    exists S. apply: IH HS.
    + exact: agree_cext.
    + exact: inj_cext.
  - (* one internal step of the image *)
    move=> P' Hst.
    case: (ltst_ren_inv2 Hst erefl) => R0 [-> H0].
    exact: IH (St _ H0).
Qed.

Print Assumptions EsemT_ren.

(** ** Frame instances of renaming closure *)

Lemma agree_shift n (Δ : sctx n) o : agree shift Δ (scons o Δ).
Proof. move=> z. by right. Qed.

Lemma inj_shift n (Δ : sctx n) : inj_on (shift : ren n n.+1) Δ.
Proof.
  move=> z1 z2 _ _ E.
  exact: (f_equal (fun c : option (ch n) => if c is Some u then u else z1) E).
Qed.

Lemma agree_shift2 n (Δ : sctx n) o1 o2 :
  agree (shift \o shift) Δ (scons o1 (scons o2 Δ)).
Proof. move=> z. by right. Qed.

Lemma inj_shift2 n (Δ : sctx n) : inj_on (shift \o shift : ren n n.+2) Δ.
Proof.
  move=> z1 z2 _ _ E.
  have E1 := f_equal (fun c : option (ch n.+1) => if c is Some u then u else shift z1) E.
  exact: (f_equal (fun c : option (ch n) => if c is Some u then u else z1) E1).
Qed.

Lemma EsemT_shift k n (Δ : sctx n) o (P : proc n) :
  EsemT k Δ P -> EsemT k (scons o Δ) (subst_proc shift P).
Proof. apply: EsemT_ren; [exact: agree_shift | exact: inj_shift]. Qed.

Lemma EsemT_shift2 k n (Δ : sctx n) o1 o2 (P : proc n) :
  EsemT k Δ P ->
  EsemT k (scons o1 (scons o2 Δ)) (subst_proc (shift \o shift) P).
Proof. apply: EsemT_ren; [exact: agree_shift2 | exact: inj_shift2]. Qed.

(** ** Bound-send parallel inversion, with residues *)
Lemma ltsb_par_inv2 n (y : ch n) P1 P2 R :
  ltsb y (P1 ∥ P2) R ->
  (exists P1', R = P1' ∥ subst_proc (shift \o shift) P2 /\ ltsb y P1 P1') \/
  (exists P2', R = subst_proc (shift \o shift) P1 ∥ P2' /\ ltsb y P2 P2').
Proof.
  move=> H. tau_inv H.
  - left. eexists. split; [reflexivity | assumption].
  - right. eexists. split; [reflexivity | assumption].
Qed.

(** ** [split] gives weakenings *)
Lemma split_leL n (Δ Δ1 Δ2 : sctx n) : split Δ Δ1 Δ2 -> ctx_le Δ1 Δ.
Proof. move=> Hs x S H1. by case: (split_someL Hs H1). Qed.

Lemma split_leR n (Δ Δ1 Δ2 : sctx n) : split Δ Δ1 Δ2 -> ctx_le Δ2 Δ.
Proof. move=> /split_sym. exact: split_leL. Qed.


(** ** Semantic parallel composition *)
Lemma par_combineT k : forall n (Δ Δ1 Δ2 : sctx n) (P Q : proc n),
  split Δ Δ1 Δ2 -> EsemT k Δ1 P -> EsemT k Δ2 Q -> EsemT k Δ (P ∥ Q).
Proof.
  elim: k => [//|k IH] n Δ Δ1 Δ2 P Q Hs HP HQ.
  case: (HP) => CP VP DP XP StP.
  case: (HQ) => CQ VQ DQ XQ StQ.
  have HPk := EsemT_antitone HP.
  have HQk := EsemT_antitone HQ.
  split.
  - (* conformance: an offer of the composition is an offer of a side *)
    move=> a x Hof.
    have side : offers a x P \/ offers a x Q.
      case: a Hof => /=.
      + move=> [P' HT].
        case: (ltsc_par_inv HT) => [[P'' [_ H]]|[Q'' [_ H]]];
          [by left; exists P'' | by right; exists Q''].
      + move=> [P' HT].
        case: (ltsw_par_inv HT) => [[P'' [_ H]]|[Q'' [_ H]]];
          [by left; exists P'' | by right; exists Q''].
      + move=> [[z [P' HT]]|[P' HT]].
        * case: (ltsf_par_inv HT) => [[P'' [_ H]]|[Q'' [_ H]]];
            [by left; left; exists z, P'' | by right; left; exists z, Q''].
        * case: (ltsb_par_inv HT) => [[P'' H]|[Q'' H]];
            [by left; right; exists P'' | by right; right; exists Q''].
      + move=> [P' HT].
        case: (ltsr_par_inv HT) => [[P'' [_ H]]|[Q'' [_ H]]];
          [by left; exists P'' | by right; exists Q''].
    case: side => [HofS | HofS].
    + case: (CP _ _ HofS) => S [HS Ha]. exists S. split=> //.
      by case: (split_someL Hs HS).
    + case: (CQ _ _ HofS) => S [HS Ha]. exists S. split=> //.
      by case: (split_someR Hs HS).
  - (* value clauses *)
    move=> x S HxS.
    case EL : (Δ1 x) => [S1|].
    + (* left side owns x *)
      have [ED ER] := split_someL Hs EL.
      have ES : S1 = S by rewrite HxS in ED; case: ED.
      subst S1. move: (VP _ _ EL). clear EL ED.
      case: S HxS => [| |T S2|T S2] HxS /= HV.
      * move=> P'' HT.
        case: (ltsc_par_inv HT) => [[P1' [-> H]]|[Q1' [_ H]]].
        -- apply: IH (HV _ H) HQk. exact: split_cupd.
        -- exfalso. case: (CQ AClose x (ex_intro _ _ H)) => S' [HS' _].
           by rewrite ER in HS'.
      * move=> P'' HT.
        case: (ltsw_par_inv HT) => [[P1' [-> H]]|[Q1' [_ H]]].
        -- apply: IH (HV _ H) HQk. exact: split_cupd.
        -- exfalso. case: (CQ AWait x (ex_intro _ _ H)) => S' [HS' _].
           by rewrite ER in HS'.
      * split.
        -- move=> y P'' HT.
           case: (ltsf_par_inv HT) => [[P1' [-> H]]|[Q1' [_ H]]].
           ++ case: HV => [HVf _]. case: (HVf _ _ H) => HyT HE'.
              split; first by case: (split_someL Hs HyT).
              apply: IH HE' HQk.
              apply: split_cupd; first exact: split_cupd.
              by case: (split_someL Hs HyT).
           ++ exfalso.
              case: (CQ ADelS x (or_introl (ex_intro _ _ (ex_intro _ _ H))))
                => S' [HS' _]. by rewrite ER in HS'.
        -- move=> P'' HT.
           case: (ltsb_par_inv2 HT) => [[P1' [-> H]]|[Q1' [_ H]]].
           ++ case: HV => [_ HVb].
              apply: IH (HVb _ H) _.
              ** do 2 apply: split_scons. exact: split_cupd.
              ** exact: EsemT_shift2 HQk.
           ++ exfalso.
              case: (CQ ADelS x (or_intror (ex_intro _ _ H)))
                => S' [HS' _]. by rewrite ER in HS'.
      * move=> P'' HT.
        case: (ltsr_par_inv HT) => [[P1' [-> H]]|[Q1' [_ H]]].
        -- apply: IH (HV _ H) _.
           ++ apply: split_scons. exact: split_cupd.
           ++ exact: EsemT_shift HQk.
        -- exfalso. case: (CQ ADelR x (ex_intro _ _ H)) => S' [HS' _].
           by rewrite ER in HS'.
    + (* right side owns x *)
      have ER : Δ2 x = Some S.
        case: (Hs x) => [[Ha Hb]|[Ha Hb]].
        - by rewrite Ha HxS in EL.
        - by rewrite Ha.
      move: (VQ _ _ ER).
      case: S HxS ER => [| |T S2|T S2] HxS ER /= HV.
      * move=> P'' HT.
        case: (ltsc_par_inv HT) => [[P1' [_ H]]|[Q1' [-> H]]].
        -- exfalso. case: (CP AClose x (ex_intro _ _ H)) => S' [HS' _].
           by rewrite EL in HS'.
        -- apply: IH HPk (HV _ H).
           apply: split_sym. apply: split_cupd; [exact: split_sym Hs | exact: EL].
      * move=> P'' HT.
        case: (ltsw_par_inv HT) => [[P1' [_ H]]|[Q1' [-> H]]].
        -- exfalso. case: (CP AWait x (ex_intro _ _ H)) => S' [HS' _].
           by rewrite EL in HS'.
        -- apply: IH HPk (HV _ H).
           apply: split_sym. apply: split_cupd; [exact: split_sym Hs | exact: EL].
      * split.
        -- move=> y P'' HT.
           case: (ltsf_par_inv HT) => [[P1' [_ H]]|[Q1' [-> H]]].
           ++ exfalso.
              case: (CP ADelS x (or_introl (ex_intro _ _ (ex_intro _ _ H))))
                => S' [HS' _]. by rewrite EL in HS'.
           ++ case: HV => [HVf _]. case: (HVf _ _ H) => HyT HE'.
              split; first by case: (split_someR Hs HyT).
              apply: IH HPk HE'.
              apply: split_sym.
              apply: split_cupd; last by case: (split_someR Hs HyT).
              apply: split_cupd; [exact: split_sym Hs | exact: EL].
        -- move=> P'' HT.
           case: (ltsb_par_inv2 HT) => [[P1' [_ H]]|[Q1' [-> H]]].
           ++ exfalso.
              case: (CP ADelS x (or_intror (ex_intro _ _ H)))
                => S' [HS' _]. by rewrite EL in HS'.
           ++ case: HV => [_ HVb].
              apply: IH _ (HVb _ H).
              ** apply: split_sym. do 2 apply: split_scons.
                 apply: split_cupd; [exact: split_sym Hs | exact: EL].
              ** exact: EsemT_shift2 HPk.
      * move=> P'' HT.
        case: (ltsr_par_inv HT) => [[P1' [_ H]]|[Q1' [-> H]]].
        -- exfalso. case: (CP ADelR x (ex_intro _ _ H)) => S' [HS' _].
           by rewrite EL in HS'.
        -- apply: IH _ (HV _ H).
           ++ apply: split_sym. apply: split_scons.
              apply: split_cupd; [exact: split_sym Hs | exact: EL].
           ++ exact: EsemT_shift HPk.
  - (* parallel-descent clause *)
    move=> A B [E1 E2]. subst.
    by exists Δ1, Δ2.
  - (* cut clause: a parallel is not a restriction *)
    by move=> Q0 E.
  - (* one internal step: it happens on a side *)
    move=> P' Hst.
    case: (ltst_par_inv Hst) => [[P1' [-> H]]|[Q1' [-> H]]].
    + exact: IH Hs (StP _ H) HQk.
    + exact: IH Hs HPk (StQ _ H).
Qed.

Print Assumptions par_combineT.

(** ** Semantic synchronization: close against wait

    Two value-clause consumptions; the budget drops by two.  The
    subjects are distinct because their protocols differ. *)
Lemma syncC_sem k n (Δ : sctx n) (x y : ch n) (P R : proc n) :
  syncC x y P R -> EsemT k.+2 Δ P ->
  Δ x = Some SClose -> Δ y = Some SWait ->
  EsemT k (cupd y None (cupd x None Δ)) R.
Proof.
  move=> HS HE Hx Hy.
  case: (syncC_seq HS) => Pc [H1 H2].
  case: HE => _ V _ _ _.
  move: (V _ _ Hx) => /= HV.
  have HEc := HV _ H1.
  case: HEc => _ Vc _ _ _.
  have Hy' : cupd x None Δ y = Some SWait.
    rewrite /cupd. case: (y =P x) => [E|_]; last by rewrite Hy.
    by rewrite E Hx in Hy.
  move: (Vc _ _ Hy') => /= HVc.
  exact: HVc _ H2.
Qed.

Print Assumptions syncC_sem.
