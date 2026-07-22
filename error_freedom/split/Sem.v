(** * Semantic transport for relation v3 (typed ✓)

    [agree]/[inj_on] over the semantic slots, conformance transport
    through the uniform endpoint lookup [sat], the guarded backward τ,
    and the substitution lemma. *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import Base Types Proc LTS Err
  Typing LogRel Equiv.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope pol_scope.

(** ** The transport conditions *)

Definition agree {m n : nat} (s : ren m n) (Δm : sctxP m) (Δn : sctxP n)
  : Prop :=
  forall x, Δm x = None \/ Δn (s x) = Δm x.

Definition inj_on {m n : nat} (s : ren m n) (Δm : sctxP m) : Prop :=
  forall x1 x2,
    Δm x1 <> None -> Δm x2 <> None -> s x1 = s x2 -> x1 = x2.

Lemma inj_on_sub m n (s : ren m n) (ΔA ΔB : sctxP m) :
  (forall x, ΔA x <> None -> ΔB x <> None) ->
  inj_on s ΔB -> inj_on s ΔA.
Proof. move=> Hsub Hinj x1 x2 H1 H2. exact: Hinj (Hsub _ H1) (Hsub _ H2). Qed.

Lemma owned_scupd_sub m (Δ : sctxP m) (x0 : ch m) e :
  Δ x0 <> None ->
  forall x, scupd x0 e Δ x <> None -> Δ x <> None.
Proof.
  move=> Hx x. rewrite /scupd. by case: (x =P x0) => [->|_].
Qed.

Lemma agree_scupd m n (s : ren m n) (Δm : sctxP m) (Δn : sctxP n)
    (x0 : ch m) e :
  agree s Δm Δn -> inj_on s Δm -> Δm x0 <> None ->
  agree s (scupd x0 e Δm) (scupd (s x0) e Δn).
Proof.
  move=> Hag Hinj Hx x. rewrite /scupd.
  case: (x =P x0) => [-> | Hne].
  - by rewrite eqxx; right.
  - case E : (Δm x) => [S0|]; last by left.
    right.
    have Hne2 : (s x == s x0) = false.
      apply/eqP => Es. apply: Hne. apply: Hinj Es => //.
      by rewrite E.
    rewrite Hne2.
    by case: (Hag x); rewrite E.
Qed.

Lemma agree_sscons m n (s : ren m n) (Δm : sctxP m) (Δn : sctxP n) e :
  agree s Δm Δn ->
  agree (up_ch s) (scons e Δm) (scons e Δn).
Proof.
  move=> Hag [x|] /=.
  - by case: (Hag x) => [E|E]; [left | right].
  - by right.
Qed.

Lemma inj_sscons m n (s : ren m n) (Δm : sctxP m) e :
  inj_on s Δm -> inj_on (up_ch s) (scons e Δm).
Proof.
  move=> Hinj [x1|] [x2|] //= H1 H2 E.
  have Es := f_equal (fun c : option (ch n) => if c is Some u then u else s x1) E.
  by rewrite (Hinj _ _ H1 H2 Es).
Qed.

(** ** Conformance transports (uniform through [sat]) *)

Lemma sat_agree m n (s : ren m n) (Δm : sctxP m) (Δn : sctxP n)
    (c : pch m) S0 :
  agree s Δm Δn -> sat Δm c = Some S0 -> sat Δn (pren s c) = Some S0.
Proof.
  move=> Hag. rewrite /sat /=.
  case E : (Δm c.1) => [e|] // Hs.
  case: (Hag c.1) => [E'|E']; first by rewrite E' in E.
  by rewrite E' E.
Qed.

Lemma conformV_ren m n (s : ren m n) (Δm : sctxP m) (Δn : sctxP n)
    (P : procP m) :
  agree s Δm Δn ->
  conformV Δm P -> conformV Δn (psubst s P).
Proof.
  move=> Hag C1 a C Hof.
  case: (offersP_ren_inv Hof) => c [-> Hof0].
  case: (C1 _ _ Hof0) => S0 [HS0 Ha].
  exists S0. split=> //. exact: sat_agree Hag HS0.
Qed.

Lemma conformD_ren m n (s : ren m n) (Δm : sctxP m) (Δn : sctxP n)
    (P : procP m) :
  agree s Δm Δn ->
  conformD Δm P -> conformD Δn (psubst s P).
Proof.
  elim: P n s Δm Δn => //=
    [ m' | m' c K IH | m' c K IH | m' B IH | m' A IHA B IHB
    | m' c r K IH | m' c d K IH | m' c b K IH
    | m' c K1 IH1 K2 IH2 ] n s Δm Δn Hag HD.
  - split=> //. exact (conformV_ren Hag (proj1 HD)).
  - split=> //. exact (conformV_ren Hag (proj1 HD)).
  - split=> //. exact (conformV_ren Hag (proj1 HD)).
  - split.
    + exact (conformV_ren Hag (proj1 HD)).
    + case: (proj2 HD) => S0 HD'.
      exists S0. apply: (IH _ _ _ _ _ HD'). exact: agree_sscons.
  - split.
    + exact (conformV_ren Hag (proj1 HD)).
    + split.
      * exact (IHA _ _ _ _ Hag (proj1 (proj2 HD))).
      * exact (IHB _ _ _ _ Hag (proj2 (proj2 HD))).
  - split=> //. exact (conformV_ren Hag (proj1 HD)).
  - split=> //. exact (conformV_ren Hag (proj1 HD)).
  - split=> //. exact (conformV_ren Hag (proj1 HD)).
  - split=> //. exact (conformV_ren Hag (proj1 HD)).
Qed.

(** ** Backward τ under a coverage guard

    Full injectivity is unavailable at the substitution lemma's call
    sites (a collapse [scons y id] always merges [zero] with
    [shift y]).  What holds instead: P only offers at names satisfying
    a guard [G] (in use: ownership, from P's conformance), and [s] is
    injective on [G].  Synchronization subjects are offers, so their
    preimages fall in [G] and are identified. *)
Lemma ltstP_ren_inv_cov n' X R (H : ltstP X R) :
  forall m (s : ren m n') (P : procP m) (G : ch m -> Prop),
    (forall a (c : pch m), offersP a c P -> G c.1) ->
    (forall x1 x2, G x1 -> G x2 -> s x1 = s x2 -> x1 = x2) ->
    psubst s P = X ->
    exists P0, R = psubst s P0 /\ ltstP P P0.
Proof.
  elim: H => {n' X R}.
  - move=> n' A A' B _ IH m s P G HG GInj EP.
    case: (psubst_inv_par EP) => A0 [B0 [EP2 EA EB]]. subst P. rewrite EB.
    have HG' : forall a (c : pch m), offersP a c A0 -> G c.1.
      move=> a c Hof. exact: (HG _ _ (offersP_liftL B0 Hof)).
    case: (IH _ _ _ _ HG' GInj (esym EA)) => P0 [-> H0].
    exists (P0 ∥ B0). split=> //=. exact: PT_ParL H0.
  - move=> n' A B B' _ IH m s P G HG GInj EP.
    case: (psubst_inv_par EP) => A0 [B0 [EP2 EA EB]]. subst P. rewrite EA.
    have HG' : forall a (c : pch m), offersP a c B0 -> G c.1.
      move=> a c Hof. exact: (HG _ _ (offersP_liftR A0 Hof)).
    case: (IH _ _ _ _ HG' GInj (esym EB)) => P0 [-> H0].
    exists (A0 ∥ P0). split=> //=. exact: PT_ParR H0.
  - move=> n' B B' _ IH m s P G HG GInj EP.
    case: (psubst_inv_res EP) => B0 [EP2 EB]. subst P.
    pose G' := fun w : ch m.+1 => if w is Some x then G x else True.
    have HG' : forall a (c : pch m.+1), offersP a c B0 -> G' c.1.
      move=> a [cn cr]. case: cn => [x|] Hof //=.
      exact: (HG _ _ (offersP_liftRes (c := (x, cr)) Hof)).
    have GInj' : forall w1 w2, G' w1 -> G' w2 ->
        up_ch s w1 = up_ch s w2 -> w1 = w2.
      move=> [x1|] [x2|] //= Hg1 Hg2 E.
      have Es := f_equal
        (fun c : ch n'.+1 => if c is Some u then u else s x1) E.
      by rewrite (GInj _ _ Hg1 Hg2 Es).
    case: (IH _ _ _ _ HG' GInj' (esym EB)) => P0 [-> H0].
    exists ((ν) P0). split=> //=. exact: PT_Res H0.
  - move=> n' C A A' B B' Hc Hw m s P G HG GInj EP.
    case: (psubst_inv_par EP) => A0 [B0 [EP2 EA EB]]. subst P.
    case: (ltscP_ren_inv Hc (esym EA)) => c [PA [E1 -> HA]].
    case: (ltswP_ren_inv Hw (esym EB)) => w [PB [E2 -> HB]].
    have Gc : G c.1.
      apply: (HG AClose). apply: (offersP_liftL B0). by exists PA.
    have Gw : G w.1.
      apply: (HG AWait). apply: (offersP_liftR A0). by exists PB.
    have Ew : w = pflip c.
      case: w E2 Gw {HB} => wn wr E2 Gw.
      case: c E1 Gc {HA} => cn cr E1 Gc'.
      move: E2. rewrite E1 /= => -[E2n E2r].
      have En := GInj _ _ Gw Gc' (esym E2n).
      move: En => /= En. by rewrite En -E2r.
    subst w.
    exists (PA ∥ PB). split=> //=. exact: PT_CW HA HB.
  - move=> n' C A A' B B' Hw Hc m s P G HG GInj EP.
    case: (psubst_inv_par EP) => A0 [B0 [EP2 EA EB]]. subst P.
    case: (ltswP_ren_inv Hw (esym EA)) => w [PA [E2 -> HA]].
    case: (ltscP_ren_inv Hc (esym EB)) => c [PB [E1 -> HB]].
    have Gc : G c.1.
      apply: (HG AClose). apply: (offersP_liftR A0). by exists PB.
    have Gw : G w.1.
      apply: (HG AWait). apply: (offersP_liftL B0). by exists PA.
    have Ew : w = pflip c.
      case: w E2 Gw {HA} => wn wr E2 Gw.
      case: c E1 Gc {HB} => cn cr E1 Gc'.
      move: E2. rewrite E1 /= => -[E2n E2r].
      have En := GInj _ _ Gw Gc' (esym E2n).
      move: En => /= En. by rewrite En -E2r.
    subst w.
    exists (PA ∥ PB). split=> //=. exact: PT_WC HA HB.
  - move=> n' C D A A' B B' Hf Hr m s P G HG GInj EP.
    case: (psubst_inv_par EP) => A0 [B0 [EP2 EA EB]]. subst P.
    case: (ltsfP_ren_inv Hf (esym EA)) => c [d [PA [E1 ED -> HA]]].
    case: (ltsrP_ren_inv Hr (esym EB)) => w [PB [E2 ER Hu]].
    have Gc : G c.1.
      apply: (HG ADelS). apply: (offersP_liftL B0). left.
      by exists d, PA.
    have Gw : G w.1.
      apply: (HG ADelR). apply: (offersP_liftR A0).
      exists (w.1, D.2), (psubst (scons w.1 id_ren) PB). exact: (Hu w.1).
    have Ew : w = pflip c.
      case: w E2 Gw Hu => wn wr E2 Gw Hu.
      case: c E1 Gc {HA} => cn cr E1 Gc'.
      move: E2. rewrite E1 /= => -[E2n E2r].
      have En := GInj _ _ Gw Gc' (esym E2n).
      move: En => /= En. by rewrite En -E2r.
    subst w.
    exists (PA ∥ psubst (scons d.1 id_ren) PB). split=> /=.
    + congr (_ ∥ _). rewrite ER ED !psubst_comp.
      by apply: psubst_ext => -[z|].
    + apply: PT_DR HA _.
      have Ed : D.2 = d.2 by rewrite ED.
      have Hu' := Hu d.1. rewrite Ed -surjective_pairing in Hu'.
      exact: Hu'.
  - move=> n' C D A A' B B' Hr Hf m s P G HG GInj EP.
    case: (psubst_inv_par EP) => A0 [B0 [EP2 EA EB]]. subst P.
    case: (ltsrP_ren_inv Hr (esym EA)) => w [PA [E2 ER Hu]].
    case: (ltsfP_ren_inv Hf (esym EB)) => c [d [PB [E1 ED -> HB]]].
    have Gc : G c.1.
      apply: (HG ADelS). apply: (offersP_liftR A0). left.
      by exists d, PB.
    have Gw : G w.1.
      apply: (HG ADelR). apply: (offersP_liftL B0).
      exists (w.1, D.2), (psubst (scons w.1 id_ren) PA). exact: (Hu w.1).
    have Ew : w = pflip c.
      case: w E2 Gw Hu => wn wr E2 Gw Hu.
      case: c E1 Gc {HB} => cn cr E1 Gc'.
      move: E2. rewrite E1 /= => -[E2n E2r].
      have En := GInj _ _ Gw Gc' (esym E2n).
      move: En => /= En. by rewrite En -E2r.
    subst w.
    exists (psubst (scons d.1 id_ren) PA ∥ PB). split=> /=.
    + congr (_ ∥ _). rewrite ER ED !psubst_comp.
      by apply: psubst_ext => -[z|].
    + apply: PT_RD _ HB.
      have Ed : D.2 = d.2 by rewrite ED.
      have Hu' := Hu d.1. rewrite Ed -surjective_pairing in Hu'.
      exact: Hu'.
  - move=> n' C r A A' B B' Hb Hr m s P G HG GInj EP.
    case: (psubst_inv_par EP) => A0 [B0 [EP2 EA EB]]. subst P.
    case: (ltsbP_ren_inv Hb (esym EA)) => c [PA [E1 -> HA]].
    have EBs : psubst shift B = psubst (up_ch s) (psubst shift B0).
      by rewrite EB psubst_shift_comm.
    move: Hr. rewrite EBs => Hr.
    case: (ltsrP_ren_inv Hr erefl) => w [PB [E2 ER Hu]].
    have Gc : G c.1.
      apply: (HG ADelS). apply: (offersP_liftL B0). right.
      by exists r, PA.
    have [w0 [Eww Gw]] : exists w0 : pch m, w = pshift w0 /\ G w0.1.
      have Hofs : offersP ADelR w (psubst shift B0).
        exists (w.1, r), (psubst (scons w.1 id_ren) PB). exact: (Hu w.1).
      case: (offersP_ren_inv Hofs) => w0 [Ew0 Hof0].
      exists w0. split=> //. exact: (HG _ _ (offersP_liftR A0 Hof0)).
    have Ew0 : w0 = pflip c.
      case: w0 Eww Gw => wn wr Eww Gw.
      case: c E1 Gc {HA} => cn cr E1 Gc'.
      move: E2. rewrite Eww E1 /= => -[E2n E2r].
      have En := GInj _ _ Gw Gc' (esym E2n).
      move: En => /= En. by rewrite En -E2r.
    subst w0. subst w.
    exists ((ν) (PA ∥ psubst (scons zero id_ren) PB)). split=> /=.
    + congr PRes. congr (_ ∥ _). rewrite ER /= !psubst_comp.
      by apply: psubst_ext => -[z|].
    + apply: PT_BR HA _.
      exact (Hu zero).
  - move=> n' C r A A' B B' Hr Hb m s P G HG GInj EP.
    case: (psubst_inv_par EP) => A0 [B0 [EP2 EA EB]]. subst P.
    case: (ltsbP_ren_inv Hb (esym EB)) => c [PB [E1 -> HB]].
    have EAs : psubst shift A = psubst (up_ch s) (psubst shift A0).
      by rewrite EA psubst_shift_comm.
    move: Hr. rewrite EAs => Hr.
    case: (ltsrP_ren_inv Hr erefl) => w [PA [E2 ER Hu]].
    have Gc : G c.1.
      apply: (HG ADelS). apply: (offersP_liftR A0). right.
      by exists r, PB.
    have [w0 [Eww Gw]] : exists w0 : pch m, w = pshift w0 /\ G w0.1.
      have Hofs : offersP ADelR w (psubst shift A0).
        exists (w.1, r), (psubst (scons w.1 id_ren) PA). exact: (Hu w.1).
      case: (offersP_ren_inv Hofs) => w0 [Ew0 Hof0].
      exists w0. split=> //. exact: (HG _ _ (offersP_liftL B0 Hof0)).
    have Ew0 : w0 = pflip c.
      case: w0 Eww Gw => wn wr Eww Gw.
      case: c E1 Gc {HB} => cn cr E1 Gc'.
      move: E2. rewrite Eww E1 /= => -[E2n E2r].
      have En := GInj _ _ Gw Gc' (esym E2n).
      move: En => /= En. by rewrite En -E2r.
    subst w0. subst w.
    exists ((ν) (psubst (scons zero id_ren) PA ∥ PB)). split=> /=.
    + congr PRes. congr (_ ∥ _). rewrite ER /= !psubst_comp.
      by apply: psubst_ext => -[z|].
    + apply: PT_RB _ HB.
      exact (Hu zero).
  - move=> n' C b A A' B B' Hs Hbr m s P G HG GInj EP.
    case: (psubst_inv_par EP) => A0 [B0 [EP2 EA EB]]. subst P.
    case: (ltsselP_ren_inv Hs (esym EA)) => c [PA [E1 -> HA]].
    case: (ltsbrP_ren_inv Hbr (esym EB)) => w [PB [E2 -> HB]].
    have Gc : G c.1.
      apply: (HG ASel). apply: (offersP_liftL B0). by exists b, PA.
    have Gw : G w.1.
      apply: (HG ABra). apply: (offersP_liftR A0). by exists b, PB.
    have Ew : w = pflip c.
      case: w E2 Gw {HB} => wn wr E2 Gw.
      case: c E1 Gc {HA} => cn cr E1 Gc'.
      move: E2. rewrite E1 /= => -[E2n E2r].
      have En := GInj _ _ Gw Gc' (esym E2n).
      move: En => /= En. by rewrite En -E2r.
    subst w.
    exists (PA ∥ PB). split=> //=. exact: PT_SB HA HB.
  - move=> n' C b A A' B B' Hbr Hs m s P G HG GInj EP.
    case: (psubst_inv_par EP) => A0 [B0 [EP2 EA EB]]. subst P.
    case: (ltsbrP_ren_inv Hbr (esym EA)) => w [PA [E2 -> HA]].
    case: (ltsselP_ren_inv Hs (esym EB)) => c [PB [E1 -> HB]].
    have Gc : G c.1.
      apply: (HG ASel). apply: (offersP_liftR A0). by exists b, PB.
    have Gw : G w.1.
      apply: (HG ABra). apply: (offersP_liftL B0). by exists b, PA.
    have Ew : w = pflip c.
      case: w E2 Gw {HA} => wn wr E2 Gw.
      case: c E1 Gc {HB} => cn cr E1 Gc'.
      move: E2. rewrite E1 /= => -[E2n E2r].
      have En := GInj _ _ Gw Gc' (esym E2n).
      move: En => /= En. by rewrite En -E2r.
    subst w.
    exists (PA ∥ PB). split=> //=. exact: PT_BS HA HB.
Qed.

Print Assumptions ltstP_ren_inv_cov.

(** ** Payload self-reference is impossible *)
Fixpoint stysz (S : sty) : nat :=
  match S with
  | SClose | SWait => 1
  | SSend a b | SRecv a b => (stysz a + stysz b).+1
  | SSel a b | SBra a b => (stysz a + stysz b).+1
  end.

Lemma ssend_neqT T S2 : T = SSend T S2 -> False.
Proof.
  move=> E. have := f_equal stysz E. rewrite /= => /eqP.
  by rewrite -[X in X == _]addn0 -addnS eqn_add2l.
Qed.

(** ** Pointwise context extensionality *)

Lemma conformV_ext m (Δ1 Δ2 : sctxP m) (P : procP m) :
  (forall x, Δ1 x = Δ2 x) -> conformV Δ1 P -> conformV Δ2 P.
Proof.
  move=> Hd C a c Hof. case: (C _ _ Hof) => S0 [HS0 Ha].
  exists S0. split=> //. by rewrite /sat -Hd.
Qed.

Lemma conformD_ext m (Δ1 Δ2 : sctxP m) (P : procP m) :
  (forall x, Δ1 x = Δ2 x) -> conformD Δ1 P -> conformD Δ2 P.
Proof.
  elim: P Δ1 Δ2 => //=
    [ m' | m' c K IH | m' c K IH | m' B IH | m' A IHA B IHB
    | m' c r K IH | m' c d K IH | m' c b K IH
    | m' c K1 IH1 K2 IH2 ] Δ1 Δ2 Hd HD.
  - split=> //. exact (conformV_ext Hd (proj1 HD)).
  - split=> //. exact (conformV_ext Hd (proj1 HD)).
  - split=> //. exact (conformV_ext Hd (proj1 HD)).
  - split.
    + exact (conformV_ext Hd (proj1 HD)).
    + case: (proj2 HD) => S0 HD'. exists S0.
      have Hd' : forall x : ch m'.+1,
          scons (Some (SBoth S0)) Δ1 x = scons (Some (SBoth S0)) Δ2 x.
        by move=> [x|] //=; rewrite Hd.
      exact: IH Hd' HD'.
  - split.
    + exact (conformV_ext Hd (proj1 HD)).
    + split.
      * exact (IHA _ _ Hd (proj1 (proj2 HD))).
      * exact (IHB _ _ Hd (proj2 (proj2 HD))).
  - split=> //. exact (conformV_ext Hd (proj1 HD)).
  - split=> //. exact (conformV_ext Hd (proj1 HD)).
  - split=> //. exact (conformV_ext Hd (proj1 HD)).
  - split=> //. exact (conformV_ext Hd (proj1 HD)).
Qed.

Lemma EsemP_ext k : forall m (Δ1 Δ2 : sctxP m) (P : procP m),
  (forall x, Δ1 x = Δ2 x) -> EsemP k Δ1 P -> EsemP k Δ2 P.
Proof.
  elim: k => [//|k IH] m Δ1 Δ2 P Hd [C V St]. split.
  - exact: conformD_ext Hd C.
  - move=> w rw S HwS.
    have HwS1 : Δ1 w = Some (SSep rw S) by rewrite Hd.
    move: (V _ _ _ HwS1).
    case: S HwS HwS1 => [| |T S2|T S2|S1 S2|S1 S2] HwS HwS1 /= HV.
    + move=> P' HT. apply: IH (HV _ HT).
      move=> x. rewrite /scupd. by case: (x =P w).
    + move=> P' HT. apply: IH (HV _ HT).
      move=> x. rewrite /scupd. by case: (x =P w).
    + case: HV => HVf HVb. split.
      * move=> y rd P' HT. case: (HVf _ _ _ HT) => e [He Hs HE].
        exists e. split=> //; first by rewrite -Hd.
        apply: IH HE.
        move=> x. rewrite /scupd.
        by case: (x =P y) => // _; case: (x =P w).
      * move=> r' P' HT. apply: IH (HVb _ _ HT).
        move=> [x|] //=. rewrite /scupd.
        by case: ((x : ch m) =P w).
    + case: HV => HVc HVs. split.
      * move=> y rd P' HT. case: (HVc _ _ _ HT) => Hf Hz. split.
        -- move=> Hy2. have Hy1 : Δ1 y = None by rewrite Hd.
           apply: IH (Hf Hy1).
           move=> x. rewrite /scupd.
           by case: (x =P y) => // _; case: (x =P w).
        -- move=> Hy2.
           have Hy1 : Δ1 y = Some (SSep (flipp rd) (dual T))
             by rewrite Hd.
           apply: IH (Hz Hy1).
           move=> x. rewrite /scupd.
           by case: (x =P y) => // _; case: (x =P w).
      * move=> rd P'' HT. apply: IH (HVs _ _ HT).
        move=> [x|] //=. rewrite /scupd.
        by case: ((x : ch m) =P w).
    + move=> b P' HT. apply: IH (HV _ _ HT).
      move=> x. rewrite /scupd. by case: (x =P w).
    + move=> b P' HT. case: (HV _ _ HT) => Δ' [Hev HE].
      exists Δ'. split.
      * move=> x. case: (Hev x) => [E|[S0 [S0' [E E']]]].
        -- left. by rewrite E Hd.
        -- right. exists S0, S0'. by rewrite -Hd.
      * apply: IH HE.
        move=> x. rewrite /scupd. by case: (x =P w).
  - move=> P' Hst. case: (St _ Hst) => Δ' [Hev HE].
    exists Δ'. split=> //.
    move=> x. case: (Hev x) => [E|[S0 [S0' [E E']]]].
    + left. by rewrite E Hd.
    + right. exists S0, S0'. by rewrite -Hd.
Qed.

(** ** The slot order

    Target contexts may strengthen source contexts pointwise:
    a missing slot may become anything (the process never acts
    there -- its conformance at the source says so), and a separate
    end may become a typed ✓ holding that end at the same protocol
    ([pole ρ (pole ρ T) = T]).  The order is closed under the
    context surgery the value clauses perform: consuming an upgraded
    end leaves [None ⊑ SSep co-end], and a fresh reception against an
    upgraded co-end lands in the fuse clause one level down. *)

Lemma pole_invol r T : pole r (pole r T) = T.
Proof. case: r => //=. by rewrite dual_involutive. Qed.

Definition sle (o1 o2 : option sslot) : Prop :=
  o1 = o2
  \/ o1 = None
  \/ (exists r T, o1 = Some (SSep r T) /\ o2 = Some (SBoth (pole r T))).

Lemma sle_refl o : sle o o.
Proof. by left. Qed.

Lemma sle_none o : sle None o.
Proof. by right; left. Qed.

Lemma sle_both r T : sle (Some (SSep r T)) (Some (SBoth (pole r T))).
Proof. right. right. by exists r, T. Qed.

Lemma sty_dec (S1 S2 : sty) : {S1 = S2} + {S1 <> S2}.
Proof. decide equality. Qed.

Lemma sslot_dec (e1 e2 : sslot) : {e1 = e2} + {e1 <> e2}.
Proof. decide equality; by [exact: sty_dec | exact: pol_dec]. Qed.

Lemma oslot_dec (o1 o2 : option sslot) : {o1 = o2} + {o1 <> o2}.
Proof. decide equality. exact: sslot_dec. Qed.

Definition oslot_eqb (o1 o2 : option sslot) : bool :=
  if oslot_dec o1 o2 then true else false.

Lemma oslot_eqP o1 o2 : reflect (o1 = o2) (oslot_eqb o1 o2).
Proof. rewrite /oslot_eqb. case: oslot_dec => [E|Ne]; by constructor. Qed.

(** Owned source slots transport their endpoint view. *)
Lemma sle_esat o1 o2 r T :
  sle o1 o2 ->
  (if o1 is Some e then esat r e else None) = Some T ->
  (if o2 is Some e then esat r e else None) = Some T.
Proof.
  case=> [->|[-> //|[r' [T' [-> ->]]]]] //=.
  case Er : (pol_eqb r r') => // -[ET].
  have -> : r = r' by case: (r) Er; case: (r').
  by rewrite pole_invol ET.
Qed.

(** ** Transport along the slot order *)

Lemma conformV_sle m (Δ1 Δ2 : sctxP m) (P : procP m) :
  (forall x, sle (Δ1 x) (Δ2 x)) ->
  conformV Δ1 P -> conformV Δ2 P.
Proof.
  move=> Hle C a c Hof.
  case: (C _ _ Hof) => S0 [HS0 Ha].
  exists S0. split=> //.
  move: HS0. rewrite /sat.
  exact: sle_esat (Hle c.1).
Qed.

Lemma conformD_sle m (Δ1 Δ2 : sctxP m) (P : procP m) :
  (forall x, sle (Δ1 x) (Δ2 x)) ->
  conformD Δ1 P -> conformD Δ2 P.
Proof.
  elim: P Δ1 Δ2 => //=
    [ m' | m' c K IH | m' c K IH | m' B IH | m' A IHA B IHB
    | m' c r K IH | m' c d K IH | m' c b K IH
    | m' c K1 IH1 K2 IH2 ] Δ1 Δ2 Hle HD.
  - split=> //. exact (conformV_sle Hle (proj1 HD)).
  - split=> //. exact (conformV_sle Hle (proj1 HD)).
  - split=> //. exact (conformV_sle Hle (proj1 HD)).
  - split.
    + exact (conformV_sle Hle (proj1 HD)).
    + case: (proj2 HD) => S0 HD'. exists S0.
      apply: IH HD'. by move=> [x|] //=; last exact: sle_refl.
  - split.
    + exact (conformV_sle Hle (proj1 HD)).
    + split.
      * exact (IHA _ _ Hle (proj1 (proj2 HD))).
      * exact (IHB _ _ Hle (proj2 (proj2 HD))).
  - split=> //. exact (conformV_sle Hle (proj1 HD)).
  - split=> //. exact (conformV_sle Hle (proj1 HD)).
  - split=> //. exact (conformV_sle Hle (proj1 HD)).
  - split=> //. exact (conformV_sle Hle (proj1 HD)).
Qed.

Lemma sle_scupd m (Δ1 Δ2 : sctxP m) (y : ch m) o1 o2 :
  (forall x, sle (Δ1 x) (Δ2 x)) -> sle o1 o2 ->
  forall x, sle (scupd y o1 Δ1 x) (scupd y o2 Δ2 x).
Proof.
  move=> Hle Ho x. rewrite /scupd. by case: (x =P y).
Qed.

Lemma sle_sscons m (Δ1 Δ2 : sctxP m) o1 o2 :
  (forall x, sle (Δ1 x) (Δ2 x)) -> sle o1 o2 ->
  forall x : ch m.+1, sle (scons o1 Δ1 x) (scons o2 Δ2 x).
Proof. move=> Hle Ho [x|] //=. Qed.

Lemma EsemP_sle k :
  forall m (Δ1 Δ2 : sctxP m) (P : procP m),
  (forall x, sle (Δ1 x) (Δ2 x)) ->
  EsemP k Δ1 P -> EsemP k Δ2 P.
Proof.
  elim: k => [//|k IH] m Δ1 Δ2 P Hle [C V St].
  have C1 := conformD_V C.
  split.
  - exact: conformD_sle Hle C.
  - move=> w rw Sw HwS.
    (* which source slot sits under the dispatched target slot? *)
    case: (Hle w) => [E1|[E1|[r' [T' [E1 E2]]]]].
    + (* same slot: transport the source dispatch *)
      have HS1 : Δ1 w = Some (SSep rw Sw) by rewrite E1 HwS.
      move: (V _ _ _ HS1).
      case: Sw HwS HS1 => [| |T S2|T S2|S1' S2'|S1' S2'] HwS HS1 /= HV.
      * move=> P' HT. apply: IH (HV _ HT).
        apply: sle_scupd => //. exact: sle_refl.
      * move=> P' HT. apply: IH (HV _ HT).
        apply: sle_scupd => //. exact: sle_refl.
      * case: HV => HVf HVb. split.
        -- move=> y rd P' HT. case: (HVf _ _ _ HT) => e [He Hs HE].
           case: (Hle y) => [Ey|[Ey|[ry [Ty [Ey Ey2]]]]].
           ++ exists e. split=> //; first by rewrite -Ey.
              apply: IH HE.
              apply: sle_scupd; last exact: sle_refl.
              apply: sle_scupd => //. exact: sle_refl.
           ++ by rewrite Ey in He.
           ++ have Ee : e = SSep ry Ty by move: He; rewrite Ey => -[].
              exists (SBoth (pole ry Ty)). split=> //.
              ** move: Hs. rewrite Ee /=.
                 case Er : (pol_eqb rd ry) => // -[ET].
                 have -> : rd = ry by case: (rd) Er; case: (ry).
                 by rewrite pole_invol ET.
              ** apply: IH HE.
                 apply: sle_scupd.
                 --- apply: sle_scupd => //. exact: sle_refl.
                 --- rewrite Ee /=. exact: sle_none.
        -- move=> r0 P' HT.
           apply: IH (HVb _ _ HT).
           apply: sle_sscons; last exact: sle_refl.
           apply: sle_scupd => //. exact: sle_refl.
      * case: HV => HVc HVs. split.
        -- move=> y rd P' HT. case: (HVc _ _ _ HT) => Hf Hz. split.
           ++ (* target-fresh: the source is None too *)
              move=> Hy2.
              have Hy1 : Δ1 y = None.
                case: (Hle y) => [E|[E //|[ry [Ty [E E2]]]]].
                ** by rewrite E Hy2.
                ** by rewrite E2 in Hy2.
              apply: IH (Hf Hy1).
              apply: sle_scupd; last exact: sle_refl.
              apply: sle_scupd => //. exact: sle_refl.
           ++ (* target-fuse: source is same (fuse) or None (fresh) *)
              move=> Hy2.
              case: (Hle y) => [E|[E|[ry [Ty [E E2]]]]].
              ** have Hy1 : Δ1 y = Some (SSep (flipp rd) (dual T))
                   by rewrite E Hy2.
                 apply: IH (Hz Hy1).
                 apply: sle_scupd; last exact: sle_refl.
                 apply: sle_scupd => //. exact: sle_refl.
              ** (* source fresh, target co-end: route the fresh
                    obligation and upgrade the received slot *)
                 apply: IH (Hf E).
                 apply: sle_scupd.
                 --- apply: sle_scupd => //. exact: sle_refl.
                 --- exact: sle_both.
              ** by rewrite E2 in Hy2.
        -- move=> rd P'' HT.
           apply: IH (HVs _ _ HT).
           apply: sle_sscons; last exact: sle_refl.
           apply: sle_scupd => //. exact: sle_refl.
      * move=> b P' HT. apply: IH (HV _ _ HT).
        apply: sle_scupd => //. exact: sle_refl.
      * move=> b P' HT. case: (HV _ _ HT) => Δ1' [Hev HE].
        exists (fun x => if oslot_eqb (Δ1' x) (Δ1 x)
                         then Δ2 x else Δ1' x).
        split.
        -- move=> x.
           case: (oslot_eqP (Δ1' x) (Δ1 x)) => [E|Ne]; first by left.
           case: (Hev x) => [E|[S0 [S0' [E E']]]];
             first by rewrite E in Ne.
           right. exists S0, S0'. split=> //.
           case: (Hle x) => [El|[El|[ry [Ty [El _]]]]].
           ++ by rewrite -El.
           ++ by rewrite El in E.
           ++ by rewrite El in E.
        -- apply: IH HE.
           apply: sle_scupd; last exact: sle_refl.
           move=> x.
           case: (oslot_eqP (Δ1' x) (Δ1 x)) => [E|Ne].
           ++ rewrite E. exact: Hle.
           ++ exact: sle_refl.
    + (* source unowned: any transition at (w,rw) is an offer the
         source conformance cannot cover *)
      have Hno : forall a, ~ offersP a ((w, rw) : pch m) P.
        move=> a Hof. case: (C1 _ _ Hof) => S0 [HS0 _].
        by move: HS0; rewrite /sat /= E1.
      case: Sw HwS => [| |T S2|T S2|S1' S2'|S1' S2'] HwS /=.
      * move=> P' HT. exfalso.
        apply: (Hno AClose). by exists P'.
      * move=> P' HT. exfalso.
        apply: (Hno AWait). by exists P'.
      * split.
        -- move=> y rd P' HT. exfalso.
           apply: (Hno ADelS). left. by exists (y, rd), P'.
        -- move=> r0 P' HT. exfalso.
           apply: (Hno ADelS). right. by exists r0, P'.
      * split.
        -- move=> y rd P' HT. exfalso.
           apply: (Hno ADelR). by exists (y, rd), P'.
        -- move=> rd P'' HT. exfalso.
           (* shifted transition pulls back to an offer of P *)
           have Hof' : offersP ADelR (pshift ((w, rw) : pch m))
                         (psubst shift P).
             by exists (zero, rd), P''.
           case: (offersP_ren_inv Hof') => c0 [Ec0 Hof0].
           have Ec0' : c0 = ((w, rw) : pch m).
             case: c0 Ec0 Hof0 => cn cr /= -[E1' E2'] Hof0.
             by rewrite E1' E2'.
           rewrite Ec0' in Hof0.
           apply: (Hno ADelR). exact: Hof0.
      * move=> b P' HT. exfalso.
        apply: (Hno ASel). by exists b, P'.
      * move=> b P' HT. exfalso.
        apply: (Hno ABra). by exists b, P'.
    + (* source SSep, target SBoth: the target never dispatches *)
      by rewrite E2 in HwS.
  - move=> P' Hst. case: (St _ Hst) => Δ1' [Hev HE].
    exists (fun x => if oslot_eqb (Δ1' x) (Δ1 x) then Δ2 x else Δ1' x).
    split.
    + move=> x. case: (oslot_eqP (Δ1' x) (Δ1 x)) => [E|Ne]; first by left.
      case: (Hev x) => [E|[S0 [S0' [E E']]]]; first by rewrite E in Ne.
      right. exists S0, S0'. split=> //.
      case: (Hle x) => [El|[El|[ry [Ty [El _]]]]].
      * by rewrite -El.
      * by rewrite El in E.
      * by rewrite El in E.
    + apply: IH HE => x.
      case: (oslot_eqP (Δ1' x) (Δ1 x)) => [E|Ne].
      * rewrite E. exact: Hle.
      * exact: sle_refl.
Qed.

Print Assumptions EsemP_sle.

(** ** The substitution lemma (v3)

    Renamings preserving owned slots and injective on them carry the
    relation.  The receive clauses route fresh image-receptions
    through the preimage's shifted-fresh conjunct (factoring
    [psubst s P = psubst (scons y s) (psubst shift P)]); the fuse
    clause splits on whether the fused image name has an owned
    preimage ([find_ch] decides): with one, the preimage's own fuse
    obligation transports; without one, the fresh route lands one
    [sle]-upgrade below the target. *)

Lemma EsemP_ren k :
  forall m n (s : ren m n) (Δm : sctxP m) (Δn : sctxP n) (P : procP m),
  agree s Δm Δn -> inj_on s Δm ->
  EsemP k Δm P -> EsemP k Δn (psubst s P).
Proof.
  elim: k => [//|k IH] m n s Δm Δn P Hag Hinj [C V St].
  have C1 := conformD_V C.
  split.
  - exact: conformD_ren Hag C.
  - move=> w rw Sw HwS.
    have SUBJ : forall (c : pch m) a, offersP a c P -> pren s c = (w, rw) ->
        Δm c.1 = Δn w /\ c.2 = rw.
      move=> c a Hof Ec.
      case: (C1 _ _ Hof) => S' [HS' _].
      move: HS'. rewrite /sat.
      case E : (Δm c.1) => [e|] // Hes.
      case: (Hag c.1) => [E'|E']; first by rewrite E' in E.
      move: Ec => -[Ec1 Ec2].
      split; last by rewrite Ec2.
      by rewrite -Ec1 E'.
    case: Sw HwS => [| |T S2|T S2|S1 S2|S1 S2] HwS /=.
    + (* ===== SClose ===== *)
      move=> P' HT.
      case: (ltscP_ren_inv HT erefl) => c [P0 [E1 -> H0]].
      have Hof : offersP AClose c P by exists P0.
      case: (SUBJ _ _ Hof (esym E1)) => HS Ep. rewrite HwS in HS.
      move: (V _ _ _ HS) => /= HV.
      have H0' : ltscP (c.1, rw) P P0
        by rewrite -Ep -surjective_pairing.
      have HE0 := HV _ H0'.
      have Ew : w = s c.1 by move: E1 => -[-> _].
      rewrite Ew.
      apply: IH HE0.
      * apply: agree_scupd => //. by rewrite HS.
      * apply: inj_on_sub Hinj. apply: owned_scupd_sub. by rewrite HS.
    + (* SWait *)
      move=> P' HT.
      case: (ltswP_ren_inv HT erefl) => c [P0 [E1 -> H0]].
      have Hof : offersP AWait c P by exists P0.
      case: (SUBJ _ _ Hof (esym E1)) => HS Ep. rewrite HwS in HS.
      move: (V _ _ _ HS) => /= HV.
      have H0' : ltswP (c.1, rw) P P0
        by rewrite -Ep -surjective_pairing.
      have HE0 := HV _ H0'.
      have Ew : w = s c.1 by move: E1 => -[-> _].
      rewrite Ew.
      apply: IH HE0.
      * apply: agree_scupd => //. by rewrite HS.
      * apply: inj_on_sub Hinj. apply: owned_scupd_sub. by rewrite HS.
    + (* ===== SSend ===== *)
      split.
      * (* free send *)
        move=> y rd P' HT.
        case: (ltsfP_ren_inv HT erefl) => c [d [P0 [E1 ED -> H0]]].
        have Hof : offersP ADelS c P by left; exists d, P0.
        case: (SUBJ _ _ Hof (esym E1)) => HS Ep. rewrite HwS in HS.
        move: (V _ _ _ HS) => /= -[HVf _].
        have H0' : ltsfP (c.1, rw) (d.1, d.2) P P0
          by rewrite -Ep -!surjective_pairing.
        case: (HVf _ _ _ H0') => e [He Hs HE0].
        have Ew : w = s c.1 by move: E1 => -[-> _].
        have Edy : y = s d.1 /\ rd = d.2 by move: ED => -[-> ->].
        case: Edy => Ey Erd.
        have Hdc : d.1 <> c.1.
          move=> E. rewrite E HS in He. case: He => Ee.
          move: Hs. rewrite -Ee /=.
          case Er : (pol_eqb d.2 rw) => // -[Efix].
          exact: ssend_neqT (esym Efix).
        exists e. split.
        -- rewrite Ey.
           case: (Hag d.1) => [E|E]; first by rewrite E in He.
           by rewrite E He.
        -- by rewrite Erd.
        -- rewrite Ew Ey Erd.
           apply: IH HE0.
           ++ apply: agree_scupd.
              ** apply: agree_scupd => //. by rewrite HS.
              ** apply: inj_on_sub Hinj. apply: owned_scupd_sub.
                 by rewrite HS.
              ** rewrite /scupd. case: (d.1 =P c.1) => // _.
                 by rewrite He.
           ++ apply: inj_on_sub Hinj => x.
              rewrite /scupd. case: (x =P d.1) => [->|_].
              ** move=> _. by rewrite He.
              ** case: (x =P c.1) => [->|_]; first by rewrite HS.
                 by [].
      * (* bound send *)
        move=> r' P' HT.
        case: (ltsbP_ren_inv HT erefl) => c [P0 [E1 -> H0]].
        have Hof : offersP ADelS c P by right; exists r', P0.
        case: (SUBJ _ _ Hof (esym E1)) => HS Ep. rewrite HwS in HS.
        move: (V _ _ _ HS) => /= -[_ HVb].
        have H0' : ltsbP (c.1, rw) r' P P0
          by rewrite -Ep -surjective_pairing.
        have HE0 := HVb _ _ H0'.
        have Ew : w = s c.1 by move: E1 => -[-> _].
        rewrite Ew.
        apply: IH HE0.
        -- apply: agree_sscons. apply: agree_scupd => //. by rewrite HS.
        -- apply: inj_sscons. apply: inj_on_sub Hinj.
           apply: owned_scupd_sub. by rewrite HS.
    + (* ===== SRecv ===== *)
      split.
      * move=> y rd P' HT. split.
        -- (* fresh reception *)
           move=> Hy.
           have EPfac : psubst (scons y s) (psubst shift P) = psubst s P.
             rewrite psubst_comp. by apply: psubst_ext => x.
           case: (ltsrP_ren_inv HT EPfac) => c'' [P0 [E1'' ER'' Hu'']].
           case: c'' E1'' Hu'' => -[c0|] cr E1'' Hu''; last first.
           ++ exfalso. move: E1'' => -[E1n _].
              rewrite /= in E1n. by rewrite -E1n HwS in Hy.
           ++ have Hof : offersP ADelR (c0, cr) P.
                have Hof' : offersP ADelR ((Some c0, cr) : pch m.+1)
                              (psubst shift P).
                  exists (zero, rd), (psubst (scons zero id_ren) P0).
                  exact (Hu'' zero).
                case: (offersP_ren_inv Hof') => cP [EcP HofP].
                have EcP' : cP = (c0, cr).
                  case: cP EcP HofP => cpn cpr /= -[EcP1 EcP2] HofP.
                  by rewrite EcP1 EcP2.
                by rewrite -EcP'.
              have Esubj : pren s ((c0, cr) : pch m) = (w, rw).
                move: E1'' => -[E1n E1r]. move: E1n => /= E1n.
                by rewrite /pren /= -E1n -E1r.
              case: (SUBJ _ _ Hof Esubj) => HS Ep. rewrite HwS in HS.
              move: (V _ _ _ HS) => /= -[_ HVs].
              have Hz : ltsrP (pshift ((c0, rw) : pch m)) (zero, rd)
                  (psubst shift P) (psubst (scons zero id_ren) P0).
                rewrite -Ep. exact (Hu'' zero).
              have HE0 := HVs _ _ Hz.
              have EP' : P' = psubst (scons y s)
                                (psubst (scons zero id_ren) P0).
                rewrite ER'' !psubst_comp. by apply: psubst_ext => -[z|].
              rewrite EP'.
              have Ew : w = s c0 by move: Esubj => -[-> _].
              rewrite Ew.
              apply: IH HE0.
              ** move=> [x|] /=; last first.
                 --- right. by rewrite /scupd eqxx.
                 --- case E : (scupd c0 (Some (SSep rw S2)) Δm x) => [e|];
                       last by left.
                     right.
                     have Hsx : s x <> y.
                       move=> Exy.
                       have Hox : Δm x <> None.
                         move: E. rewrite /scupd.
                         case: ((x : ch m) =P c0) => [->|_];
                           first by rewrite HS.
                         by move=> ->.
                       case: (Hag x) => [//|E2].
                       by rewrite Exy Hy in E2; rewrite -E2 in Hox.
                     rewrite /scupd.
                     case: (s x =P y) => [//|_].
                     move: E. rewrite /scupd.
                     case: ((x : ch m) =P c0) => [-> E2 |Nxc E].
                     +++ by rewrite eqxx -E2.
                     +++ have Hox : Δm x <> None by rewrite E.
                         have Bsx : (s x == s c0) = false.
                           apply/eqP => Es. apply: Nxc. apply: Hinj Es => //.
                           by rewrite HS.
                         rewrite Bsx.
                         case: (Hag x) => [E2|E2];
                           first by rewrite E2 in E.
                         by rewrite E2 E.
              ** move=> [x1|] [x2|] //= H1 H2 E.
                 --- have Hox1 : Δm x1 <> None.
                       move: H1. rewrite /scupd.
                       case: ((x1 : ch m) =P c0) => [->|_];
                         first by rewrite HS.
                       by [].
                     have Hox2 : Δm x2 <> None.
                       move: H2. rewrite /scupd.
                       case: ((x2 : ch m) =P c0) => [->|_];
                         first by rewrite HS.
                       by [].
                     by rewrite (Hinj _ _ Hox1 Hox2 E).
                 --- exfalso.
                     have Hox1 : Δm x1 <> None.
                       move: H1. rewrite /scupd.
                       case: ((x1 : ch m) =P c0) => [->|_];
                         first by rewrite HS.
                       by [].
                     case: (Hag x1) => [//|E2].
                     by rewrite E Hy in E2; rewrite -E2 in Hox1.
                 --- exfalso.
                     have Hox2 : Δm x2 <> None.
                       move: H2. rewrite /scupd.
                       case: ((x2 : ch m) =P c0) => [->|_];
                         first by rewrite HS.
                       by [].
                     case: (Hag x2) => [//|E2].
                     by rewrite -E Hy in E2; rewrite -E2 in Hox2.
        -- (* fuse: the received image name has an owned co-end *)
           move=> Hy.
           case F : (find_ch (fun x => (s x == y)
                       && ~~ oslot_eqb (Δm x) None)) => [x0|].
           ++ (* an owned preimage exists: the preimage fuses *)
              move: (find_ch_sound F) => /andP[/eqP Fx0 Fo].
              have Hox0 : Δm x0 <> None.
                by move: Fo; case: (oslot_eqP (Δm x0) None).
              have Ex0 : Δm x0 = Some (SSep (flipp rd) (dual T)).
                case: (Hag x0) => [//|E2].
                by rewrite Fx0 Hy in E2.
              case: (ltsrP_ren_inv HT erefl) => -[cn cr] [P0 [E1 ER Hu]].
              have Hof : offersP ADelR (cn, cr) P.
                exists (cn, rd), (psubst (scons cn id_ren) P0).
                exact (Hu cn).
              case: (SUBJ _ _ Hof (esym E1)) => /= HS Ep. rewrite HwS in HS.
              move: (V _ _ _ HS) => /= -[HVc _].
              have Hx0 : ltsrP (cn, rw) (x0, rd) P
                  (psubst (scons x0 id_ren) P0).
                rewrite -Ep -[((x0, rd))]/((x0, (y, rd).2)).
                exact (Hu x0).
              case: (HVc _ _ _ Hx0) => _ Hfuse.
              have HE0 := Hfuse Ex0.
              have EP' : P' = psubst s (psubst (scons x0 id_ren) P0).
                by rewrite ER !psubst_comp; apply: psubst_ext => -[z|] //=.
              rewrite {}EP'.
              have Ew : w = s cn by move: E1 => -[-> _].
              rewrite Ew -Fx0.
              apply: IH HE0.
              ** apply: agree_scupd.
                 --- apply: agree_scupd => //. by rewrite HS.
                 --- apply: inj_on_sub Hinj. apply: owned_scupd_sub.
                     by rewrite HS.
                 --- rewrite /scupd.
                     by case: ((x0 : ch m) =P cn) => [_|_]; rewrite ?Ex0.
              ** apply: inj_on_sub Hinj => x.
                 rewrite /scupd.
                 case: ((x : ch m) =P x0) => [-> _|_];
                   first by rewrite Ex0.
                 case: ((x : ch m) =P cn) => [-> _|_];
                   first by rewrite HS.
                 by [].
           ++ (* no owned preimage: fresh route, then upgrade *)
              have Hnone : forall x, s x = y -> Δm x = None.
                move=> x Ex.
                case E : (Δm x) => [e|] //.
                have Hp : (s x == y) && ~~ oslot_eqb (Δm x) None.
                  rewrite Ex eqxx /=.
                  by case: (oslot_eqP (Δm x) None); rewrite E.
                case: (find_ch_complete (p := fun x => (s x == y)
                          && ~~ oslot_eqb (Δm x) None) Hp) => x' F'.
                by rewrite F' in F.
              (* replay the fresh argument against a y-cleared target *)
              have EPfac : psubst (scons y s) (psubst shift P) = psubst s P.
                rewrite psubst_comp. by apply: psubst_ext => x.
              case: (ltsrP_ren_inv HT EPfac) => c'' [P0 [E1'' ER'' Hu'']].
              case: c'' E1'' Hu'' => -[c0|] cr E1'' Hu''; last first.
              ** exfalso. move: E1'' => -[E1n _].
                 rewrite -E1n HwS in Hy. case: Hy => _ ETy.
                 have ED := f_equal dual ETy.
                 rewrite /= dual_involutive in ED.
                 exact: ssend_neqT (esym ED).
              ** have Hof : offersP ADelR (c0, cr) P.
                   have Hof' : offersP ADelR ((Some c0, cr) : pch m.+1)
                                 (psubst shift P).
                     exists (zero, rd), (psubst (scons zero id_ren) P0).
                     exact (Hu'' zero).
                   case: (offersP_ren_inv Hof') => cP [EcP HofP].
                   have EcP' : cP = (c0, cr).
                     case: cP EcP HofP => cpn cpr /= -[EcP1 EcP2] HofP.
                     by rewrite EcP1 EcP2.
                   by rewrite -EcP'.
                 have Esubj : pren s ((c0, cr) : pch m) = (w, rw).
                   move: E1'' => -[E1n E1r]. move: E1n => /= E1n.
                   by rewrite /pren /= -E1n -E1r.
                 case: (SUBJ _ _ Hof Esubj) => HS Ep. rewrite HwS in HS.
                 move: (V _ _ _ HS) => /= -[_ HVs].
                 have Hz : ltsrP (pshift ((c0, rw) : pch m)) (zero, rd)
                     (psubst shift P) (psubst (scons zero id_ren) P0).
                   rewrite -Ep. exact (Hu'' zero).
                 have HE0 := HVs _ _ Hz.
                 have EP' : P' = psubst (scons y s)
                                   (psubst (scons zero id_ren) P0).
                   rewrite ER'' !psubst_comp.
                   by apply: psubst_ext => -[z|].
                 rewrite EP'.
                 have Ew : w = s c0 by move: Esubj => -[-> _].
                 rewrite Ew.
                 (* transport to the SSep target, then upgrade to SBoth *)
                 have HMID : EsemP k
                     (scupd y (Some (SSep rd T))
                        (scupd (s c0) (Some (SSep rw S2)) Δn))
                     (psubst (scons y s)
                        (psubst (scons zero id_ren) P0)).
                   apply: IH HE0.
                   --- move=> [x|] /=; last first.
                       +++ right. by rewrite /scupd eqxx.
                       +++ case E : (scupd c0 (Some (SSep rw S2)) Δm x)
                             => [e|]; last by left.
                           right.
                           have Hox : Δm x <> None.
                             move: E. rewrite /scupd.
                             case: ((x : ch m) =P c0) => [->|_];
                               first by rewrite HS.
                             by move=> ->.
                           have Hsx : s x <> y.
                             move=> Exy. by rewrite (Hnone _ Exy) in Hox.
                           rewrite /scupd.
                           case: (s x =P y) => [//|_].
                           move: E. rewrite /scupd.
                           case: ((x : ch m) =P c0) => [-> E2 |Nxc E].
                           *** by rewrite eqxx -E2.
                           *** have Bsx : (s x == s c0) = false.
                                 apply/eqP => Es. apply: Nxc.
                                 apply: Hinj Es => //. by rewrite HS.
                               rewrite Bsx.
                               case: (Hag x) => [E2|E2];
                                 first by rewrite E2 in E.
                               by rewrite E2 E.
                   --- move=> [x1|] [x2|] //= H1 H2 E.
                       +++ have Hox1 : Δm x1 <> None.
                             move: H1. rewrite /scupd.
                             case: ((x1 : ch m) =P c0) => [->|_];
                               first by rewrite HS.
                             by [].
                           have Hox2 : Δm x2 <> None.
                             move: H2. rewrite /scupd.
                             case: ((x2 : ch m) =P c0) => [->|_];
                               first by rewrite HS.
                             by [].
                           by rewrite (Hinj _ _ Hox1 Hox2 E).
                       +++ exfalso.
                           have Hox1 : Δm x1 <> None.
                             move: H1. rewrite /scupd.
                             case: ((x1 : ch m) =P c0) => [->|_];
                               first by rewrite HS.
                             by [].
                           by rewrite (Hnone _ E) in Hox1.
                       +++ exfalso.
                           have Hox2 : Δm x2 <> None.
                             move: H2. rewrite /scupd.
                             case: ((x2 : ch m) =P c0) => [->|_];
                               first by rewrite HS.
                             by [].
                           by rewrite (Hnone _ (esym E)) in Hox2.
                 apply: EsemP_sle HMID => x.
                 rewrite /scupd. case: (x =P y) => [_|_].
                 --- exact: sle_both.
                 --- exact: sle_refl.
      * (* shifted-fresh of the image *)
        move=> rd P'' HT.
        have EPs : psubst shift (psubst s P)
                 = psubst (up_ch s) (psubst shift P).
          by rewrite psubst_shift_comm.
        move: HT. rewrite EPs => HT.
        case: (ltsrP_ren_inv HT erefl) => c'' [P0 [E1'' ER'' Hu'']].
        case: c'' E1'' Hu'' => -[c0|] cr E1'' Hu''; last first.
        -- exfalso. move: E1'' => -[E1n _]. by discriminate E1n.
        -- have Hof : offersP ADelR (c0, cr) P.
             have Hof' : offersP ADelR ((Some c0, cr) : pch m.+1)
                           (psubst shift P).
               exists (zero, rd), (psubst (scons zero id_ren) P0).
               exact (Hu'' zero).
             case: (offersP_ren_inv Hof') => cP [EcP HofP].
             have EcP' : cP = (c0, cr).
               case: cP EcP HofP => cpn cpr /= -[EcP1 EcP2] HofP.
               by rewrite EcP1 EcP2.
             by rewrite -EcP'.
           have Esubj : pren s ((c0, cr) : pch m) = (w, rw).
             move: E1'' => -[E1n E1r]. move: E1n => /= E1n.
             by rewrite /pren /= -E1n -E1r.
           case: (SUBJ _ _ Hof Esubj) => HS Ep. rewrite HwS in HS.
           move: (V _ _ _ HS) => /= -[_ HVs].
           have Hz : ltsrP (pshift ((c0, rw) : pch m)) (zero, rd)
               (psubst shift P) (psubst (scons zero id_ren) P0).
             rewrite -Ep. exact (Hu'' zero).
           have HE0 := HVs _ _ Hz.
           have EP'' : P'' = psubst (up_ch s)
                               (psubst (scons zero id_ren) P0).
             rewrite ER'' !psubst_comp. by apply: psubst_ext => -[z|].
           rewrite EP''.
           have Ew : w = s c0 by move: Esubj => -[-> _].
           rewrite Ew.
           apply: IH HE0.
           ++ apply: agree_sscons. apply: agree_scupd => //. by rewrite HS.
           ++ apply: inj_sscons. apply: inj_on_sub Hinj.
              apply: owned_scupd_sub. by rewrite HS.
    + (* ===== SSel ===== *)
      move=> b P' HT.
      case: (ltsselP_ren_inv HT erefl) => c [P0 [E1 -> H0]].
      have Hof : offersP ASel c P by exists b, P0.
      case: (SUBJ _ _ Hof (esym E1)) => HS Ep. rewrite HwS in HS.
      move: (V _ _ _ HS) => /= HV.
      have H0' : ltsselP (c.1, rw) b P P0
        by rewrite -Ep -surjective_pairing.
      have HE0 := HV _ _ H0'.
      have Ew : w = s c.1 by move: E1 => -[-> _].
      rewrite Ew.
      apply: IH HE0.
      * apply: agree_scupd => //. by rewrite HS.
      * apply: inj_on_sub Hinj. apply: owned_scupd_sub. by rewrite HS.
    + (* SBra: the branch may re-choose the internal protocols;
         push that evolution forward like a τ *)
      move=> b P' HT.
      case: (ltsbrP_ren_inv HT erefl) => c [P0 [E1 -> H0]].
      have Hof : offersP ABra c P by exists b, P0.
      case: (SUBJ _ _ Hof (esym E1)) => HS Ep. rewrite HwS in HS.
      move: (V _ _ _ HS) => /= HV.
      have H0' : ltsbrP (c.1, rw) b P P0
        by rewrite -Ep -surjective_pairing.
      case: (HV _ _ H0') => Δm' [Hev HE0].
      have Ew : w = s c.1 by move: E1 => -[-> _].
      rewrite Ew.
      pose Δn' : sctxP n := fun w' =>
        if find_ch (fun x => (s x == w') && ~~ oslot_eqb (Δm x) (Δm' x))
          is Some x0 then Δm' x0 else Δn w'.
      have Hchg : forall x, oslot_eqb (Δm x) (Δm' x) = false ->
          exists S0 S0',
            Δm x = Some (SBoth S0) /\ Δm' x = Some (SBoth S0').
        move=> x Hne.
        case: (Hev x) => [E|//].
        case: (oslot_eqP (Δm x) (Δm' x)) Hne => // Ne _.
        by rewrite E in Ne.
      have Hag' : agree s Δm' Δn'.
        move=> x.
        case Ex : (Δm' x) => [e'|]; last by left.
        right. rewrite /Δn'.
        have Hox' : Δm x <> None.
          case: (Hev x) => [E|[S0 [S0' [E _]]]]; last by rewrite E.
          by rewrite -E Ex.
        case F : (find_ch (fun x' => (s x' == s x)
                    && ~~ oslot_eqb (Δm x') (Δm' x'))) => [x1|].
        * move: (find_ch_sound F) => /andP[/eqP Fx1 Fne].
          have [S0 [S0' [Em Em']]] := Hchg x1 (negbTE Fne).
          have Ex1 : x1 = x.
            apply: Hinj Fx1; by [rewrite Em | exact: Hox'].
          by rewrite Ex1 Ex.
        * have Exx : Δm x = Δm' x.
            case: (oslot_eqP (Δm x) (Δm' x)) => // Ne.
            have Hp : (s x == s x) && ~~ oslot_eqb (Δm x) (Δm' x).
              rewrite eqxx /=.
              by case: (oslot_eqP (Δm x) (Δm' x)) Ne.
            case: (find_ch_complete (p := fun x' => (s x' == s x)
                      && ~~ oslot_eqb (Δm x') (Δm' x')) Hp) => x' F'.
            by rewrite F' in F.
          case: (Hag x) => [E|E]; first by rewrite Exx Ex in E.
          by rewrite E Exx Ex.
      have Hinj' : inj_on s Δm'.
        move=> x1 x2 H1 H2 E.
        apply: Hinj E.
        * case: (Hev x1) H1 => [<-|[S0 [S0' [Em _]]]] //.
          by rewrite Em.
        * case: (Hev x2) H2 => [<-|[S0 [S0' [Em _]]]] //.
          by rewrite Em.
      have HmC : Δm' c.1 = Δm c.1.
        case: (Hev c.1) => [E|[S0 [S0' [E _]]]] //.
        by rewrite E in HS.
      exists Δn'. split.
      * move=> w'. rewrite /Δn'.
        case F : (find_ch (fun x => (s x == w')
                    && ~~ oslot_eqb (Δm x) (Δm' x))) => [x0|];
          last by left.
        move: (find_ch_sound F) => /andP[/eqP Fx0 Fne].
        have [S0 [S0' [Em Em']]] := Hchg x0 (negbTE Fne).
        right. exists S0, S0'. split=> //.
        case: (Hag x0) => [E|E]; first by rewrite E in Em.
        by rewrite -Fx0 E Em.
      * apply: IH HE0.
        -- apply: agree_scupd => //. by rewrite HmC HS.
        -- apply: inj_on_sub Hinj'. apply: owned_scupd_sub.
           by rewrite HmC HS.
  - (* ===== internal step ===== *) move=> P' Hst.
    have HG : forall a (c : pch m), offersP a c P -> Δm c.1 <> None.
      move=> a c Hof.
      case: (C1 _ _ Hof) => S' [HS' _].
      move: HS'. rewrite /sat. by case: (Δm c.1).
    case: (ltstP_ren_inv_cov Hst HG Hinj erefl) => P0 [-> H0].
    case: (St _ H0) => Δm' [Hev HE].
    (* push the evolution forward *)
    pose Δn' : sctxP n := fun w' =>
      if find_ch (fun x => (s x == w') && ~~ oslot_eqb (Δm x) (Δm' x))
        is Some x0 then Δm' x0 else Δn w'.
    have Hchg : forall x, oslot_eqb (Δm x) (Δm' x) = false ->
        exists S0 S0', Δm x = Some (SBoth S0) /\ Δm' x = Some (SBoth S0').
      move=> x Hne.
      case: (Hev x) => [E|//].
      case: (oslot_eqP (Δm x) (Δm' x)) Hne => // Ne _.
      by rewrite E in Ne.
    exists Δn'. split.
    + move=> w'. rewrite /Δn'.
      case F : (find_ch (fun x => (s x == w')
                  && ~~ oslot_eqb (Δm x) (Δm' x))) => [x0|]; last by left.
      move: (find_ch_sound F) => /andP[/eqP Fx0 Fne].
      have [S0 [S0' [Em Em']]] := Hchg x0 (negbTE Fne).
      right. exists S0, S0'. split=> //.
      case: (Hag x0) => [E|E]; first by rewrite E in Em.
      by rewrite -Fx0 E Em.
    + apply: IH HE.
      * move=> x.
        case Ex : (Δm' x) => [e'|]; last by left.
        right. rewrite /Δn'.
        have Hox' : Δm x <> None.
          case: (Hev x) => [E|[S0 [S0' [E _]]]]; last by rewrite E.
          by rewrite -E Ex.
        case F : (find_ch (fun x' => (s x' == s x)
                    && ~~ oslot_eqb (Δm x') (Δm' x'))) => [x1|].
        -- move: (find_ch_sound F) => /andP[/eqP Fx1 Fne].
           have [S0 [S0' [Em Em']]] := Hchg x1 (negbTE Fne).
           have Ex1 : x1 = x.
             apply: Hinj Fx1; by [rewrite Em | exact: Hox'].
           by rewrite Ex1 Ex.
        -- (* x itself did not change *)
           have Exx : Δm x = Δm' x.
             case: (oslot_eqP (Δm x) (Δm' x)) => // Ne.
             have Hp : (s x == s x) && ~~ oslot_eqb (Δm x) (Δm' x).
               rewrite eqxx /=.
               by case: (oslot_eqP (Δm x) (Δm' x)) Ne.
             case: (find_ch_complete (p := fun x' => (s x' == s x)
                       && ~~ oslot_eqb (Δm x') (Δm' x')) Hp) => x' F'.
             by rewrite F' in F.
           case: (Hag x) => [E|E]; first by rewrite Exx Ex in E.
           by rewrite E Exx Ex.
      * move=> x1 x2 H1 H2 E.
        apply: Hinj E.
        -- case: (Hev x1) H1 => [<-|[S0 [S0' [Em _]]]] //.
           by rewrite Em.
        -- case: (Hev x2) H2 => [<-|[S0 [S0' [Em _]]]] //.
           by rewrite Em.
Qed.

Print Assumptions EsemP_ren.

(** ** Entering a fresh scope *)
Lemma EsemP_shift k m (Δ : sctxP m) e (P : procP m) :
  EsemP k Δ P -> EsemP k (scons e Δ) (psubst shift P).
Proof.
  apply: EsemP_ren.
  - move=> x. by right.
  - move=> x1 x2 _ _ E.
    exact: (f_equal (fun c : ch m.+1 => if c is Some u then u else x1) E).
Qed.

Print Assumptions EsemP_shift.
