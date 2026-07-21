(** * Transfer: structural congruence preserves transitions

    The single ≅-induction of the development.  Together with the
    syntax-directed inversion of the LTS, it subsumes the bespoke
    decomposition lemmas of the old interface.

    Contents:
    - [struct_eq_ren]: ≅ is closed under renaming (discharges the
      first interface hypothesis of [Fundamental.v]);
    - inversion helpers: dead processes have no transitions, prefixes
      have exactly their own;
    - backward equivariance: transitions of a renamed process are
      renamed transitions (injective renamings) -- for all five
      families, equational form; existential form for free-send;
    - transfer for the close, wait, free-send and receive families.

    ** Audit: why there is no [transfer_b]

    The bound-send family [ltsb] is part of the LTS for completeness,
    but nothing in the safety development consumes its transfer lemma:
    - the logical relation's exposure clauses mention only the four
      prefix shapes, whose inversion interface maps to the four
      transfers proved here (close/wait/del/ins ↦ c/w/f/r);
    - reduction never fires a bound send: extrusion happens by [≅]
      before any redex forms, so the payload of every communication is
      free at the redex scope -- the [⇛]-bridges analyse [ltsf]/[ltsr]
      pairs (plus close/wait), never [ltsb];
    - [Esem_rename] needs only the equivariance lemmas.
    Its transfer would in any case be the hardest of the five (the
    SwapB case crosses derivation shapes: extrude-then-pass-binder vs
    pass-binder-then-extrude); it is deliberately out of scope. *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import synsem Errors LogRel Toolkit LTS.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma subst_eqP n m (s t : ren n m) {P : proc n} :
  (forall z, s z = t z) -> subst_proc s P = subst_proc t P.
Proof. move=> H. exact: subst_proc_ext. Qed.

(** ** ≅ is closed under renaming *)
Lemma struct_eq_ren m (P Q : proc m) (H : P ≅ Q) :
  forall n (s : ren m n), subst_proc s P ≅ subst_proc s Q.
Proof.
  elim: H => {m P Q}.
  - move=> m P Q n s /=. exact: SC_Par_Com.
  - move=> m P Q R n s /=. exact: SC_Par_Assoc.
  - move=> m P n s /=. exact: SC_Par_Inact.
  - move=> m P Q n s /=.
    have -> : subst_proc (up_ch (up_ch s)) (subst_proc (shift \o shift) Q)
              = subst_proc (shift \o shift) (subst_proc s Q).
      rewrite !subst_proc_comp. apply: subst_eqP => z.
      exact: up2_shift2.
    exact: SC_Res_Scope.
  - move=> m P n s /=.
    have -> : subst_proc (up_ch (up_ch s)) (subst_proc (swap_ch zero one) P)
              = subst_proc (swap_ch zero one) (subst_proc (up_ch (up_ch s)) P).
      rewrite !subst_proc_comp. apply: subst_eqP => z.
      by rewrite /= swap01_up2.
    exact: SC_Res_SwapC.
  - move=> m P n s /=.
    have -> : subst_proc (up_ch (up_ch (up_ch (up_ch s))))
                (subst_proc (swap_ch one three)
                   (subst_proc (swap_ch zero two) P))
              = subst_proc (swap_ch one three)
                  (subst_proc (swap_ch zero two)
                     (subst_proc (up_ch (up_ch (up_ch (up_ch s)))) P)).
      rewrite !subst_proc_comp. apply: subst_eqP => z.
      by rewrite /= swap02_up4 swap13_up4.
    exact: SC_Res_SwapB.
  - move=> m n s /=. exact: SC_Res_Inact.
  - move=> m P n s. exact: SC_Refl.
  - move=> m P Q _ IH n s. exact: SC_Sym (IH _ _).
  - move=> m P Q R _ IH1 _ IH2 n s. exact: SC_Trans (IH1 _ _) (IH2 _ _).
  - move=> m P P' Q Q' _ IH1 _ IH2 n s /=.
    exact: SC_Cong_Par (IH1 _ _) (IH2 _ _).
  - move=> m P P' _ IH n s /=. exact: SC_Cong_Res (IH _ _).
  - move=> m P P' x _ IH n s /=. exact: SC_Cong_Close (IH _ _).
  - move=> m P P' x _ IH n s /=. exact: SC_Cong_Wait (IH _ _).
  - move=> m P P' x y _ IH n s /=. exact: SC_Cong_OutS (IH _ _).
  - move=> m P P' x _ IH n s /=. exact: SC_Cong_InsP (IH _ _).
Qed.

(** ** Dead processes have no transitions; prefixes have exactly one *)

Lemma ltsc_end_inv n (y : ch n) R : ltsc y (EndP n) R -> False.
Proof. by move E: (EndP n) => Q H; case: H E. Qed.

Lemma ltsw_end_inv n (y : ch n) R : ltsw y (EndP n) R -> False.
Proof. by move E: (EndP n) => Q H; case: H E. Qed.

Lemma ltsf_end_inv n (y z : ch n) R : ltsf y z (EndP n) R -> False.
Proof. by move E: (EndP n) => Q H; case: H E. Qed.

Lemma ltsr_end_inv n (y : ch n) (R : proc n.+1) : ltsr y (EndP n) R -> False.
Proof. by move E: (EndP n) => Q H; case: H E. Qed.

Lemma ltsb_end_inv n (y : ch n) (R : proc n.+2) : ltsb y (EndP n) R -> False.
Proof. by move E: (EndP n) => Q H; case: H E. Qed.

(** ** Injective renamings and shape inversion of [subst_proc] *)

Definition ren_inj m n (s : ren m n) : Prop :=
  forall z1 z2, s z1 = s z2 -> z1 = z2.

Lemma up_inj m n (s : ren m n) : ren_inj s -> ren_inj (up_ch s).
Proof.
  move=> H [a|] [b|] //= E.
  have E2 : s a = s b by case: E.
  by rewrite (H _ _ E2).
Qed.

Lemma subst_inv_close m n (s : ren m n) P y K :
  subst_proc s P = CloseP y K ->
  exists x K0, [/\ P = CloseP x K0, s x = y & subst_proc s K0 = K].
Proof. case: P => //= x K0 [E1 E2]. by exists x, K0. Qed.

Lemma subst_inv_wait m n (s : ren m n) P y K :
  subst_proc s P = WaitP y K ->
  exists x K0, [/\ P = WaitP x K0, s x = y & subst_proc s K0 = K].
Proof. case: P => //= x K0 [E1 E2]. by exists x, K0. Qed.

Lemma subst_inv_del m n (s : ren m n) P y z K :
  subst_proc s P = DelP y z K ->
  exists x w K0,
    [/\ P = DelP x w K0, s x = y, s w = z & subst_proc s K0 = K].
Proof. case: P => //= x w K0 [E1 E2 E3]. by exists x, w, K0. Qed.

Lemma subst_inv_ins m n (s : ren m n) P y (K : proc n.+1) :
  subst_proc s P = InSP y K ->
  exists x (K0 : proc m.+1),
    [/\ P = InSP x K0, s x = y & subst_proc (up_ch s) K0 = K].
Proof. case: P => //= x K0 [E1 E2]. by exists x, K0. Qed.

Lemma subst_inv_par m n (s : ren m n) P Q1 Q2 :
  subst_proc s P = Q1 ∥ Q2 ->
  exists P1 P2,
    [/\ P = P1 ∥ P2, subst_proc s P1 = Q1 & subst_proc s P2 = Q2].
Proof. case: P => //= P1 P2 [E1 E2]. by exists P1, P2. Qed.

Lemma subst_inv_res m n (s : ren m n) P (Q : proc n.+2) :
  subst_proc s P = (ν) Q ->
  exists P0 : proc m.+2,
    P = (ν) P0 /\ subst_proc (up_ch (up_ch s)) P0 = Q.
Proof. case: P => //= P0 [E]. by exists P0. Qed.

(** ** Backward equivariance: transitions of a renamed process come from
    transitions of the original (injective renamings) *)

Lemma ltsc_ren_inv n' (y : ch n') Q R (H : ltsc y Q R) :
  forall m (s : ren m n') (x : ch m) P,
    ren_inj s -> s x = y -> subst_proc s P = Q ->
    exists P', R = subst_proc s P' /\ ltsc x P P'.
Proof.
  elim: H => {n' y Q R}.
  - move=> n' y K m s x P Hinj Ex EP.
    case: (subst_inv_close EP) => x0 [K0 [E1 E2 E3]].
    have Exx : x0 = x by apply: Hinj; rewrite E2 Ex.
    subst. exists K0. split=> //. exact: LC_Pfx.
  - move=> n' y P1 P1' Q1 _ IH m s x P Hinj Ex EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ _ Hinj erefl erefl) => Pa' [-> Ha].
    exists (Pa' ∥ Pb). split=> //=. exact: LC_ParL.
  - move=> n' y P1 Q1 Q1' _ IH m s x P Hinj Ex EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ _ Hinj erefl erefl) => Pb' [-> Hb].
    exists (Pa ∥ Pb'). split=> //=. exact: LC_ParR.
  - move=> n' y P1 P1' _ IH m s x P Hinj Ex EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (IH _ _ _ _ (up_inj (up_inj Hinj)) (up2_shift2 s x) erefl) => P0' [-> H0].
    exists ((ν) P0'). split=> //=. exact: LC_Res.
Qed.

Lemma ltsw_ren_inv n' (y : ch n') Q R (H : ltsw y Q R) :
  forall m (s : ren m n') (x : ch m) P,
    ren_inj s -> s x = y -> subst_proc s P = Q ->
    exists P', R = subst_proc s P' /\ ltsw x P P'.
Proof.
  elim: H => {n' y Q R}.
  - move=> n' y K m s x P Hinj Ex EP.
    case: (subst_inv_wait EP) => x0 [K0 [E1 E2 E3]].
    have Exx : x0 = x by apply: Hinj; rewrite E2 Ex.
    subst. exists K0. split=> //. exact: LW_Pfx.
  - move=> n' y P1 P1' Q1 _ IH m s x P Hinj Ex EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ _ Hinj erefl erefl) => Pa' [-> Ha].
    exists (Pa' ∥ Pb). split=> //=. exact: LW_ParL.
  - move=> n' y P1 Q1 Q1' _ IH m s x P Hinj Ex EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ _ Hinj erefl erefl) => Pb' [-> Hb].
    exists (Pa ∥ Pb'). split=> //=. exact: LW_ParR.
  - move=> n' y P1 P1' _ IH m s x P Hinj Ex EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (IH _ _ _ _ (up_inj (up_inj Hinj)) (up2_shift2 s x) erefl) => P0' [-> H0].
    exists ((ν) P0'). split=> //=. exact: LW_Res.
Qed.

Lemma ltsf_ren_inv n' (y z : ch n') Q R (H : ltsf y z Q R) :
  forall m (s : ren m n') (x w : ch m) P,
    ren_inj s -> s x = y -> s w = z -> subst_proc s P = Q ->
    exists P', R = subst_proc s P' /\ ltsf x w P P'.
Proof.
  elim: H => {n' y z Q R}.
  - move=> n' y z K m s x w P Hinj Ex Ew EP.
    case: (subst_inv_del EP) => x0 [w0 [K0 [E1 E2 E3 E4]]].
    have Exx : x0 = x by apply: Hinj; rewrite E2 Ex.
    have Eww : w0 = w by apply: Hinj; rewrite E3 Ew.
    subst. exists K0. split=> //. exact: LF_Pfx.
  - move=> n' y z P1 P1' Q1 _ IH m s x w P Hinj Ex Ew EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ _ _ Hinj erefl erefl erefl) => Pa' [-> Ha].
    exists (Pa' ∥ Pb). split=> //=. exact: LF_ParL.
  - move=> n' y z P1 Q1 Q1' _ IH m s x w P Hinj Ex Ew EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ _ _ Hinj erefl erefl erefl) => Pb' [-> Hb].
    exists (Pa ∥ Pb'). split=> //=. exact: LF_ParR.
  - move=> n' y z P1 P1' _ IH m s x w P Hinj Ex Ew EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (IH _ _ _ _ _ (up_inj (up_inj Hinj)) (up2_shift2 s x) (up2_shift2 s w) erefl) => P0' [-> H0].
    exists ((ν) P0'). split=> //=. exact: LF_Res.
Qed.

Print Assumptions struct_eq_ren.
Print Assumptions ltsf_ren_inv.

(** ** Source-shape inversion for the close family *)

Ltac lts_inv H :=
  inversion H; subst;
  repeat match goal with
  | [ E : existT _ ?k _ = existT _ ?k _ |- _ ] =>
      apply (inj_pair2_eq_dec _ Nat.eq_dec) in E; subst
  end.

Lemma ltsc_close_inv n (y x : ch n) K R :
  ltsc y (CloseP x K) R -> y = x /\ R = K.
Proof. move=> H. by lts_inv H. Qed.

Lemma ltsc_wait_noT n (y x : ch n) K R : ltsc y (WaitP x K) R -> False.
Proof. move=> H. by lts_inv H. Qed.

Lemma ltsc_del_noT n (y x z : ch n) K R : ltsc y (DelP x z K) R -> False.
Proof. move=> H. by lts_inv H. Qed.

Lemma ltsc_ins_noT n (y x : ch n) (K : proc n.+1) R :
  ltsc y (InSP x K) R -> False.
Proof. move=> H. by lts_inv H. Qed.

Lemma ltsc_par_inv n (y : ch n) P1 P2 R :
  ltsc y (P1 ∥ P2) R ->
  (exists P1', R = P1' ∥ P2 /\ ltsc y P1 P1') \/
  (exists P2', R = P1 ∥ P2' /\ ltsc y P2 P2').
Proof.
  move=> H. lts_inv H.
  - left. eexists. split; [reflexivity | assumption].
  - right. eexists. split; [reflexivity | assumption].
Qed.

Lemma ltsc_res_inv n (y : ch n) (P0 : proc n.+2) R :
  ltsc y ((ν) P0) R ->
  exists P0', R = (ν) P0' /\ ltsc (shift (shift y)) P0 P0'.
Proof.
  move=> H. lts_inv H.
  eexists. split; [reflexivity | assumption].
Qed.

(** ** Involutions and fixed points of the swap renamings *)

Lemma swap01_invol n (z : ch n.+2) :
  swap_ch zero one (swap_ch zero one z) = z.
Proof. by case: z => [[w|]|]. Qed.

Lemma swapB_invol n (z : ch n.+4) :
  swap_ch one three (swap_ch zero two
    (swap_ch one three (swap_ch zero two z))) = z.
Proof. by case: z => [[[[w|]|]|]|]. Qed.

Lemma swap01_fix2 n (y : ch n) :
  swap_ch zero one (shift (shift y)) = shift (shift y).
Proof. by []. Qed.

Lemma swapB_fix4 n (y : ch n) :
  swap_ch one three (swap_ch zero two
    (shift (shift (shift (shift y))))) = shift (shift (shift (shift y))).
Proof. by []. Qed.

Lemma shift2_ren_inj n : ren_inj (fun z : ch n => shift (shift z)).
Proof. move=> z1 z2 E. by case: E. Qed.

Lemma subst_swap01_invol n (P : proc n.+2) :
  subst_proc (swap_ch zero one) (subst_proc (swap_ch zero one) P) = P.
Proof.
  rewrite subst_proc_comp.
  rewrite (subst_proc_ext P (t := id_ren) (fun z => swap01_invol z)).
  exact: subst_proc_id.
Qed.

(** ** Transfer for the close family *)

Lemma transfer_c m (P Q : proc m) (H : P ≅ Q) :
  forall (x : ch m),
    (forall P', ltsc x P P' -> exists Q', ltsc x Q Q' /\ P' ≅ Q') /\
    (forall Q', ltsc x Q Q' -> exists P', ltsc x P P' /\ Q' ≅ P').
Proof.
  elim: H => {m P Q}.
  - (* Par_Com *)
    move=> m P Q x; split=> R HT.
    + case: (ltsc_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * exists (Q ∥ Z). split; [exact: LC_ParR HZ | exact: SC_Par_Com].
      * exists (Z ∥ P). split; [exact: LC_ParL HZ | exact: SC_Par_Com].
    + case: (ltsc_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * exists (P ∥ Z). split; [exact: LC_ParR HZ | exact: SC_Par_Com].
      * exists (Z ∥ Q). split; [exact: LC_ParL HZ | exact: SC_Par_Com].
  - (* Par_Assoc *)
    move=> m P Q R x; split=> W HT.
    + case: (ltsc_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * case: (ltsc_par_inv HZ) => [[Y [-> HY]]|[Y [-> HY]]].
        -- exists (Y ∥ (Q ∥ R)).
           split; [exact: LC_ParL HY | exact: SC_Par_Assoc].
        -- exists (P ∥ (Y ∥ R)).
           split; [apply: LC_ParR; exact: LC_ParL HY | exact: SC_Par_Assoc].
      * exists (P ∥ (Q ∥ Z)).
        split; [apply: LC_ParR; exact: LC_ParR HZ | exact: SC_Par_Assoc].
    + case: (ltsc_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * exists (Z ∥ Q ∥ R).
        split; [apply: LC_ParL; exact: LC_ParL HZ
               | exact: SC_Sym (SC_Par_Assoc _ _ _)].
      * case: (ltsc_par_inv HZ) => [[Y [-> HY]]|[Y [-> HY]]].
        -- exists (P ∥ Y ∥ R).
           split; [apply: LC_ParL; exact: LC_ParR HY
                  | exact: SC_Sym (SC_Par_Assoc _ _ _)].
        -- exists (P ∥ Q ∥ Y).
           split; [exact: LC_ParR HY | exact: SC_Sym (SC_Par_Assoc _ _ _)].
  - (* Par_Inact *)
    move=> m P x; split=> R HT.
    + case: (ltsc_par_inv HT) => [[Z [-> HZ]]|[Z [_ /ltsc_end_inv []]]].
      exists Z. split; [exact: HZ | exact: SC_Par_Inact].
    + exists (R ∥ EndP m).
      split; [exact: LC_ParL HT | exact: SC_Sym (SC_Par_Inact _)].
  - (* Res_Scope *)
    move=> m P Q x; split=> R HT.
    + case: (ltsc_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * case: (ltsc_res_inv HZ) => Y [-> HY].
        exists ((ν) (Y ∥ subst_proc (shift \o shift) Q)).
        split; [apply: LC_Res; exact: LC_ParL HY | exact: SC_Res_Scope].
      * exists ((ν) (P ∥ subst_proc (shift \o shift) Z)).
        split.
          apply: LC_Res. apply: LC_ParR.
          by have := ltsc_ren HZ (shift \o shift).
        exact: SC_Res_Scope.
    + case: (ltsc_res_inv HT) => Z [-> HZ].
      case: (ltsc_par_inv HZ) => [[Y [-> HY]]|[Y [-> HY]]].
      * exists ((ν) Y ∥ Q).
        split; [apply: LC_ParL; exact: LC_Res HY
               | exact: SC_Sym (SC_Res_Scope _ _)].
      * case: (ltsc_ren_inv HY (@shift2_ren_inj m) erefl erefl)
          => Q1 [-> HQ].
        exists ((ν) P ∥ Q1).
        split; [exact: LC_ParR HQ | exact: SC_Sym (SC_Res_Scope _ _)].
  - (* Res_SwapC *)
    move=> m P x; split.
    + move=> R /ltsc_res_inv [Z [-> HT]].
      exists ((ν) (subst_proc (swap_ch zero one) Z)).
      split.
        apply: LC_Res.
        by have := ltsc_ren HT (swap_ch zero one); rewrite swap01_fix2.
      exact: SC_Res_SwapC.
    + move=> R /ltsc_res_inv [Z [-> HT]].
      have HT2 : ltsc (shift (shift x)) P (subst_proc (swap_ch zero one) Z).
        have := ltsc_ren HT (swap_ch zero one).
        by rewrite swap01_fix2 subst_swap01_invol.
      exists ((ν) (subst_proc (swap_ch zero one) Z)).
      split; [exact: LC_Res HT2 | exact: SC_Res_SwapC].
  - (* Res_SwapB *)
    move=> m P x; split.
    + move=> R /ltsc_res_inv [Z [-> /ltsc_res_inv [Y [-> HT]]]].
      exists ((ν) ((ν) (subst_proc (swap_ch one three)
                          (subst_proc (swap_ch zero two) Y)))).
      split.
        apply: LC_Res. apply: LC_Res.
        have := ltsc_ren (ltsc_ren HT (swap_ch zero two)) (swap_ch one three).
        by rewrite subst_proc_comp swapB_fix4.
      exact: SC_Res_SwapB.
    + move=> R /ltsc_res_inv [Z [-> /ltsc_res_inv [Y [-> HT]]]].
      have HT2 : ltsc (shift (shift (shift (shift x)))) P
                   (subst_proc (swap_ch one three)
                      (subst_proc (swap_ch zero two) Y)).
        have := ltsc_ren (ltsc_ren HT (swap_ch zero two)) (swap_ch one three).
        rewrite subst_proc_comp swapB_fix4.
        rewrite [X in ltsc _ X _ -> _]subst_proc_comp
                [X in ltsc _ X _ -> _]subst_proc_comp.
        rewrite (subst_proc_ext P (t := id_ren)) ?subst_proc_id //.
        move=> z /=. exact: swapB_invol.
      exists ((ν) ((ν) (subst_proc (swap_ch one three)
                          (subst_proc (swap_ch zero two) Y)))).
      split; [by apply: LC_Res; apply: LC_Res | exact: SC_Res_SwapB].
  - (* Res_Inact *)
    move=> m x; split=> [R /ltsc_res_inv [Z [_ /ltsc_end_inv []]]
                        |R /ltsc_end_inv []].
  - (* Refl *)
    move=> m P x; split=> R HT; exists R; split=> //; exact: SC_Refl.
  - (* Sym *)
    move=> m P Q _ IH x. case: (IH x) => IH1 IH2.
    split=> R HT.
    + case: (IH2 _ HT) => W [HW HR]. exists W. by split.
    + case: (IH1 _ HT) => W [HW HR]. exists W. by split.
  - (* Trans *)
    move=> m P Q R _ IH1 _ IH2 x.
    case: (IH1 x) => IHa IHb. case: (IH2 x) => IHc IHd.
    split=> W HT.
    + case: (IHa _ HT) => W1 [HW1 HR1]. case: (IHc _ HW1) => W2 [HW2 HR2].
      exists W2. split=> //. exact: SC_Trans HR1 HR2.
    + case: (IHd _ HT) => W1 [HW1 HR1]. case: (IHb _ HW1) => W2 [HW2 HR2].
      exists W2. split=> //. exact: SC_Trans HR1 HR2.
  - (* Cong_Par *)
    move=> m P P' Q Q' HPP IH1 HQQ IH2 x.
    case: (IH1 x) => IHa IHb. case: (IH2 x) => IHc IHd.
    split=> R /ltsc_par_inv [[Z [-> HT]]|[Z [-> HT]]].
    + case: (IHa _ HT) => W [HW HR]. exists (W ∥ Q').
      split; [exact: LC_ParL HW | exact: SC_Cong_Par HR HQQ].
    + case: (IHc _ HT) => W [HW HR]. exists (P' ∥ W).
      split; [exact: LC_ParR HW | exact: SC_Cong_Par HPP HR].
    + case: (IHb _ HT) => W [HW HR]. exists (W ∥ Q).
      split; [exact: LC_ParL HW | exact: SC_Cong_Par HR (SC_Sym HQQ)].
    + case: (IHd _ HT) => W [HW HR]. exists (P ∥ W).
      split; [exact: LC_ParR HW | exact: SC_Cong_Par (SC_Sym HPP) HR].
  - (* Cong_Res *)
    move=> m P P' _ IH x.
    case: (IH (shift (shift x))) => IHa IHb.
    split=> R /ltsc_res_inv [Z [-> HT]].
    + case: (IHa _ HT) => W [HW HR]. exists ((ν) W).
      split; [exact: LC_Res HW | exact: SC_Cong_Res HR].
    + case: (IHb _ HT) => W [HW HR]. exists ((ν) W).
      split; [exact: LC_Res HW | exact: SC_Cong_Res HR].
  - (* Cong_Close *)
    move=> m P P' y HPP IH x.
    split=> R /ltsc_close_inv [-> ->].
    + exists P'. split; [exact: LC_Pfx | exact: HPP].
    + exists P. split; [exact: LC_Pfx | exact: SC_Sym HPP].
  - (* Cong_Wait *)
    move=> m P P' y _ IH x.
    by split=> R /ltsc_wait_noT [].
  - (* Cong_OutS *)
    move=> m P P' y z _ IH x.
    by split=> R /ltsc_del_noT [].
  - (* Cong_InsP *)
    move=> m P P' y _ IH x.
    by split=> R /ltsc_ins_noT [].
Qed.

Print Assumptions transfer_c.

(** ** Source-shape inversion, wait family *)

Lemma ltsw_wait_inv n (y x : ch n) K R :
  ltsw y (WaitP x K) R -> y = x /\ R = K.
Proof. move=> H. by lts_inv H. Qed.

Lemma ltsw_close_noT n (y x : ch n) K R : ltsw y (CloseP x K) R -> False.
Proof. move=> H. by lts_inv H. Qed.

Lemma ltsw_del_noT n (y x z : ch n) K R : ltsw y (DelP x z K) R -> False.
Proof. move=> H. by lts_inv H. Qed.

Lemma ltsw_ins_noT n (y x : ch n) (K : proc n.+1) R :
  ltsw y (InSP x K) R -> False.
Proof. move=> H. by lts_inv H. Qed.

Lemma ltsw_par_inv n (y : ch n) P1 P2 R :
  ltsw y (P1 ∥ P2) R ->
  (exists P1', R = P1' ∥ P2 /\ ltsw y P1 P1') \/
  (exists P2', R = P1 ∥ P2' /\ ltsw y P2 P2').
Proof.
  move=> H. lts_inv H.
  - left. eexists. split; [reflexivity | assumption].
  - right. eexists. split; [reflexivity | assumption].
Qed.

Lemma ltsw_res_inv n (y : ch n) (P0 : proc n.+2) R :
  ltsw y ((ν) P0) R ->
  exists P0', R = (ν) P0' /\ ltsw (shift (shift y)) P0 P0'.
Proof.
  move=> H. lts_inv H.
  eexists. split; [reflexivity | assumption].
Qed.

(** ** Transfer for the wait family *)

Lemma transfer_w m (P Q : proc m) (H : P ≅ Q) :
  forall (x : ch m),
    (forall P', ltsw x P P' -> exists Q', ltsw x Q Q' /\ P' ≅ Q') /\
    (forall Q', ltsw x Q Q' -> exists P', ltsw x P P' /\ Q' ≅ P').
Proof.
  elim: H => {m P Q}.
  - (* Par_Com *)
    move=> m P Q x; split=> R HT.
    + case: (ltsw_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * exists (Q ∥ Z). split; [exact: LW_ParR HZ | exact: SC_Par_Com].
      * exists (Z ∥ P). split; [exact: LW_ParL HZ | exact: SC_Par_Com].
    + case: (ltsw_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * exists (P ∥ Z). split; [exact: LW_ParR HZ | exact: SC_Par_Com].
      * exists (Z ∥ Q). split; [exact: LW_ParL HZ | exact: SC_Par_Com].
  - (* Par_Assoc *)
    move=> m P Q R x; split=> W HT.
    + case: (ltsw_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * case: (ltsw_par_inv HZ) => [[Y [-> HY]]|[Y [-> HY]]].
        -- exists (Y ∥ (Q ∥ R)).
           split; [exact: LW_ParL HY | exact: SC_Par_Assoc].
        -- exists (P ∥ (Y ∥ R)).
           split; [apply: LW_ParR; exact: LW_ParL HY | exact: SC_Par_Assoc].
      * exists (P ∥ (Q ∥ Z)).
        split; [apply: LW_ParR; exact: LW_ParR HZ | exact: SC_Par_Assoc].
    + case: (ltsw_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * exists (Z ∥ Q ∥ R).
        split; [apply: LW_ParL; exact: LW_ParL HZ
               | exact: SC_Sym (SC_Par_Assoc _ _ _)].
      * case: (ltsw_par_inv HZ) => [[Y [-> HY]]|[Y [-> HY]]].
        -- exists (P ∥ Y ∥ R).
           split; [apply: LW_ParL; exact: LW_ParR HY
                  | exact: SC_Sym (SC_Par_Assoc _ _ _)].
        -- exists (P ∥ Q ∥ Y).
           split; [exact: LW_ParR HY | exact: SC_Sym (SC_Par_Assoc _ _ _)].
  - (* Par_Inact *)
    move=> m P x; split=> R HT.
    + case: (ltsw_par_inv HT) => [[Z [-> HZ]]|[Z [_ /ltsw_end_inv []]]].
      exists Z. split; [exact: HZ | exact: SC_Par_Inact].
    + exists (R ∥ EndP m).
      split; [exact: LW_ParL HT | exact: SC_Sym (SC_Par_Inact _)].
  - (* Res_Scope *)
    move=> m P Q x; split=> R HT.
    + case: (ltsw_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * case: (ltsw_res_inv HZ) => Y [-> HY].
        exists ((ν) (Y ∥ subst_proc (shift \o shift) Q)).
        split; [apply: LW_Res; exact: LW_ParL HY | exact: SC_Res_Scope].
      * exists ((ν) (P ∥ subst_proc (shift \o shift) Z)).
        split.
          apply: LW_Res. apply: LW_ParR.
          by have := ltsw_ren HZ (shift \o shift).
        exact: SC_Res_Scope.
    + case: (ltsw_res_inv HT) => Z [-> HZ].
      case: (ltsw_par_inv HZ) => [[Y [-> HY]]|[Y [-> HY]]].
      * exists ((ν) Y ∥ Q).
        split; [apply: LW_ParL; exact: LW_Res HY
               | exact: SC_Sym (SC_Res_Scope _ _)].
      * case: (ltsw_ren_inv HY (@shift2_ren_inj m) erefl erefl)
          => Q1 [-> HQ].
        exists ((ν) P ∥ Q1).
        split; [exact: LW_ParR HQ | exact: SC_Sym (SC_Res_Scope _ _)].
  - (* Res_SwapC *)
    move=> m P x; split.
    + move=> R /ltsw_res_inv [Z [-> HT]].
      exists ((ν) (subst_proc (swap_ch zero one) Z)).
      split.
        apply: LW_Res.
        by have := ltsw_ren HT (swap_ch zero one); rewrite swap01_fix2.
      exact: SC_Res_SwapC.
    + move=> R /ltsw_res_inv [Z [-> HT]].
      have HT2 : ltsw (shift (shift x)) P (subst_proc (swap_ch zero one) Z).
        have := ltsw_ren HT (swap_ch zero one).
        by rewrite swap01_fix2 subst_swap01_invol.
      exists ((ν) (subst_proc (swap_ch zero one) Z)).
      split; [exact: LW_Res HT2 | exact: SC_Res_SwapC].
  - (* Res_SwapB *)
    move=> m P x; split.
    + move=> R /ltsw_res_inv [Z [-> /ltsw_res_inv [Y [-> HT]]]].
      exists ((ν) ((ν) (subst_proc (swap_ch one three)
                          (subst_proc (swap_ch zero two) Y)))).
      split.
        apply: LW_Res. apply: LW_Res.
        have := ltsw_ren (ltsw_ren HT (swap_ch zero two)) (swap_ch one three).
        by rewrite subst_proc_comp swapB_fix4.
      exact: SC_Res_SwapB.
    + move=> R /ltsw_res_inv [Z [-> /ltsw_res_inv [Y [-> HT]]]].
      have HT2 : ltsw (shift (shift (shift (shift x)))) P
                   (subst_proc (swap_ch one three)
                      (subst_proc (swap_ch zero two) Y)).
        have := ltsw_ren (ltsw_ren HT (swap_ch zero two)) (swap_ch one three).
        rewrite subst_proc_comp swapB_fix4.
        rewrite [X in ltsw _ X _ -> _]subst_proc_comp
                [X in ltsw _ X _ -> _]subst_proc_comp.
        rewrite (subst_proc_ext P (t := id_ren)) ?subst_proc_id //.
        move=> z /=. exact: swapB_invol.
      exists ((ν) ((ν) (subst_proc (swap_ch one three)
                          (subst_proc (swap_ch zero two) Y)))).
      split; [by apply: LW_Res; apply: LW_Res | exact: SC_Res_SwapB].
  - (* Res_Inact *)
    move=> m x; split=> [R /ltsw_res_inv [Z [_ /ltsw_end_inv []]]
                        |R /ltsw_end_inv []].
  - (* Refl *)
    move=> m P x; split=> R HT; exists R; split=> //; exact: SC_Refl.
  - (* Sym *)
    move=> m P Q _ IH x. case: (IH x) => IH1 IH2.
    split=> R HT.
    + case: (IH2 _ HT) => W [HW HR]. exists W. by split.
    + case: (IH1 _ HT) => W [HW HR]. exists W. by split.
  - (* Trans *)
    move=> m P Q R _ IH1 _ IH2 x.
    case: (IH1 x) => IHa IHb. case: (IH2 x) => IHc IHd.
    split=> W HT.
    + case: (IHa _ HT) => W1 [HW1 HR1]. case: (IHc _ HW1) => W2 [HW2 HR2].
      exists W2. split=> //. exact: SC_Trans HR1 HR2.
    + case: (IHd _ HT) => W1 [HW1 HR1]. case: (IHb _ HW1) => W2 [HW2 HR2].
      exists W2. split=> //. exact: SC_Trans HR1 HR2.
  - (* Cong_Par *)
    move=> m P P' Q Q' HPP IH1 HQQ IH2 x.
    case: (IH1 x) => IHa IHb. case: (IH2 x) => IHc IHd.
    split=> R /ltsw_par_inv [[Z [-> HT]]|[Z [-> HT]]].
    + case: (IHa _ HT) => W [HW HR]. exists (W ∥ Q').
      split; [exact: LW_ParL HW | exact: SC_Cong_Par HR HQQ].
    + case: (IHc _ HT) => W [HW HR]. exists (P' ∥ W).
      split; [exact: LW_ParR HW | exact: SC_Cong_Par HPP HR].
    + case: (IHb _ HT) => W [HW HR]. exists (W ∥ Q).
      split; [exact: LW_ParL HW | exact: SC_Cong_Par HR (SC_Sym HQQ)].
    + case: (IHd _ HT) => W [HW HR]. exists (P ∥ W).
      split; [exact: LW_ParR HW | exact: SC_Cong_Par (SC_Sym HPP) HR].
  - (* Cong_Res *)
    move=> m P P' _ IH x.
    case: (IH (shift (shift x))) => IHa IHb.
    split=> R /ltsw_res_inv [Z [-> HT]].
    + case: (IHa _ HT) => W [HW HR]. exists ((ν) W).
      split; [exact: LW_Res HW | exact: SC_Cong_Res HR].
    + case: (IHb _ HT) => W [HW HR]. exists ((ν) W).
      split; [exact: LW_Res HW | exact: SC_Cong_Res HR].
  - (* Cong_Close *)
    move=> m P P' y _ IH x.
    by split=> R /ltsw_close_noT [].
  - (* Cong_Wait *)
    move=> m P P' y HPP IH x.
    split=> R /ltsw_wait_inv [-> ->].
    + exists P'. split; [exact: LW_Pfx | exact: HPP].
    + exists P. split; [exact: LW_Pfx | exact: SC_Sym HPP].
  - (* Cong_OutS *)
    move=> m P P' y z _ IH x.
    by split=> R /ltsw_del_noT [].
  - (* Cong_InsP *)
    move=> m P P' y _ IH x.
    by split=> R /ltsw_ins_noT [].
Qed.

Print Assumptions transfer_w.

(** ** Source-shape inversion, free-send family *)

Lemma ltsf_del_inv n (y z x w : ch n) K R :
  ltsf y z (DelP x w K) R -> [/\ y = x, z = w & R = K].
Proof. move=> H. by lts_inv H. Qed.

Lemma ltsf_close_noT n (y z x : ch n) K R : ltsf y z (CloseP x K) R -> False.
Proof. move=> H. by lts_inv H. Qed.

Lemma ltsf_wait_noT n (y z x : ch n) K R : ltsf y z (WaitP x K) R -> False.
Proof. move=> H. by lts_inv H. Qed.

Lemma ltsf_ins_noT n (y z x : ch n) (K : proc n.+1) R :
  ltsf y z (InSP x K) R -> False.
Proof. move=> H. by lts_inv H. Qed.

Lemma ltsf_par_inv n (y z : ch n) P1 P2 R :
  ltsf y z (P1 ∥ P2) R ->
  (exists P1', R = P1' ∥ P2 /\ ltsf y z P1 P1') \/
  (exists P2', R = P1 ∥ P2' /\ ltsf y z P2 P2').
Proof.
  move=> H. lts_inv H.
  - left. eexists. split; [reflexivity | assumption].
  - right. eexists. split; [reflexivity | assumption].
Qed.

Lemma ltsf_res_inv n (y z : ch n) (P0 : proc n.+2) R :
  ltsf y z ((ν) P0) R ->
  exists P0', R = (ν) P0' /\
              ltsf (shift (shift y)) (shift (shift z)) P0 P0'.
Proof.
  move=> H. lts_inv H.
  eexists. split; [reflexivity | assumption].
Qed.

(** Existential backward equivariance for the free-send family: subject
    AND payload of any transition of a renamed process are in the image
    (needed to analyse bound-send transitions of compounds). *)
Lemma up2_image_shift2 m n (s : ren m n) (a : ch m.+2) (b : ch n) :
  up_ch (up_ch s) a = shift (shift b) ->
  exists a0, a = shift (shift a0) /\ s a0 = b.
Proof.
  case: a => [[w|]|] //= E.
  have E2 : s w = b by case: E.
  by exists w; rewrite E2.
Qed.

Lemma ltsf_ren_inv2 n' (y z : ch n') Q R (H : ltsf y z Q R) :
  forall m (s : ren m n') P,
    ren_inj s -> subst_proc s P = Q ->
    exists x w P',
      [/\ y = s x, z = s w, R = subst_proc s P' & ltsf x w P P'].
Proof.
  elim: H => {n' y z Q R}.
  - move=> n' y z K m s P Hinj EP.
    case: (subst_inv_del EP) => x0 [w0 [K0 [E1 E2 E3 E4]]]. subst.
    exists x0, w0, K0. split=> //. exact: LF_Pfx.
  - move=> n' y z P1 P1' Q1 _ IH m s P Hinj EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ Hinj erefl) => x0 [w0 [Pa' [E1 E2 -> Ha]]].
    exists x0, w0, (Pa' ∥ Pb). split=> //=. exact: LF_ParL.
  - move=> n' y z P1 Q1 Q1' _ IH m s P Hinj EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ Hinj erefl) => x0 [w0 [Pb' [E1 E2 -> Hb]]].
    exists x0, w0, (Pa ∥ Pb'). split=> //=. exact: LF_ParR.
  - move=> n' y z P1 P1' _ IH m s P Hinj EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (IH _ _ _ (up_inj (up_inj Hinj)) erefl)
      => x0 [w0 [P0' [E1 E2 -> H0]]].
    case: (up2_image_shift2 (esym E1)) => x1 [Ex1 Ex2].
    case: (up2_image_shift2 (esym E2)) => w1 [Ew1 Ew2].
    subst. exists x1, w1, ((ν) P0'). split=> //=. exact: LF_Res.
Qed.

(** ** Transfer for the free-send family *)

Lemma transfer_f m (P Q : proc m) (H : P ≅ Q) :
  forall (x y : ch m),
    (forall P', ltsf x y P P' -> exists Q', ltsf x y Q Q' /\ P' ≅ Q') /\
    (forall Q', ltsf x y Q Q' -> exists P', ltsf x y P P' /\ Q' ≅ P').
Proof.
  elim: H => {m P Q}.
  - (* Par_Com *)
    move=> m P Q x y; split=> R HT.
    + case: (ltsf_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * exists (Q ∥ Z). split; [exact: LF_ParR HZ | exact: SC_Par_Com].
      * exists (Z ∥ P). split; [exact: LF_ParL HZ | exact: SC_Par_Com].
    + case: (ltsf_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * exists (P ∥ Z). split; [exact: LF_ParR HZ | exact: SC_Par_Com].
      * exists (Z ∥ Q). split; [exact: LF_ParL HZ | exact: SC_Par_Com].
  - (* Par_Assoc *)
    move=> m P Q R x y; split=> W HT.
    + case: (ltsf_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * case: (ltsf_par_inv HZ) => [[Y [-> HY]]|[Y [-> HY]]].
        -- exists (Y ∥ (Q ∥ R)).
           split; [exact: LF_ParL HY | exact: SC_Par_Assoc].
        -- exists (P ∥ (Y ∥ R)).
           split; [apply: LF_ParR; exact: LF_ParL HY | exact: SC_Par_Assoc].
      * exists (P ∥ (Q ∥ Z)).
        split; [apply: LF_ParR; exact: LF_ParR HZ | exact: SC_Par_Assoc].
    + case: (ltsf_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * exists (Z ∥ Q ∥ R).
        split; [apply: LF_ParL; exact: LF_ParL HZ
               | exact: SC_Sym (SC_Par_Assoc _ _ _)].
      * case: (ltsf_par_inv HZ) => [[Y [-> HY]]|[Y [-> HY]]].
        -- exists (P ∥ Y ∥ R).
           split; [apply: LF_ParL; exact: LF_ParR HY
                  | exact: SC_Sym (SC_Par_Assoc _ _ _)].
        -- exists (P ∥ Q ∥ Y).
           split; [exact: LF_ParR HY | exact: SC_Sym (SC_Par_Assoc _ _ _)].
  - (* Par_Inact *)
    move=> m P x y; split=> R HT.
    + case: (ltsf_par_inv HT) => [[Z [-> HZ]]|[Z [_ /ltsf_end_inv []]]].
      exists Z. split; [exact: HZ | exact: SC_Par_Inact].
    + exists (R ∥ EndP m).
      split; [exact: LF_ParL HT | exact: SC_Sym (SC_Par_Inact _)].
  - (* Res_Scope *)
    move=> m P Q x y; split=> R HT.
    + case: (ltsf_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * case: (ltsf_res_inv HZ) => Y [-> HY].
        exists ((ν) (Y ∥ subst_proc (shift \o shift) Q)).
        split; [apply: LF_Res; exact: LF_ParL HY | exact: SC_Res_Scope].
      * exists ((ν) (P ∥ subst_proc (shift \o shift) Z)).
        split.
          apply: LF_Res. apply: LF_ParR.
          by have := ltsf_ren HZ (shift \o shift).
        exact: SC_Res_Scope.
    + case: (ltsf_res_inv HT) => Z [-> HZ].
      case: (ltsf_par_inv HZ) => [[Y [-> HY]]|[Y [-> HY]]].
      * exists ((ν) Y ∥ Q).
        split; [apply: LF_ParL; exact: LF_Res HY
               | exact: SC_Sym (SC_Res_Scope _ _)].
      * case: (ltsf_ren_inv HY (@shift2_ren_inj m) erefl erefl erefl)
          => Q1 [-> HQ].
        exists ((ν) P ∥ Q1).
        split; [exact: LF_ParR HQ | exact: SC_Sym (SC_Res_Scope _ _)].
  - (* Res_SwapC *)
    move=> m P x y; split.
    + move=> R /ltsf_res_inv [Z [-> HT]].
      exists ((ν) (subst_proc (swap_ch zero one) Z)).
      split.
        apply: LF_Res.
        by have := ltsf_ren HT (swap_ch zero one); rewrite !swap01_fix2.
      exact: SC_Res_SwapC.
    + move=> R /ltsf_res_inv [Z [-> HT]].
      have HT2 : ltsf (shift (shift x)) (shift (shift y)) P
                   (subst_proc (swap_ch zero one) Z).
        have := ltsf_ren HT (swap_ch zero one).
        by rewrite !swap01_fix2 subst_swap01_invol.
      exists ((ν) (subst_proc (swap_ch zero one) Z)).
      split; [exact: LF_Res HT2 | exact: SC_Res_SwapC].
  - (* Res_SwapB *)
    move=> m P x y; split.
    + move=> R /ltsf_res_inv [Z [-> /ltsf_res_inv [Y [-> HT]]]].
      exists ((ν) ((ν) (subst_proc (swap_ch one three)
                          (subst_proc (swap_ch zero two) Y)))).
      split.
        apply: LF_Res. apply: LF_Res.
        have := ltsf_ren (ltsf_ren HT (swap_ch zero two)) (swap_ch one three).
        by rewrite subst_proc_comp !swapB_fix4.
      exact: SC_Res_SwapB.
    + move=> R /ltsf_res_inv [Z [-> /ltsf_res_inv [Y [-> HT]]]].
      have HT2 : ltsf (shift (shift (shift (shift x))))
                      (shift (shift (shift (shift y)))) P
                   (subst_proc (swap_ch one three)
                      (subst_proc (swap_ch zero two) Y)).
        have := ltsf_ren (ltsf_ren HT (swap_ch zero two)) (swap_ch one three).
        rewrite subst_proc_comp !swapB_fix4.
        rewrite [X in ltsf _ _ X _ -> _]subst_proc_comp
                [X in ltsf _ _ X _ -> _]subst_proc_comp.
        rewrite (subst_proc_ext P (t := id_ren)) ?subst_proc_id //.
        move=> z /=. exact: swapB_invol.
      exists ((ν) ((ν) (subst_proc (swap_ch one three)
                          (subst_proc (swap_ch zero two) Y)))).
      split; [by apply: LF_Res; apply: LF_Res | exact: SC_Res_SwapB].
  - (* Res_Inact *)
    move=> m x y; split=> [R /ltsf_res_inv [Z [_ /ltsf_end_inv []]]
                          |R /ltsf_end_inv []].
  - (* Refl *)
    move=> m P x y; split=> R HT; exists R; split=> //; exact: SC_Refl.
  - (* Sym *)
    move=> m P Q _ IH x y. case: (IH x y) => IH1 IH2.
    split=> R HT.
    + case: (IH2 _ HT) => W [HW HR]. exists W. by split.
    + case: (IH1 _ HT) => W [HW HR]. exists W. by split.
  - (* Trans *)
    move=> m P Q R _ IH1 _ IH2 x y.
    case: (IH1 x y) => IHa IHb. case: (IH2 x y) => IHc IHd.
    split=> W HT.
    + case: (IHa _ HT) => W1 [HW1 HR1]. case: (IHc _ HW1) => W2 [HW2 HR2].
      exists W2. split=> //. exact: SC_Trans HR1 HR2.
    + case: (IHd _ HT) => W1 [HW1 HR1]. case: (IHb _ HW1) => W2 [HW2 HR2].
      exists W2. split=> //. exact: SC_Trans HR1 HR2.
  - (* Cong_Par *)
    move=> m P P' Q Q' HPP IH1 HQQ IH2 x y.
    case: (IH1 x y) => IHa IHb. case: (IH2 x y) => IHc IHd.
    split=> R /ltsf_par_inv [[Z [-> HT]]|[Z [-> HT]]].
    + case: (IHa _ HT) => W [HW HR]. exists (W ∥ Q').
      split; [exact: LF_ParL HW | exact: SC_Cong_Par HR HQQ].
    + case: (IHc _ HT) => W [HW HR]. exists (P' ∥ W).
      split; [exact: LF_ParR HW | exact: SC_Cong_Par HPP HR].
    + case: (IHb _ HT) => W [HW HR]. exists (W ∥ Q).
      split; [exact: LF_ParL HW | exact: SC_Cong_Par HR (SC_Sym HQQ)].
    + case: (IHd _ HT) => W [HW HR]. exists (P ∥ W).
      split; [exact: LF_ParR HW | exact: SC_Cong_Par (SC_Sym HPP) HR].
  - (* Cong_Res *)
    move=> m P P' _ IH x y.
    case: (IH (shift (shift x)) (shift (shift y))) => IHa IHb.
    split=> R /ltsf_res_inv [Z [-> HT]].
    + case: (IHa _ HT) => W [HW HR]. exists ((ν) W).
      split; [exact: LF_Res HW | exact: SC_Cong_Res HR].
    + case: (IHb _ HT) => W [HW HR]. exists ((ν) W).
      split; [exact: LF_Res HW | exact: SC_Cong_Res HR].
  - (* Cong_Close *)
    move=> m P P' w _ IH x y.
    by split=> R /ltsf_close_noT [].
  - (* Cong_Wait *)
    move=> m P P' w _ IH x y.
    by split=> R /ltsf_wait_noT [].
  - (* Cong_OutS *)
    move=> m P P' w v HPP IH x y.
    split=> R /ltsf_del_inv [-> -> ->].
    + exists P'. split; [exact: LF_Pfx | exact: HPP].
    + exists P. split; [exact: LF_Pfx | exact: SC_Sym HPP].
  - (* Cong_InsP *)
    move=> m P P' w _ IH x y.
    by split=> R /ltsf_ins_noT [].
Qed.

Print Assumptions transfer_f.

(** ** Backward equivariance, receive and bound-send families *)

Lemma ltsr_ren_inv n' (y : ch n') Q (R : proc n'.+1) (H : ltsr y Q R) :
  forall m (s : ren m n') (x : ch m) P,
    ren_inj s -> s x = y -> subst_proc s P = Q ->
    exists P', R = subst_proc (up_ch s) P' /\ ltsr x P P'.
Proof.
  elim: H => {n' y Q R}.
  - move=> n' y K m s x P Hinj Ex EP.
    case: (subst_inv_ins EP) => x0 [K0 [E1 E2 E3]].
    have Exx : x0 = x by apply: Hinj; rewrite E2 Ex.
    subst. exists K0. split=> //. exact: LR_Pfx.
  - move=> n' y P1 P1' Q1 _ IH m s x P Hinj Ex EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ _ Hinj erefl erefl) => Pa' [-> Ha].
    exists (Pa' ∥ subst_proc shift Pb). split; last exact: LR_ParL.
    by rewrite /= !subst_proc_comp; congr (_ ∥ _); apply: subst_eqP => -[w|].
  - move=> n' y P1 Q1 Q1' _ IH m s x P Hinj Ex EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ _ Hinj erefl erefl) => Pb' [-> Hb].
    exists (subst_proc shift Pa ∥ Pb'). split; last exact: LR_ParR.
    by rewrite /= !subst_proc_comp; congr (_ ∥ _); apply: subst_eqP => -[w|].
  - move=> n' y P1 P1' _ IH m s x P Hinj Ex EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (IH _ _ _ _ (up_inj (up_inj Hinj)) (up2_shift2 s x) erefl)
      => P0' [-> H0].
    exists ((ν) (subst_proc rho3 P0')). split; last exact: LR_Res.
    by rewrite /= !subst_proc_comp; congr ResP;
       apply: subst_eqP => -[[[w|]|]|].
Qed.

Lemma up2_image_zero m n (s : ren m n) (w : ch m.+2) :
  up_ch (up_ch s) w = zero -> w = zero.
Proof. by case: w => [[v|]|]. Qed.

Lemma up2_image_one m n (s : ren m n) (w : ch m.+2) :
  up_ch (up_ch s) w = one -> w = one.
Proof. by case: w => [[v|]|]. Qed.

Lemma ltsb_ren_inv n' (y : ch n') Q (R : proc n'.+2) (H : ltsb y Q R) :
  forall m (s : ren m n') (x : ch m) P,
    ren_inj s -> s x = y -> subst_proc s P = Q ->
    exists P', R = subst_proc (up_ch (up_ch s)) P' /\ ltsb x P P'.
Proof.
  elim: H => {n' y Q R}.
  - (* Open0 *)
    move=> n' y P1 P1' Hf m s x P Hinj Ex EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (ltsf_ren_inv2 Hf (up_inj (up_inj Hinj)) erefl)
      => x0 [w0 [P0' [E1 E2 -> Hff]]].
    case: (up2_image_shift2 (esym E1)) => x1 [Ex1 Ex2].
    have Exx : x1 = x by apply: Hinj; rewrite Ex2.
    have Ew : w0 = zero by apply: up2_image_zero (esym E2).
    subst. exists P0'. split=> //. exact: LB_Open0.
  - (* Open1 *)
    move=> n' y P1 P1' Hf m s x P Hinj Ex EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (ltsf_ren_inv2 Hf (up_inj (up_inj Hinj)) erefl)
      => x0 [w0 [P0' [E1 E2 -> Hff]]].
    case: (up2_image_shift2 (esym E1)) => x1 [Ex1 Ex2].
    have Exx : x1 = x by apply: Hinj; rewrite Ex2.
    have Ew : w0 = one by apply: up2_image_one (esym E2).
    subst. exists (subst_proc (swap_ch zero one) P0').
    split; last exact: LB_Open1.
    rewrite !subst_proc_comp. apply: subst_eqP => z.
    by rewrite /= swap01_up2.
  - (* ParL *)
    move=> n' y P1 P1' Q1 _ IH m s x P Hinj Ex EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ _ Hinj erefl erefl) => Pa' [-> Ha].
    exists (Pa' ∥ subst_proc (shift \o shift) Pb). split; last exact: LB_ParL.
    by rewrite /= !subst_proc_comp; congr (_ ∥ _); apply: subst_eqP => -[w|].
  - (* ParR *)
    move=> n' y P1 Q1 Q1' _ IH m s x P Hinj Ex EP.
    case: (subst_inv_par EP) => Pa [Pb [E1 E2 E3]]. subst.
    case: (IH _ _ _ _ Hinj erefl erefl) => Pb' [-> Hb].
    exists (subst_proc (shift \o shift) Pa ∥ Pb'). split; last exact: LB_ParR.
    by rewrite /= !subst_proc_comp; congr (_ ∥ _); apply: subst_eqP => -[w|].
  - (* Res *)
    move=> n' y P1 P1' _ IH m s x P Hinj Ex EP.
    case: (subst_inv_res EP) => P0 [E1 E2]. subst.
    case: (IH _ _ _ _ (up_inj (up_inj Hinj)) (up2_shift2 s x) erefl)
      => P0' [-> H0].
    exists ((ν) (subst_proc (swap_ch one three)
                   (subst_proc (swap_ch zero two) P0'))).
    split; last exact: LB_Res.
    by rewrite /= !subst_proc_comp; congr ResP;
       apply: subst_eqP => -[[[[w|]|]|]|].
Qed.

(** ** rho3 bridges *)

Lemma rho3_shift n (z : ch n.+2) : rho3 (shift z) = up_ch (up_ch shift) z.
Proof. by case: z => [[w|]|]. Qed.

Lemma rho3_upshift2 n (z : ch n.+1) :
  rho3 (up_ch (shift \o shift) z) = shift (shift z).
Proof. by case: z. Qed.

(** ** Source-shape inversion, receive family *)

Lemma ltsr_ins_inv n (y x : ch n) (K : proc n.+1) R :
  ltsr y (InSP x K) R -> y = x /\ R = K.
Proof. move=> H. by lts_inv H. Qed.

Lemma ltsr_close_noT n (y x : ch n) K R : ltsr y (CloseP x K) R -> False.
Proof. move=> H. by lts_inv H. Qed.

Lemma ltsr_wait_noT n (y x : ch n) K R : ltsr y (WaitP x K) R -> False.
Proof. move=> H. by lts_inv H. Qed.

Lemma ltsr_del_noT n (y x z : ch n) K R : ltsr y (DelP x z K) R -> False.
Proof. move=> H. by lts_inv H. Qed.

Lemma ltsr_par_inv n (y : ch n) P1 P2 R :
  ltsr y (P1 ∥ P2) R ->
  (exists P1', R = P1' ∥ subst_proc shift P2 /\ ltsr y P1 P1') \/
  (exists P2', R = subst_proc shift P1 ∥ P2' /\ ltsr y P2 P2').
Proof.
  move=> H. lts_inv H.
  - left. eexists. split; [reflexivity | assumption].
  - right. eexists. split; [reflexivity | assumption].
Qed.

Lemma ltsr_res_inv n (y : ch n) (P0 : proc n.+2) R :
  ltsr y ((ν) P0) R ->
  exists P0', R = (ν) (subst_proc rho3 P0') /\
              ltsr (shift (shift y)) P0 P0'.
Proof.
  move=> H. lts_inv H.
  eexists. split; [reflexivity | assumption].
Qed.

(** ** Transfer for the receive family *)

Lemma transfer_r m (P Q : proc m) (H : P ≅ Q) :
  forall (x : ch m),
    (forall P', ltsr x P P' -> exists Q', ltsr x Q Q' /\ P' ≅ Q') /\
    (forall Q', ltsr x Q Q' -> exists P', ltsr x P P' /\ Q' ≅ P').
Proof.
  elim: H => {m P Q}.
  - (* Par_Com *)
    move=> m P Q x; split=> R HT.
    + case: (ltsr_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * exists (subst_proc shift Q ∥ Z).
        split; [exact: LR_ParR HZ | exact: SC_Par_Com].
      * exists (Z ∥ subst_proc shift P).
        split; [exact: LR_ParL HZ | exact: SC_Par_Com].
    + case: (ltsr_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * exists (subst_proc shift P ∥ Z).
        split; [exact: LR_ParR HZ | exact: SC_Par_Com].
      * exists (Z ∥ subst_proc shift Q).
        split; [exact: LR_ParL HZ | exact: SC_Par_Com].
  - (* Par_Assoc *)
    move=> m P Q R x; split=> W HT.
    + case: (ltsr_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * case: (ltsr_par_inv HZ) => [[Y [-> HY]]|[Y [-> HY]]].
        -- exists (Y ∥ subst_proc shift (Q ∥ R)).
           split; [exact: LR_ParL HY | exact: SC_Par_Assoc].
        -- exists (subst_proc shift P ∥ (Y ∥ subst_proc shift R)).
           split; [apply: LR_ParR; exact: LR_ParL HY | exact: SC_Par_Assoc].
      * exists (subst_proc shift P ∥ (subst_proc shift Q ∥ Z)).
        split; [apply: LR_ParR; exact: LR_ParR HZ | exact: SC_Par_Assoc].
    + case: (ltsr_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * exists (Z ∥ subst_proc shift Q ∥ subst_proc shift R).
        split; [apply: LR_ParL; exact: LR_ParL HZ
               | exact: SC_Sym (SC_Par_Assoc _ _ _)].
      * case: (ltsr_par_inv HZ) => [[Y [-> HY]]|[Y [-> HY]]].
        -- exists (subst_proc shift P ∥ Y ∥ subst_proc shift R).
           split; [apply: LR_ParL; exact: LR_ParR HY
                  | exact: SC_Sym (SC_Par_Assoc _ _ _)].
        -- exists (subst_proc shift (P ∥ Q) ∥ Y).
           split; [exact: LR_ParR HY | exact: SC_Sym (SC_Par_Assoc _ _ _)].
  - (* Par_Inact *)
    move=> m P x; split=> R HT.
    + case: (ltsr_par_inv HT) => [[Z [-> HZ]]|[Z [_ /ltsr_end_inv []]]].
      exists Z. split; [exact: HZ | exact: SC_Par_Inact].
    + exists (R ∥ subst_proc shift (EndP m)).
      split; [exact: LR_ParL HT | exact: SC_Sym (SC_Par_Inact _)].
  - (* Res_Scope *)
    move=> m P Q x; split=> R HT.
    + case: (ltsr_par_inv HT) => [[Z [-> HZ]]|[Z [-> HZ]]].
      * case: (ltsr_res_inv HZ) => Y [-> HY].
        exists ((ν) (subst_proc rho3 (Y ∥ subst_proc shift
                       (subst_proc (shift \o shift) Q)))).
        split.
          apply: LR_Res. exact: LR_ParL HY.
        have -> : subst_proc rho3 (Y ∥ subst_proc shift
                    (subst_proc (shift \o shift) Q))
                = subst_proc rho3 Y ∥
                  subst_proc (shift \o shift) (subst_proc shift Q).
          by rewrite /= !subst_proc_comp; congr (_ ∥ _);
             apply: subst_eqP => -[w|].
        exact: SC_Res_Scope.
      * exists ((ν) (subst_proc rho3 (subst_proc shift P ∥
                       subst_proc (up_ch (shift \o shift)) Z))).
        split.
          apply: LR_Res. apply: LR_ParR.
          by have := ltsr_ren HZ (shift \o shift).
        have -> : subst_proc rho3 (subst_proc shift P ∥
                    subst_proc (up_ch (shift \o shift)) Z)
                = subst_proc (up_ch (up_ch shift)) P ∥
                  subst_proc (shift \o shift) Z.
          by rewrite /= !subst_proc_comp; congr (_ ∥ _);
             [apply: subst_eqP => -[[w|]|] | apply: subst_eqP => -[w|]].
        exact: SC_Res_Scope.
    + case: (ltsr_res_inv HT) => Z [-> HZ].
      case: (ltsr_par_inv HZ) => [[Y [-> HY]]|[Y [-> HY]]].
      * exists ((ν) (subst_proc rho3 Y) ∥ subst_proc shift Q).
        split.
          apply: LR_ParL. exact: LR_Res HY.
        have -> : subst_proc rho3 (Y ∥ subst_proc shift
                    (subst_proc (shift \o shift) Q))
                = subst_proc rho3 Y ∥
                  subst_proc (shift \o shift) (subst_proc shift Q).
          by rewrite /= !subst_proc_comp; congr (_ ∥ _);
             apply: subst_eqP => -[w|].
        exact: SC_Sym (SC_Res_Scope _ _).
      * case: (ltsr_ren_inv HY (@shift2_ren_inj m) erefl erefl) => Q1 [-> HQ].
        exists (subst_proc shift ((ν) P) ∥ Q1).
        split.
          apply: LR_ParR. exact: HQ.
        have -> : subst_proc rho3 (subst_proc shift P ∥
                    subst_proc (up_ch (shift \o shift)) Q1)
                = subst_proc (up_ch (up_ch shift)) P ∥
                  subst_proc (shift \o shift) Q1.
          by rewrite /= !subst_proc_comp; congr (_ ∥ _);
             [apply: subst_eqP => -[[w|]|] | apply: subst_eqP => -[w|]].
        exact: SC_Sym (SC_Res_Scope _ _).
  - (* Res_SwapC *)
    move=> m P x; split.
    + move=> R /ltsr_res_inv [Z [-> HT]].
      exists ((ν) (subst_proc rho3
                     (subst_proc (up_ch (swap_ch zero one)) Z))).
      split.
        apply: LR_Res.
        by have := ltsr_ren HT (swap_ch zero one); rewrite swap01_fix2.
      have -> : subst_proc rho3 (subst_proc (up_ch (swap_ch zero one)) Z)
              = subst_proc (swap_ch zero one) (subst_proc rho3 Z).
        by rewrite !subst_proc_comp; apply: subst_eqP => -[[[w|]|]|].
      exact: SC_Res_SwapC.
    + move=> R /ltsr_res_inv [Z [-> HT]].
      have HT2 : ltsr (shift (shift x)) P
                   (subst_proc (up_ch (swap_ch zero one)) Z).
        have HX := ltsr_ren HT (swap_ch zero one).
        by rewrite swap01_fix2 subst_swap01_invol in HX.
      exists ((ν) (subst_proc rho3
                     (subst_proc (up_ch (swap_ch zero one)) Z))).
      split. exact: LR_Res HT2.
      have -> : subst_proc rho3 (subst_proc (up_ch (swap_ch zero one)) Z)
              = subst_proc (swap_ch zero one) (subst_proc rho3 Z).
        by rewrite !subst_proc_comp; apply: subst_eqP => -[[[w|]|]|].
      exact: SC_Res_SwapC.
  - (* Res_SwapB *)
    move=> m P x; split.
    + move=> R /ltsr_res_inv [Z [-> /ltsr_res_inv [Y [-> HY]]]].
      exists ((ν) (subst_proc rho3 ((ν) (subst_proc rho3
                (subst_proc (up_ch (swap_ch one three))
                   (subst_proc (up_ch (swap_ch zero two)) Y)))))).
      split.
        apply: LR_Res. apply: LR_Res.
        have HX := ltsr_ren (ltsr_ren HY (swap_ch zero two))
                            (swap_ch one three).
        rewrite swapB_fix4 in HX. exact: HX.
      have -> : subst_proc rho3 ((ν) (subst_proc rho3
                   (subst_proc (up_ch (swap_ch one three))
                      (subst_proc (up_ch (swap_ch zero two)) Y))))
              = (ν) (subst_proc (swap_ch one three)
                       (subst_proc (swap_ch zero two)
                          (subst_proc (up_ch (up_ch rho3))
                             (subst_proc rho3 Y)))).
        by rewrite /= !subst_proc_comp; congr ResP;
           apply: subst_eqP => -[[[[[w|]|]|]|]|].
      exact: SC_Res_SwapB.
    + move=> R /ltsr_res_inv [Z [-> /ltsr_res_inv [Y [-> HY]]]].
      have HX := ltsr_ren (ltsr_ren HY (swap_ch zero two))
                          (swap_ch one three).
      rewrite swapB_fix4 in HX.
      rewrite ![in X in ltsr _ X _]subst_proc_comp in HX.
      rewrite (subst_proc_ext P (t := id_ren) (fun z => swapB_invol z))
              subst_proc_id in HX.
      exists ((ν) (subst_proc rho3 ((ν) (subst_proc rho3
                (subst_proc (up_ch (swap_ch one three))
                   (subst_proc (up_ch (swap_ch zero two)) Y)))))).
      split.
        apply: LR_Res. apply: LR_Res. exact: HX.
      have -> : subst_proc rho3 ((ν) (subst_proc rho3
                   (subst_proc (up_ch (swap_ch one three))
                      (subst_proc (up_ch (swap_ch zero two)) Y))))
              = (ν) (subst_proc (swap_ch one three)
                       (subst_proc (swap_ch zero two)
                          (subst_proc (up_ch (up_ch rho3))
                             (subst_proc rho3 Y)))).
        by rewrite /= !subst_proc_comp; congr ResP;
           apply: subst_eqP => -[[[[[w|]|]|]|]|].
      exact: SC_Res_SwapB.
  - (* Res_Inact *)
    move=> m x; split=> [R /ltsr_res_inv [Z [_ /ltsr_end_inv []]]
                        |R /ltsr_end_inv []].
  - (* Refl *)
    move=> m P x; split=> R HT; exists R; split=> //; exact: SC_Refl.
  - (* Sym *)
    move=> m P Q _ IH x. case: (IH x) => IH1 IH2.
    split=> R HT.
    + case: (IH2 _ HT) => W [HW HR]. exists W. by split.
    + case: (IH1 _ HT) => W [HW HR]. exists W. by split.
  - (* Trans *)
    move=> m P Q R _ IH1 _ IH2 x.
    case: (IH1 x) => IHa IHb. case: (IH2 x) => IHc IHd.
    split=> W HT.
    + case: (IHa _ HT) => W1 [HW1 HR1]. case: (IHc _ HW1) => W2 [HW2 HR2].
      exists W2. split=> //. exact: SC_Trans HR1 HR2.
    + case: (IHd _ HT) => W1 [HW1 HR1]. case: (IHb _ HW1) => W2 [HW2 HR2].
      exists W2. split=> //. exact: SC_Trans HR1 HR2.
  - (* Cong_Par *)
    move=> m P P' Q Q' HPP IH1 HQQ IH2 x.
    case: (IH1 x) => IHa IHb. case: (IH2 x) => IHc IHd.
    split=> R /ltsr_par_inv [[Z [-> HT]]|[Z [-> HT]]].
    + case: (IHa _ HT) => W [HW HR]. exists (W ∥ subst_proc shift Q').
      split; first exact: LR_ParL HW.
      exact: (SC_Cong_Par HR (struct_eq_ren HQQ shift)).
    + case: (IHc _ HT) => W [HW HR]. exists (subst_proc shift P' ∥ W).
      split; first exact: LR_ParR HW.
      exact: (SC_Cong_Par (struct_eq_ren HPP shift) HR).
    + case: (IHb _ HT) => W [HW HR]. exists (W ∥ subst_proc shift Q).
      split; first exact: LR_ParL HW.
      exact: (SC_Cong_Par HR (SC_Sym (struct_eq_ren HQQ shift))).
    + case: (IHd _ HT) => W [HW HR]. exists (subst_proc shift P ∥ W).
      split; first exact: LR_ParR HW.
      exact: (SC_Cong_Par (SC_Sym (struct_eq_ren HPP shift)) HR).
  - (* Cong_Res *)
    move=> m P P' _ IH x.
    case: (IH (shift (shift x))) => IHa IHb.
    split=> R /ltsr_res_inv [Z [-> HT]].
    + case: (IHa _ HT) => W [HW HR]. exists ((ν) (subst_proc rho3 W)).
      split; first exact: LR_Res HW.
      exact: (SC_Cong_Res (struct_eq_ren HR rho3)).
    + case: (IHb _ HT) => W [HW HR]. exists ((ν) (subst_proc rho3 W)).
      split; first exact: LR_Res HW.
      exact: (SC_Cong_Res (struct_eq_ren HR rho3)).
  - (* Cong_Close *)
    move=> m P P' y _ IH x.
    by split=> R /ltsr_close_noT [].
  - (* Cong_Wait *)
    move=> m P P' y _ IH x.
    by split=> R /ltsr_wait_noT [].
  - (* Cong_OutS *)
    move=> m P P' y z _ IH x.
    by split=> R /ltsr_del_noT [].
  - (* Cong_InsP *)
    move=> m P P' y HPP IH x.
    split=> R /ltsr_ins_inv [-> ->].
    + exists P'. split; [exact: LR_Pfx | exact: HPP].
    + exists P. split; [exact: LR_Pfx | exact: SC_Sym HPP].
Qed.

Print Assumptions transfer_r.
