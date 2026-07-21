(** * Discharging the exposure interface

    The four prefix-exposure inversion hypotheses of [Fundamental.v],
    now theorems.  Uniform pattern: an exposed prefix gives the compound
    a transition (syntax); transfer carries it across the congruence to
    the rigid prefix source; source inversion pins the action, the
    subject, and the residue.  The three wrong-action cases die on the
    no-transition lemmas.  No induction over [≅] anywhere in this file:
    that debt was paid once, in [Transfer.v]. *)

From mathcomp Require Import all_ssreflect.
From Tait Require Import synsem Errors LogRel Toolkit LTS Transfer.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma close_expo_inv n (x : ch n) K a (y : ch n) F R :
  CloseP x K ≅ F ∥ R -> prefix_at a y F ->
  exists K0, [/\ a = AClose, y = x, F = CloseP x K0 & K ≅ K0 ∥ R].
Proof.
  move=> Heq Hpa. case: Hpa Heq => {a y F}.
  - move=> y K1 Heq.
    have HT : ltsc y (CloseP y K1 ∥ R) (K1 ∥ R).
      apply: LC_ParL. exact: LC_Pfx.
    case: (transfer_c Heq y) => _ Hd.
    case: (Hd _ HT) => W [HW HR].
    case: (ltsc_close_inv HW) => Exy EW. subst.
    exists K1. split=> //. exact: SC_Sym HR.
  - move=> y K1 Heq.
    have HT : ltsw y (WaitP y K1 ∥ R) (K1 ∥ R).
      apply: LW_ParL. exact: LW_Pfx.
    case: (transfer_w Heq y) => _ Hd.
    case: (Hd _ HT) => W [HW _].
    by case: (ltsw_close_noT HW).
  - move=> y z K1 Heq.
    have HT : ltsf y z (DelP y z K1 ∥ R) (K1 ∥ R).
      apply: LF_ParL. exact: LF_Pfx.
    case: (transfer_f Heq y z) => _ Hd.
    case: (Hd _ HT) => W [HW _].
    by case: (ltsf_close_noT HW).
  - move=> y K1 Heq.
    have HT : ltsr y (InSP y K1 ∥ R) (K1 ∥ subst_proc shift R).
      apply: LR_ParL. exact: LR_Pfx.
    case: (transfer_r Heq y) => _ Hd.
    case: (Hd _ HT) => W [HW _].
    by case: (ltsr_close_noT HW).
Qed.

Lemma wait_expo_inv n (x : ch n) K a (y : ch n) F R :
  WaitP x K ≅ F ∥ R -> prefix_at a y F ->
  exists K0, [/\ a = AWait, y = x, F = WaitP x K0 & K ≅ K0 ∥ R].
Proof.
  move=> Heq Hpa. case: Hpa Heq => {a y F}.
  - move=> y K1 Heq.
    have HT : ltsc y (CloseP y K1 ∥ R) (K1 ∥ R).
      apply: LC_ParL. exact: LC_Pfx.
    case: (transfer_c Heq y) => _ Hd.
    case: (Hd _ HT) => W [HW _].
    by case: (ltsc_wait_noT HW).
  - move=> y K1 Heq.
    have HT : ltsw y (WaitP y K1 ∥ R) (K1 ∥ R).
      apply: LW_ParL. exact: LW_Pfx.
    case: (transfer_w Heq y) => _ Hd.
    case: (Hd _ HT) => W [HW HR].
    case: (ltsw_wait_inv HW) => Exy EW. subst.
    exists K1. split=> //. exact: SC_Sym HR.
  - move=> y z K1 Heq.
    have HT : ltsf y z (DelP y z K1 ∥ R) (K1 ∥ R).
      apply: LF_ParL. exact: LF_Pfx.
    case: (transfer_f Heq y z) => _ Hd.
    case: (Hd _ HT) => W [HW _].
    by case: (ltsf_wait_noT HW).
  - move=> y K1 Heq.
    have HT : ltsr y (InSP y K1 ∥ R) (K1 ∥ subst_proc shift R).
      apply: LR_ParL. exact: LR_Pfx.
    case: (transfer_r Heq y) => _ Hd.
    case: (Hd _ HT) => W [HW _].
    by case: (ltsr_wait_noT HW).
Qed.

Lemma del_expo_inv n (x z : ch n) K a (y : ch n) F R :
  DelP x z K ≅ F ∥ R -> prefix_at a y F ->
  exists K0, [/\ a = ADelS, y = x, F = DelP x z K0 & K ≅ K0 ∥ R].
Proof.
  move=> Heq Hpa. case: Hpa Heq => {a y F}.
  - move=> y K1 Heq.
    have HT : ltsc y (CloseP y K1 ∥ R) (K1 ∥ R).
      apply: LC_ParL. exact: LC_Pfx.
    case: (transfer_c Heq y) => _ Hd.
    case: (Hd _ HT) => W [HW _].
    by case: (ltsc_del_noT HW).
  - move=> y K1 Heq.
    have HT : ltsw y (WaitP y K1 ∥ R) (K1 ∥ R).
      apply: LW_ParL. exact: LW_Pfx.
    case: (transfer_w Heq y) => _ Hd.
    case: (Hd _ HT) => W [HW _].
    by case: (ltsw_del_noT HW).
  - move=> y w K1 Heq.
    have HT : ltsf y w (DelP y w K1 ∥ R) (K1 ∥ R).
      apply: LF_ParL. exact: LF_Pfx.
    case: (transfer_f Heq y w) => _ Hd.
    case: (Hd _ HT) => W [HW HR].
    case: (ltsf_del_inv HW) => Exy Ezw EW. subst.
    exists K1. split=> //. exact: SC_Sym HR.
  - move=> y K1 Heq.
    have HT : ltsr y (InSP y K1 ∥ R) (K1 ∥ subst_proc shift R).
      apply: LR_ParL. exact: LR_Pfx.
    case: (transfer_r Heq y) => _ Hd.
    case: (Hd _ HT) => W [HW _].
    by case: (ltsr_del_noT HW).
Qed.

Lemma ins_expo_inv n (x : ch n) (K : proc n.+1) a (y : ch n) F R :
  InSP x K ≅ F ∥ R -> prefix_at a y F ->
  exists K0 : proc n.+1,
    [/\ a = ADelR, y = x, F = InSP x K0 & K ≅ K0 ∥ subst_proc shift R].
Proof.
  move=> Heq Hpa. case: Hpa Heq => {a y F}.
  - move=> y K1 Heq.
    have HT : ltsc y (CloseP y K1 ∥ R) (K1 ∥ R).
      apply: LC_ParL. exact: LC_Pfx.
    case: (transfer_c Heq y) => _ Hd.
    case: (Hd _ HT) => W [HW _].
    by case: (ltsc_ins_noT HW).
  - move=> y K1 Heq.
    have HT : ltsw y (WaitP y K1 ∥ R) (K1 ∥ R).
      apply: LW_ParL. exact: LW_Pfx.
    case: (transfer_w Heq y) => _ Hd.
    case: (Hd _ HT) => W [HW _].
    by case: (ltsw_ins_noT HW).
  - move=> y z K1 Heq.
    have HT : ltsf y z (DelP y z K1 ∥ R) (K1 ∥ R).
      apply: LF_ParL. exact: LF_Pfx.
    case: (transfer_f Heq y z) => _ Hd.
    case: (Hd _ HT) => W [HW _].
    by case: (ltsf_ins_noT HW).
  - move=> y K1 Heq.
    have HT : ltsr y (InSP y K1 ∥ R) (K1 ∥ subst_proc shift R).
      apply: LR_ParL. exact: LR_Pfx.
    case: (transfer_r Heq y) => _ Hd.
    case: (Hd _ HT) => W [HW HR].
    case: (ltsr_ins_inv HW) => Exy EW. subst.
    exists K1. split=> //. exact: SC_Sym HR.
Qed.

Print Assumptions close_expo_inv.
Print Assumptions ins_expo_inv.
