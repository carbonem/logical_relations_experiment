(** * Offer determination, and the ∅ rule

    A prefix offers exactly one action, at exactly its own subject:
    [offers_close] and friends read a hypothetical [offersP] back off
    the syntax, killing every obligation of the value interpretation
    except the one belonging to the prefix's own head.  Every
    compatibility proof in [PolFN.v] opens with one of them.

    Also here: [compat_endP], the ∅ rule, which is the one
    compatibility lemma with nothing σ-dependent to say (a context of
    all-[None] pushes forward to a context of all-[None]), so
    [fcompat_end] simply calls it.

    HISTORY.  This file used to hold closed-world compatibility
    lemmas for close, wait and free delegation too.  The fundamental
    theorem is stated in substitution form, and its σ-parametric
    versions ([fcompat_close], [fcompat_wait], [fcompat_del]) must
    also handle a MERGED subject -- an endpoint whose σ-image carries
    both ends -- which the closed-world versions cannot express; they
    are superseded, and sit in [cemetery/attic/PolAttic.v]. *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import PolBase PolTypes PolProc PolLTS
  PolErr PolTyping PolLogRel.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope pol_scope.

(** ** Offer determination for the axial shapes *)

Lemma offers_end n a (c : pch n) : offersP a c (∅ : procP n) -> False.
Proof.
  case: a => /=.
  - case=> R HT. by case: (pinv_c_end HT).
  - case=> R HT. by case: (pinv_w_end HT).
  - case=> [[d [R HT]]|[r [R HT]]];
      [by case: (pinv_f_end HT) | by case: (pinv_b_end HT)].
  - case=> d [R HT]. by case: (pinv_r_end HT).
  - case=> b [R HT]. by case: (pinv_sel_end HT).
  - case=> b [R HT]. by case: (pinv_br_end HT).
Qed.

Lemma offers_close n a (c e : pch n) K :
  offersP a c (PClose e K) -> a = AClose /\ c = e.
Proof.
  case: a => /=.
  - case=> R HT. by case: (pinv_c_closeF HT) => -> _.
  - case=> R HT. by case: (pinv_w_close HT).
  - case=> [[d [R HT]]|[r [R HT]]];
      [by case: (pinv_f_close2 HT) | by case: (pinv_b_close HT)].
  - case=> d [R HT]. by case: (pinv_r_close2 HT).
  - case=> b [R HT]. by case: (pinv_sel_close HT).
  - case=> b [R HT]. by case: (pinv_br_close HT).
Qed.

Lemma offers_wait n a (c e : pch n) K :
  offersP a c (PWait e K) -> a = AWait /\ c = e.
Proof.
  case: a => /=.
  - case=> R HT. by case: (pinv_c_wait HT).
  - case=> R HT. by case: (pinv_w_waitF HT) => -> _.
  - case=> [[d [R HT]]|[r [R HT]]];
      [by case: (pinv_f_wait2 HT) | by case: (pinv_b_wait HT)].
  - case=> d [R HT]. by case: (pinv_r_wait2 HT).
  - case=> b [R HT]. by case: (pinv_sel_wait HT).
  - case=> b [R HT]. by case: (pinv_br_wait HT).
Qed.

Lemma offers_del n a (c e p : pch n) K :
  offersP a c (PDel e p K) -> a = ADelS /\ c = e.
Proof.
  case: a => /=.
  - case=> R HT. by case: (pinv_c_del HT).
  - case=> R HT. by case: (pinv_w_del HT).
  - case=> [[d [R HT]]|[r [R HT]]];
      [by case: (pinv_f_delF HT) => -> _ _ | by case: (pinv_b_del HT)].
  - case=> d [R HT]. by case: (pinv_r_del HT).
  - case=> b [R HT]. by case: (pinv_sel_del HT).
  - case=> b [R HT]. by case: (pinv_br_del HT).
Qed.

Lemma offers_ins n a (c e : pch n) (r : pol) (K : procP n.+1) :
  offersP a c (PIns e r K) -> a = ADelR /\ c = e.
Proof.
  case: a => /=.
  - case=> R HT. by case: (pinv_c_ins HT).
  - case=> R HT. by case: (pinv_w_ins HT).
  - case=> [[d [R HT]]|[r' [R HT]]];
      [by case: (pinv_f_ins HT) | by case: (pinv_b_ins HT)].
  - case=> d [R HT]. by case: (pinv_r_insF HT) => -> _ _.
  - case=> b [R HT]. by case: (pinv_sel_ins HT).
  - case=> b [R HT]. by case: (pinv_br_ins HT).
Qed.

Lemma pol_eqb_refl r : pol_eqb r r = true.
Proof. by case: r. Qed.

(** ** ∅ *)
Lemma compat_endP n (Δ : sctxP n) :
  (forall x, Δ x = None) -> SEMP Δ (∅ : procP n).
Proof.
  move=> HD k. case: k => [//|k]. split.
  - split=> //.
    move=> a c Hof. by case: (offers_end Hof).
  - move=> w rw S HwS. by rewrite HD in HwS.
  - move=> P' Hst. by case: (pinv_t_end Hst).
Qed.

(** ** Axiom audit *)

Lemma offers_sel n a (c e : pch n) (b : bool) K :
  offersP a c (e ◁ b ․ K) -> a = ASel /\ c = e.
Proof.
  case: a => /=.
  - case=> R HT. by case: (pinv_c_sel HT).
  - case=> R HT. by case: (pinv_w_sel HT).
  - case=> [[d [R HT]]|[r [R HT]]];
      [by case: (pinv_f_sel HT) | by case: (pinv_b_sel HT)].
  - case=> d [R HT]. by case: (pinv_r_sel HT).
  - case=> b' [R HT]. by case: (pinv_sel_selF HT) => -> _ _.
  - case=> b' [R HT]. by case: (pinv_br_sel HT).
Qed.

Lemma offers_bra n a (c e : pch n) K1 K2 :
  offersP a c (e ▷ ( K1 | K2 )) -> a = ABra /\ c = e.
Proof.
  case: a => /=.
  - case=> R HT. by case: (pinv_c_bra HT).
  - case=> R HT. by case: (pinv_w_bra HT).
  - case=> [[d [R HT]]|[r [R HT]]];
      [by case: (pinv_f_bra HT) | by case: (pinv_b_bra HT)].
  - case=> d [R HT]. by case: (pinv_r_bra HT).
  - case=> b' [R HT]. by case: (pinv_sel_bra HT).
  - case=> b' [R HT]. by case: (pinv_br_braF HT) => -> _.
Qed.
