(** * Equivariance of the polarized LTS: the backward direction

    A transition of [psubst s P] comes from a transition of [P], with
    the subject an image.  These inversions are injectivity-FREE: the
    subject and the object come out existentially, and the receive
    inversion returns an OPEN residual with a uniform family over the
    received name (a received name need not be in the image of [s] at
    all).  Compared to the double-binder development the stack is
    small: early input leaves parallel frames unshifted, the inert ν
    needs no [open_recv], and the only surviving renaming juggle is
    [PB_Res]'s [swap_ch zero one].

    Note what is NOT here.  Backward τ-inversion needs the two
    co-subjects to share a preimage name; full injectivity would give
    that, but the substitution lemma cannot supply it (a collapse
    [scons y id] merges [zero] with [shift y] by construction).  The
    usable form is the coverage-guarded [ltstP_ren_inv_cov] in
    [PolSem.v]: injectivity only on the names [P] actually offers at,
    which conformance provides.  A non-injective renaming can merge
    two names and thereby CREATE synchronizations; that phenomenon is
    handled semantically, in the fuse clause of the receive
    interpretation, not syntactically here.

    The forward direction ([lts*P_ren]) is likewise absent: the
    fundamental theorem consumes renaming backwards only.  The single
    exception kept live is [ltsrP_ren], which [compat_resP] uses to
    conjugate a receive through a binder by [swap_ch zero one].  The
    rest is in [cemetery/attic/PolAttic.v]. *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import PolBase PolTypes PolProc PolLTS PolErr.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope pol_scope.

(** ** Commutation algebra *)

Lemma pren_up_pshift m n (s : ren m n) (c : pch m) :
  pren (up_ch s) (pshift c) = pshift (pren s c).
Proof. by case: c. Qed.

Lemma psubst_shift_comm m n (s : ren m n) (Q : procP m) :
  psubst (up_ch s) (psubst shift Q) = psubst shift (psubst s Q).
Proof. rewrite !psubst_comp. by apply: psubst_ext => z. Qed.

Lemma psubst_scons_comm m n (s : ren m n) (y : ch m) (K : procP m.+1) :
  psubst (scons (s y) id_ren) (psubst (up_ch s) K)
  = psubst s (psubst (scons y id_ren) K).
Proof. rewrite !psubst_comp. by apply: psubst_ext => -[z|]. Qed.

Lemma psubst_swap01_comm m n (s : ren m n) (B : procP m.+2) :
  psubst (up_ch (up_ch s)) (psubst (swap_ch zero one) B)
  = psubst (swap_ch zero one) (psubst (up_ch (up_ch s)) B).
Proof. rewrite !psubst_comp. by apply: psubst_ext => -[[z|]|]. Qed.

Lemma ltsrP_ren n (c d : pch n) P P' (H : ltsrP c d P P') :
  forall m (s : ren n m),
    ltsrP (pren s c) (pren s d) (psubst s P) (psubst s P').
Proof.
  elim: H => {n c d P P'}.
  - move=> n c y r K m s /=.
    rewrite -psubst_scons_comm. exact: (PR_Pfx (pren s c) (s y) r).
  - move=> n c d P P' Q _ IH m s /=. exact: PR_ParL (IH _ _).
  - move=> n c d P Q Q' _ IH m s /=. exact: PR_ParR (IH _ _).
  - move=> n c d P P' _ IH m s /=.
    apply: PR_Res. rewrite -!pren_up_pshift. exact: IH.
Qed.

Lemma psubst_inv_close m n (s : ren m n) P e K :
  psubst s P = PClose e K ->
  exists c K0, [/\ P = PClose c K0, e = pren s c & K = psubst s K0].
Proof.
  case: P => //= c K0 [E1 E2]. exists c, K0. by rewrite E1 E2.
Qed.

Lemma psubst_inv_wait m n (s : ren m n) P e K :
  psubst s P = PWait e K ->
  exists c K0, [/\ P = PWait c K0, e = pren s c & K = psubst s K0].
Proof.
  case: P => //= c K0 [E1 E2]. exists c, K0. by rewrite E1 E2.
Qed.

Lemma psubst_inv_del m n (s : ren m n) P e p K :
  psubst s P = PDel e p K ->
  exists c d K0,
    [/\ P = PDel c d K0, e = pren s c, p = pren s d & K = psubst s K0].
Proof.
  case: P => //= c d K0 [E1 E2 E3]. exists c, d, K0. by rewrite E1 E2 E3.
Qed.

Lemma psubst_inv_ins m n (s : ren m n) P e (r : pol) (K : procP n.+1) :
  psubst s P = PIns e r K ->
  exists c (K0 : procP m.+1),
    [/\ P = PIns c r K0, e = pren s c & K = psubst (up_ch s) K0].
Proof.
  case: P => //= c r0 K0 [E1 E2 E3]. exists c, K0. by rewrite E1 E2 E3.
Qed.

Lemma psubst_inv_par m n (s : ren m n) P A B :
  psubst s P = PPar A B ->
  exists A0 B0, [/\ P = PPar A0 B0, A = psubst s A0 & B = psubst s B0].
Proof.
  case: P => //= A0 B0 [E1 E2]. exists A0, B0. by rewrite E1 E2.
Qed.

Lemma psubst_inv_sel m n (s : ren m n) P e (b : bool) K :
  psubst s P = PSel e b K ->
  exists c K0, [/\ P = PSel c b K0, e = pren s c & K = psubst s K0].
Proof.
  case: P => //= c b0 K0 [E1 E2 E3]. exists c, K0.
  by rewrite E1 E2 E3.
Qed.

Lemma psubst_inv_bra m n (s : ren m n) P e K1 K2 :
  psubst s P = PBra e K1 K2 ->
  exists c K10 K20,
    [/\ P = PBra c K10 K20, e = pren s c,
        K1 = psubst s K10 & K2 = psubst s K20].
Proof.
  case: P => //= c K10 K20 [E1 E2 E3]. exists c, K10, K20.
  by rewrite E1 E2 E3.
Qed.

Lemma psubst_inv_res m n (s : ren m n) P (B : procP n.+1) :
  psubst s P = PRes B ->
  exists B0, P = PRes B0 /\ B = psubst (up_ch s) B0.
Proof.
  case: P => //= B0 [E1]. exists B0. by rewrite E1.
Qed.

(** ** Pulling names back through [up_ch] *)

Lemma up_image_shift m n (s : ren m n) (w : ch m.+1) (v : ch n) :
  up_ch s w = shift v -> exists w0, w = shift w0 /\ s w0 = v.
Proof.
  case: w => [w0|] //= E.
  exists w0. split=> //.
  exact: (f_equal (fun c : ch n.+1 => if c is Some u then u else v) E).
Qed.

Lemma up_image_zero m n (s : ren m n) (w : ch m.+1) :
  up_ch s w = zero -> w = zero.
Proof. by case: w. Qed.

Lemma pren_up_image_pshift m n (s : ren m n) (cb : pch m.+1) (C : pch n) :
  pren (up_ch s) cb = pshift C ->
  exists c0, cb = pshift c0 /\ pren s c0 = C.
Proof.
  case: cb => wb rb; case: C => v rv -[E1 E2]. subst rv.
  case: (up_image_shift E1) => w0 [-> Es].
  exists (w0, rb). by rewrite /pshift /pren /= Es.
Qed.

Lemma pren_up_image_zero m n (s : ren m n) (cb : pch m.+1) (r : pol) :
  pren (up_ch s) cb = (zero, r) -> cb = (zero, r).
Proof.
  case: cb => wb rb -[E1 E2]. subst rb.
  by rewrite (up_image_zero E1).
Qed.

(** ** Backward equivariance (existential, injectivity-free) *)

Lemma ltscP_ren_inv n' (C : pch n') X R (H : ltscP C X R) :
  forall m (s : ren m n') P,
    psubst s P = X ->
    exists c P0, [/\ C = pren s c, R = psubst s P0 & ltscP c P P0].
Proof.
  elim: H => {n' C X R}.
  - move=> n' C K m s P EP.
    case: (psubst_inv_close EP) => c [K0 [-> -> ->]].
    exists c, K0. split=> //. exact: PC_Pfx.
  - move=> n' C A A' B _ IH m s P EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]]. rewrite EB.
    case: (IH _ _ _ (esym EA)) => c [P0 [E1 -> H0]].
    exists c, (P0 ∥ B0). split=> //=. exact: PC_ParL H0.
  - move=> n' C A B B' _ IH m s P EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]]. rewrite EA.
    case: (IH _ _ _ (esym EB)) => c [P0 [E1 -> H0]].
    exists c, (A0 ∥ P0). split=> //=. exact: PC_ParR H0.
  - move=> n' C B B' _ IH m s P EP.
    case: (psubst_inv_res EP) => B0 [-> EB]. 
    case: (IH _ _ _ (esym EB)) => cb [P0 [E1 -> H0]].
    case: (pren_up_image_pshift (esym E1)) => c0 [Ecb EC].
    exists c0, ((ν) P0). split=> //=.
    apply: PC_Res. by rewrite -Ecb.
Qed.

Lemma ltswP_ren_inv n' (C : pch n') X R (H : ltswP C X R) :
  forall m (s : ren m n') P,
    psubst s P = X ->
    exists c P0, [/\ C = pren s c, R = psubst s P0 & ltswP c P P0].
Proof.
  elim: H => {n' C X R}.
  - move=> n' C K m s P EP.
    case: (psubst_inv_wait EP) => c [K0 [-> -> ->]].
    exists c, K0. split=> //. exact: PW_Pfx.
  - move=> n' C A A' B _ IH m s P EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]]. rewrite EB.
    case: (IH _ _ _ (esym EA)) => c [P0 [E1 -> H0]].
    exists c, (P0 ∥ B0). split=> //=. exact: PW_ParL H0.
  - move=> n' C A B B' _ IH m s P EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]]. rewrite EA.
    case: (IH _ _ _ (esym EB)) => c [P0 [E1 -> H0]].
    exists c, (A0 ∥ P0). split=> //=. exact: PW_ParR H0.
  - move=> n' C B B' _ IH m s P EP.
    case: (psubst_inv_res EP) => B0 [-> EB]. 
    case: (IH _ _ _ (esym EB)) => cb [P0 [E1 -> H0]].
    case: (pren_up_image_pshift (esym E1)) => c0 [Ecb EC].
    exists c0, ((ν) P0). split=> //=.
    apply: PW_Res. by rewrite -Ecb.
Qed.

Lemma ltsfP_ren_inv n' (C D : pch n') X R (H : ltsfP C D X R) :
  forall m (s : ren m n') P,
    psubst s P = X ->
    exists c d P0,
      [/\ C = pren s c, D = pren s d, R = psubst s P0 & ltsfP c d P P0].
Proof.
  elim: H => {n' C D X R}.
  - move=> n' C D K m s P EP.
    case: (psubst_inv_del EP) => c [d [K0 [-> -> -> ->]]].
    exists c, d, K0. split=> //. exact: PF_Pfx.
  - move=> n' C D A A' B _ IH m s P EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]]. rewrite EB.
    case: (IH _ _ _ (esym EA)) => c [d [P0 [E1 E2 -> H0]]].
    exists c, d, (P0 ∥ B0). split=> //=. exact: PF_ParL H0.
  - move=> n' C D A B B' _ IH m s P EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]]. rewrite EA.
    case: (IH _ _ _ (esym EB)) => c [d [P0 [E1 E2 -> H0]]].
    exists c, d, (A0 ∥ P0). split=> //=. exact: PF_ParR H0.
  - move=> n' C D B B' _ IH m s P EP.
    case: (psubst_inv_res EP) => B0 [-> EB]. 
    case: (IH _ _ _ (esym EB)) => cb [db [P0 [E1 E2 -> H0]]].
    case: (pren_up_image_pshift (esym E1)) => c0 [Ecb EC].
    case: (pren_up_image_pshift (esym E2)) => d0 [Edb ED].
    exists c0, d0, ((ν) P0). split=> //=.
    apply: PF_Res. by rewrite -Ecb -Edb.
Qed.

Lemma ltsrP_ren_inv n' (C D : pch n') X R (H : ltsrP C D X R) :
  forall m (s : ren m n') P,
    psubst s P = X ->
    exists c (P0 : procP m.+1),
      [/\ C = pren s c,
          R = psubst (scons D.1 s) P0
        & forall y : ch m, ltsrP c (y, D.2) P (psubst (scons y id_ren) P0)].
Proof.
  elim: H => {n' C D X R}.
  - move=> n' C y r K m s P EP.
    case: (psubst_inv_ins EP) => c [K0 [-> -> ->]].
    exists c, K0. split=> //=.
    + rewrite !psubst_comp. by apply: psubst_ext => -[z|].
    + move=> y0. exact: PR_Pfx.
  - move=> n' C D A A' B _ IH m s P EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]]. rewrite EB.
    case: (IH _ _ _ (esym EA)) => c [P0 [E1 -> Hu]].
    exists c, (P0 ∥ psubst shift B0). split=> //=.
    + congr (_ ∥ _). rewrite !psubst_comp. by apply: psubst_ext => z.
    + move=> y0.
      have -> : psubst (scons y0 id_ren) (psubst shift B0) = B0.
        rewrite psubst_comp -[RHS]psubst_id.
        by apply: psubst_ext => z.
      exact: PR_ParL (Hu y0).
  - move=> n' C D A B B' _ IH m s P EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]]. rewrite EA.
    case: (IH _ _ _ (esym EB)) => c [P0 [E1 -> Hu]].
    exists c, (psubst shift A0 ∥ P0). split=> //=.
    + congr (_ ∥ _). rewrite !psubst_comp. by apply: psubst_ext => z.
    + move=> y0.
      have -> : psubst (scons y0 id_ren) (psubst shift A0) = A0.
        rewrite psubst_comp -[RHS]psubst_id.
        by apply: psubst_ext => z.
      exact: PR_ParR (Hu y0).
  - move=> n' C D B B' _ IH m s P EP.
    case: (psubst_inv_res EP) => B0 [-> EB]. 
    case: (IH _ _ _ (esym EB)) => cb [P0 [E1 ER Hu]].
    case: (pren_up_image_pshift (esym E1)) => c0 [Ecb EC].
    exists c0, ((ν) (psubst (swap_ch zero one) P0)). split=> //=.
    + rewrite ER !psubst_comp. congr PRes.
      by apply: psubst_ext => -[[z|]|].
    + move=> y0.
      have -> : psubst (up_ch (scons y0 id_ren)) (psubst (swap_ch zero one) P0)
              = psubst (scons (shift y0) id_ren) P0.
        rewrite !psubst_comp.
        by apply: psubst_ext => -[[z|]|].
      apply: PR_Res. rewrite -Ecb.
      have -> : pshift ((y0, D.2) : pch m) = ((shift y0, D.2) : pch m.+1)
        by [].
      exact: Hu.
Qed.

Lemma ltsbP_ren_inv n' (C : pch n') (r : pol) X (R : procP n'.+1)
    (H : ltsbP C r X R) :
  forall m (s : ren m n') P,
    psubst s P = X ->
    exists c (P0 : procP m.+1),
      [/\ C = pren s c, R = psubst (up_ch s) P0 & ltsbP c r P P0].
Proof.
  elim: H => {n' C r X R}.
  - move=> n' C r B B' Hf m s P EP.
    case: (psubst_inv_res EP) => B0 [-> EB]. 
    case: (ltsfP_ren_inv Hf (esym EB)) => cb [db [P0 [E1 E2 -> H0]]].
    case: (pren_up_image_pshift (esym E1)) => c0 [Ecb EC].
    have Edb : db = ((zero, r) : pch m.+1).
      exact: pren_up_image_zero (esym E2).
    exists c0, P0. split=> //.
    apply: PB_Open. rewrite -Ecb -Edb. exact: H0.
  - move=> n' C r A A' B _ IH m s P EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]]. rewrite EB.
    case: (IH _ _ _ (esym EA)) => c [P0 [E1 -> H0]].
    exists c, (P0 ∥ psubst shift B0). split=> //=.
    + congr (_ ∥ _). by rewrite psubst_shift_comm.
    + exact: PB_ParL H0.
  - move=> n' C r A B B' _ IH m s P EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]]. rewrite EA.
    case: (IH _ _ _ (esym EB)) => c [P0 [E1 -> H0]].
    exists c, (psubst shift A0 ∥ P0). split=> //=.
    + congr (_ ∥ _). by rewrite psubst_shift_comm.
    + exact: PB_ParR H0.
  - move=> n' C r B B' _ IH m s P EP.
    case: (psubst_inv_res EP) => B0 [-> EB]. 
    case: (IH _ _ _ (esym EB)) => cb [P0 [E1 -> H0]].
    case: (pren_up_image_pshift (esym E1)) => c0 [Ecb EC].
    exists c0, ((ν) (psubst (swap_ch zero one) P0)). split=> //=.
    + congr PRes. by rewrite psubst_swap01_comm.
    + apply: PB_Res. rewrite -Ecb. exact: H0.
Qed.

(** ** Offers pull back (any renaming) *)
Lemma ltsselP_ren_inv n' (C : pch n') (b : bool) X R
    (H : ltsselP C b X R) :
  forall m (s : ren m n') P,
    psubst s P = X ->
    exists c P0, [/\ C = pren s c, R = psubst s P0 & ltsselP c b P P0].
Proof.
  elim: H => {n' C b X R}.
  - move=> n' C b K m s P EP.
    case: (psubst_inv_sel EP) => c [K0 [-> -> ->]].
    exists c, K0. split=> //. exact: PS_Pfx.
  - move=> n' C b A A' B _ IH m s P EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]]. rewrite EB.
    case: (IH _ _ _ (esym EA)) => c [P0 [E1 -> H0]].
    exists c, (P0 ∥ B0). split=> //=. exact: PS_ParL H0.
  - move=> n' C b A B B' _ IH m s P EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]]. rewrite EA.
    case: (IH _ _ _ (esym EB)) => c [P0 [E1 -> H0]].
    exists c, (A0 ∥ P0). split=> //=. exact: PS_ParR H0.
  - move=> n' C b B B' _ IH m s P EP.
    case: (psubst_inv_res EP) => B0 [-> EB].
    case: (IH _ _ _ (esym EB)) => cb [P0 [E1 -> H0]].
    case: (pren_up_image_pshift (esym E1)) => c0 [Ecb EC].
    exists c0, ((ν) P0). split=> //=.
    apply: PS_Res. by rewrite -Ecb.
Qed.

Lemma ltsbrP_ren_inv n' (C : pch n') (b : bool) X R
    (H : ltsbrP C b X R) :
  forall m (s : ren m n') P,
    psubst s P = X ->
    exists c P0, [/\ C = pren s c, R = psubst s P0 & ltsbrP c b P P0].
Proof.
  elim: H => {n' C b X R}.
  - move=> n' C b K1 K2 m s P EP.
    case: (psubst_inv_bra EP) => c [K10 [K20 [-> -> -> ->]]].
    exists c, (if b then K10 else K20). split=> //.
    + by case: b.
    + exact: PBR_Pfx.
  - move=> n' C b A A' B _ IH m s P EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]]. rewrite EB.
    case: (IH _ _ _ (esym EA)) => c [P0 [E1 -> H0]].
    exists c, (P0 ∥ B0). split=> //=. exact: PBR_ParL H0.
  - move=> n' C b A B B' _ IH m s P EP.
    case: (psubst_inv_par EP) => A0 [B0 [-> EA EB]]. rewrite EA.
    case: (IH _ _ _ (esym EB)) => c [P0 [E1 -> H0]].
    exists c, (A0 ∥ P0). split=> //=. exact: PBR_ParR H0.
  - move=> n' C b B B' _ IH m s P EP.
    case: (psubst_inv_res EP) => B0 [-> EB].
    case: (IH _ _ _ (esym EB)) => cb [P0 [E1 -> H0]].
    case: (pren_up_image_pshift (esym E1)) => c0 [Ecb EC].
    exists c0, ((ν) P0). split=> //=.
    apply: PBR_Res. by rewrite -Ecb.
Qed.

Lemma offersP_ren_inv m n (s : ren m n) a (C : pch n) (P : procP m) :
  offersP a C (psubst s P) ->
  exists c, C = pren s c /\ offersP a c P.
Proof.
  case: a => /=.
  - move=> [R HT]. case: (ltscP_ren_inv HT erefl) => c [P0 [E1 _ H0]].
    exists c. split=> //. by exists P0.
  - move=> [R HT]. case: (ltswP_ren_inv HT erefl) => c [P0 [E1 _ H0]].
    exists c. split=> //. by exists P0.
  - move=> [[d [R HT]]|[r [R HT]]].
    + case: (ltsfP_ren_inv HT erefl) => c [d0 [P0 [E1 _ _ H0]]].
      exists c. split=> //. left. by exists d0, P0.
    + case: (ltsbP_ren_inv HT erefl) => c [P0 [E1 _ H0]].
      exists c. split=> //. right. by exists r, P0.
  - move=> [d [R HT]]. case: (ltsrP_ren_inv HT erefl) => c [P0 [E1 _ Hu]].
    exists c. split=> //. by exists (c.1, d.2), (psubst (scons c.1 id_ren) P0).
  - move=> [b [R HT]]. case: (ltsselP_ren_inv HT erefl) => c [P0 [E1 _ H0]].
    exists c. split=> //. by exists b, P0.
  - move=> [b [R HT]]. case: (ltsbrP_ren_inv HT erefl) => c [P0 [E1 _ H0]].
    exists c. split=> //. by exists b, P0.
Qed.

(** ** Axiom audit *)
Print Assumptions offersP_ren_inv.
