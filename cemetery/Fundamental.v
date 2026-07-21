(** * Phase 0: the fundamental theorem, conditional on an inversion interface

    Goal: validate that the logical relation of [LogRel.v] carries the
    fundamental theorem, and make its residual proof debt explicit.  The
    debt is stated as *hypotheses* of a section -- untyped facts about
    what [≅] and [⇛] can do to each process shape -- and everything else
    is proved: semantic weakening, semantic splitting for parallel, one
    compatibility lemma per typing rule, the fundamental theorem, and
    the end-to-end corollary

        cempty ⊢ P  ->  safe P.

    The interface (to be discharged in Phase 1, tiers in brackets):
    - [struct_eq_ren]                 congruence closed under renaming
                                      [mechanical rule induction]
    - [close/wait/del/ins_expo_inv]   exposure inversion at a prefix
                                      [canonical forms]
    - [prefix_res_inv]                a prefix seen under a junk binder
                                      [canonical forms]
    - [par_red_inv/expo_inv/res_inv]  decomposition of parallel
                                      [canonical forms]
    - [Esem_rename]                   the relation transports along
                                      renamings that respect contexts
                                      [k-induction over the above]
    - [res_combine]                   compatibility of restriction
                                      [Phase 0b: from res-side
                                      inversions + a semantic
                                      communication lemma]

    Everything below the section header is Qed-complete; the section
    closes and the final theorems carry the hypotheses as explicit
    premises, so [Print Assumptions] stays clean and the conditionality
    is visible in the statements. *)

From mathcomp Require Import all_ssreflect.
From Tait Require Import synsem Errors LogRel Typing Toolkit Adequacy.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** Splitting laws *)
Lemma split_someL n (Δ Δ1 Δ2 : sctx n) x S :
  split Δ Δ1 Δ2 -> Δ1 x = Some S -> Δ x = Some S /\ Δ2 x = None.
Proof.
  move=> Hs H1; case: (Hs x) => [[Ha Hb]|[Ha Hb]]; first by rewrite -Ha.
  by rewrite Hb in H1.
Qed.

Lemma split_someR n (Δ Δ1 Δ2 : sctx n) x S :
  split Δ Δ1 Δ2 -> Δ2 x = Some S -> Δ x = Some S /\ Δ1 x = None.
Proof. move=> /split_sym. exact: split_someL. Qed.

Lemma split_cupd n (Δ Δ1 Δ2 : sctx n) (x : ch n) o :
  split Δ Δ1 Δ2 -> Δ2 x = None -> split (cupd x o Δ) (cupd x o Δ1) Δ2.
Proof.
  move=> Hs H2 z; rewrite /cupd; case: ifP => [/eqP ->|_].
  - by left; rewrite H2.
  - exact: Hs.
Qed.

Lemma split_scons n (Δ Δ1 Δ2 : sctx n) o :
  split Δ Δ1 Δ2 -> split (scons o Δ) (scons o Δ1) (scons None Δ2).
Proof. by move=> Hs [i|] /=; [exact: Hs | left]. Qed.

Lemma split_cext n S (Δ Δ1 Δ2 : sctx n) :
  split Δ Δ1 Δ2 ->
  split (cext S Δ) (cext S Δ1) (scons None (scons None Δ2)).
Proof. move=> Hs. apply: split_scons. exact: split_scons. Qed.

Lemma split_cextR n S (Δ Δ1 Δ2 : sctx n) :
  split Δ Δ1 Δ2 ->
  split (cext S Δ) (scons None (scons None Δ1)) (cext S Δ2).
Proof. move=> /split_sym /(split_cext S) /split_sym. by []. Qed.

(** ** Semantic weakening: owning more (unused) channels is harmless *)
Definition ctx_le {n : nat} (Δ1 Δ2 : sctx n) : Prop :=
  forall x S, Δ1 x = Some S -> Δ2 x = Some S.

Lemma ctx_le_cupd n (Δ1 Δ2 : sctx n) (x : ch n) o :
  ctx_le Δ1 Δ2 -> ctx_le (cupd x o Δ1) (cupd x o Δ2).
Proof. move=> H z S; rewrite /cupd; case: ifP => // _. exact: H. Qed.

Lemma ctx_le_scons n (Δ1 Δ2 : sctx n) o :
  ctx_le Δ1 Δ2 -> ctx_le (scons o Δ1) (scons o Δ2).
Proof. by move=> H [i|] //= S; apply: H. Qed.

Lemma ctx_le_cext n S (Δ1 Δ2 : sctx n) :
  ctx_le Δ1 Δ2 -> ctx_le (cext S Δ1) (cext S Δ2).
Proof. move=> H. apply: ctx_le_scons. exact: ctx_le_scons. Qed.

Lemma Esem_weaken k : forall n (Δ1 Δ2 : sctx n) (P : proc n),
  ctx_le Δ1 Δ2 -> Esem k Δ1 P -> Esem k Δ2 P.
Proof.
  elim: k => [//|k IH] n Δ1 Δ2 P Hle HE P' Hred.
  case: (HE _ Hred) => C V X; split.
  - move=> a x F R HFR Hpa. case: (C _ _ _ _ HFR Hpa) => S [HS Ha].
    exists S. split=> //. exact: Hle HS.
  - move=> x S HxS.
    case E1 : (Δ1 x) => [S'|].
    + have HS2 : Δ2 x = Some S' by exact: Hle E1.
      have ES : S' = S by move: HS2; rewrite HxS => -[].
      subst S'.
      move: (V _ _ E1).
      case: S {HxS E1 HS2} => [| |S1 S2|S1 S2] /= HV.
      * move=> K R HFR. apply: (IH _ _ _ _ _ (HV _ _ HFR)).
        apply: ctx_le_cupd. exact: Hle.
      * move=> K R HFR. apply: (IH _ _ _ _ _ (HV _ _ HFR)).
        apply: ctx_le_cupd. exact: Hle.
      * move=> y K R HFR. case: (HV _ _ _ HFR) => Hy HK.
        split; first exact: Hle Hy.
        apply: (IH _ _ _ _ _ HK).
        do 2 apply: ctx_le_cupd. exact: Hle.
      * move=> K R HFR. apply: (IH _ _ _ _ _ (HV _ _ HFR)).
        apply: ctx_le_scons. apply: ctx_le_cupd. exact: Hle.
    + case: S {HxS} => [| |S1 S2|S1 S2] /=.
      * move=> K R HFR.
        case: (C _ _ _ _ HFR (PA_Close x K)) => S'' [HS'' _].
        by rewrite E1 in HS''.
      * move=> K R HFR.
        case: (C _ _ _ _ HFR (PA_Wait x K)) => S'' [HS'' _].
        by rewrite E1 in HS''.
      * move=> y K R HFR.
        case: (C _ _ _ _ HFR (PA_DelS x y K)) => S'' [HS'' _].
        by rewrite E1 in HS''.
      * move=> K R HFR.
        case: (C _ _ _ _ HFR (PA_DelR x K)) => S'' [HS'' _].
        by rewrite E1 in HS''.
  - move=> Q HQ. case: (X _ HQ) => S HS.
    exists S. apply: (IH _ _ _ _ _ HS).
    apply: ctx_le_cext. exact: Hle.
Qed.

Lemma ctx_le_of_ext n (Δ Δ' : sctx n) :
  (forall x, Δ x = Δ' x) -> ctx_le Δ Δ'.
Proof. by move=> H x S; rewrite -H. Qed.

Lemma Esem_ext k n (Δ Δ' : sctx n) (P : proc n) :
  (forall x, Δ x = Δ' x) -> Esem k Δ P -> Esem k Δ' P.
Proof. move=> H. apply: Esem_weaken. exact: ctx_le_of_ext. Qed.

(** ** No session type is a strict subterm of itself *)
Fixpoint sty_size (S : sty) : nat :=
  match S with
  | SClose | SWait => 1
  | SSend a b | SRecv a b => (sty_size a + sty_size b).+1
  end.

Lemma ssend_no_fix a b : SSend a b = a -> False.
Proof.
  move=> E. have HE := f_equal sty_size E. rewrite /= in HE.
  by move: (leq_addr (sty_size b) (sty_size a)); rewrite -ltnS HE ltnn.
Qed.

Lemma srecv_no_fix a b : SRecv a b = a -> False.
Proof.
  move=> E. have HE := f_equal sty_size E. rewrite /= in HE.
  by move: (leq_addr (sty_size b) (sty_size a)); rewrite -ltnS HE ltnn.
Qed.

(** ** Context computations under the double shift *)
Lemma cupd_shift2_cext n S (Δ : sctx n) (x : ch n) o (z : ch n.+2) :
  cupd (shift (shift x)) o (cext S Δ) z = cext S (cupd x o Δ) z.
Proof.
  have Hs2 : (shift (shift x) : ch n.+2) = Some (Some x) by [].
  case: z => [[w|]|] //=; rewrite /cupd Hs2.
  case: ifP => [/eqP E|E].
  - have E2 := f_equal (fun c : ch n.+2 =>
                          if c is Some (Some u) then u else w) E.
    rewrite /= in E2. by rewrite E2 eqxx.
  - case E2 : ((w : ch n) == x) => //.
    move/eqP: E2 => E2. move: E. by rewrite E2 eqxx.
Qed.

(** The context after both endpoints of a session are consumed. *)
Lemma ctx_close_after n S' (Δ : sctx n) (z : ch n.+2) :
  cupd zero None (cupd one None (cext S' Δ)) z = scons None (scons None Δ) z.
Proof. by case: z => [[w|]|]. Qed.

(** Two [cext]s agree away from the bound endpoints. *)
Lemma cext_agree n S S' (Δ : sctx n) (x : ch n.+2) :
  x <> zero -> x <> one -> cext S Δ x = cext S' Δ x.
Proof. by case: x => [[w|]|] H1 H2. Qed.

Lemma ctx_le_nn_cext n S (Δ : sctx n) :
  ctx_le (scons None (scons None Δ)) (cext S Δ).
Proof. by move=> [[w|]|] //= T. Qed.

(** Pulling a parallel component out of a restriction it does not use. *)
Lemma res_pull n (K : proc n) (R0 : proc n.+2) :
  (ν) (subst_proc (shift \o shift) K ∥ R0) ≅ K ∥ (ν) R0.
Proof.
  apply: SC_Trans (SC_Cong_Res (SC_Par_Com _ _)) _.
  apply: SC_Trans (SC_Sym (SC_Res_Scope R0 K)) _.
  exact: SC_Par_Com.
Qed.

(** ** Communication at a binder, and hybrid execution

    [comm P P1]: under its restriction, [P] can fire one communication
    between its two endpoints, leaving [P1].  Two rules by two
    orientations.  [hybstar] interleaves ordinary reduction of the body
    with such communications: this is exactly how the reducts of [(ν) P]
    project onto bodies. *)
Inductive comm {n : nat} : proc n.+2 -> proc n.+2 -> Prop :=
| Comm_CW : forall (P A B : proc n.+2),
    P ≅ CloseP one A ∥ WaitP zero B -> comm P (A ∥ B)
| Comm_WC : forall (P A B : proc n.+2),
    P ≅ WaitP one A ∥ CloseP zero B -> comm P (A ∥ B)
| Comm_DR : forall (P : proc n.+2) (x : ch n.+2) A (B : proc n.+3),
    P ≅ DelP one x A ∥ InSP zero B ->
    comm P (A ∥ subst_proc (scons x id_ren) B)
| Comm_RD : forall (P : proc n.+2) (x : ch n.+2) (A : proc n.+3) B,
    P ≅ InSP one A ∥ DelP zero x B ->
    comm P (subst_proc (scons x id_ren) A ∥ B).

Inductive hybstar {n : nat} : proc n.+2 -> proc n.+2 -> Prop :=
| Hyb_refl : forall P, hybstar P P
| Hyb_red : forall P Q R, P ⇛ Q -> hybstar Q R -> hybstar P R
| Hyb_comm : forall P Q R, comm P Q -> hybstar Q R -> hybstar P R.

(** ** The inversion interface *)
Section AssumedHarmony.

(** [≅] is closed under renaming (forward direction; mechanical rule
    induction once the renaming composition laws exist). *)
Hypothesis struct_eq_ren : forall m n (s : ren m n) (P Q : proc m),
    P ≅ Q -> subst_proc s P ≅ subst_proc s Q.

(** Exposure inversion at a prefix: a prefixed process exposes exactly
    its own head, and the residual is its continuation up to junk. *)
Hypothesis close_expo_inv : forall n (x : ch n) K a (y : ch n) F R,
    CloseP x K ≅ F ∥ R -> prefix_at a y F ->
    exists K0, [/\ a = AClose, y = x, F = CloseP x K0 & K ≅ K0 ∥ R].

Hypothesis wait_expo_inv : forall n (x : ch n) K a (y : ch n) F R,
    WaitP x K ≅ F ∥ R -> prefix_at a y F ->
    exists K0, [/\ a = AWait, y = x, F = WaitP x K0 & K ≅ K0 ∥ R].

Hypothesis del_expo_inv : forall n (x z : ch n) K a (y : ch n) F R,
    DelP x z K ≅ F ∥ R -> prefix_at a y F ->
    exists K0, [/\ a = ADelS, y = x, F = DelP x z K0 & K ≅ K0 ∥ R].

Hypothesis ins_expo_inv : forall n (x : ch n) (K : proc n.+1) a (y : ch n) F R,
    InSP x K ≅ F ∥ R -> prefix_at a y F ->
    exists K0 : proc n.+1,
      [/\ a = ADelR, y = x, F = InSP x K0 & K ≅ K0 ∥ subst_proc shift R].

(** A prefix under a restriction: the binder is junk. *)
Hypothesis prefix_res_inv : forall n a (x : ch n) (F : proc n) (Q : proc n.+2),
    prefix_at a x F -> F ≅ (ν) Q ->
    exists D, Q ≅ subst_proc (shift \o shift) F ∥ D /\ act_cnt D = 0.

(** Decomposition of a parallel composition: components cannot
    communicate with each other at top level (a redex needs the shared
    restriction, and hoisting a binder out of one component cannot
    capture the other's channels). *)
Hypothesis par_red_inv : forall n (P Q R : proc n),
    P ∥ Q ⇛ R ->
    (exists P1, P ⇛ P1 /\ R ≅ P1 ∥ Q) \/
    (exists Q1, Q ⇛ Q1 /\ R ≅ P ∥ Q1).

Hypothesis par_expo_inv : forall n a (x : ch n) (P Q F R : proc n),
    P ∥ Q ≅ F ∥ R -> prefix_at a x F ->
    (exists Rp, P ≅ F ∥ Rp /\ R ≅ Rp ∥ Q) \/
    (exists Rq, Q ≅ F ∥ Rq /\ R ≅ P ∥ Rq).

Hypothesis par_res_inv : forall n (P Q : proc n) (M : proc n.+2),
    P ∥ Q ≅ (ν) M ->
    (exists P0, P ≅ (ν) P0 /\ M ≅ P0 ∥ subst_proc (shift \o shift) Q) \/
    (exists Q0, Q ≅ (ν) Q0 /\ M ≅ subst_proc (shift \o shift) P ∥ Q0).

(** The relation transports along renamings that respect the contexts:
    agreement on owned channels, injectivity on owned channels. *)
Hypothesis Esem_rename : forall k m n (s : ren m n)
    (Δm : sctx m) (Δn : sctx n) (P : proc m),
    (forall z, Δm z = None \/ Δn (s z) = Δm z) ->
    (forall z1 z2, Δm z1 <> None -> Δm z2 <> None -> s z1 = s z2 -> z1 = z2) ->
    Esem k Δm P -> Esem k Δn (subst_proc s P).

(** Decomposition of a restriction: an exposed prefix comes from the
    body (shifted), a step of [(ν) P] is a step of the body or a
    communication at this binder, and congruent restrictions have
    semantically related bodies (swaps flip the polarity, extrusion
    rearranges junk -- all within some protocol). *)
Hypothesis res_expo_inv : forall n a (x : ch n) (Q : proc n.+2) F R,
    (ν) Q ≅ F ∥ R -> prefix_at a x F ->
    exists R0 : proc n.+2,
      Q ≅ subst_proc (shift \o shift) F ∥ R0 /\ R ≅ (ν) R0.

Hypothesis res_red_inv : forall n (P : proc n.+2) (R : proc n),
    (ν) P ⇛ R ->
    exists P1, R ≅ (ν) P1 /\ (P ⇛ P1 \/ comm P P1).

Hypothesis res_sem_inv : forall k n S (Δ : sctx n) (P Q : proc n.+2),
    Esem k (cext S Δ) P -> (ν) P ≅ (ν) Q ->
    exists S', Esem k (cext S' Δ) Q.

(** *** Multistep parallel decomposition (derived) *)
Lemma par_mred_inv n (X R : proc n) : X ⇛* R ->
  forall P Q, X ≅ P ∥ Q ->
  exists P1 Q1, [/\ P ⇛* P1, Q ⇛* Q1 & R ≅ P1 ∥ Q1].
Proof.
  elim=> {X R} [X|X Y R Hst _ IH] P Q Heq.
  - exists P, Q. split; try exact: MR_refl. exact: Heq.
  - have HPQ : P ∥ Q ⇛ Y by apply: R_Struct (SC_Sym Heq) Hst (SC_Refl _).
    case: (par_red_inv HPQ) => [[P1 [HstP HY]]|[Q1 [HstQ HY]]].
    + case: (IH _ _ HY) => P2 [Q2 [Hp Hq HR]].
      exists P2, Q2. split=> //. exact: MR_step HstP Hp.
    + case: (IH _ _ HY) => P2 [Q2 [Hp Hq HR]].
      exists P2, Q2. split=> //. exact: MR_step HstQ Hq.
Qed.

(** Renaming side conditions for [shift] and [shift ∘ shift]. *)
Let shift_ok n (Δ : sctx n) o :
  forall z : ch n, Δ z = None \/ scons o Δ (shift z) = Δ z.
Proof. move=> z. by right. Qed.

Let shift_inj n (z1 z2 : ch n) : shift z1 = shift z2 -> z1 = z2.
Proof. by case. Qed.

Let shift2_ok n (Δ : sctx n) o1 o2 :
  forall z : ch n,
    Δ z = None \/ scons o1 (scons o2 Δ) (shift (shift z)) = Δ z.
Proof. move=> z. by right. Qed.

Let shift2_inj n (z1 z2 : ch n) :
  shift (shift z1) = shift (shift z2) -> z1 = z2.
Proof. by case. Qed.

(** *** Semantic splitting: compatibility of parallel composition *)
Lemma par_combine k : forall n (Δ Δ1 Δ2 : sctx n) (P Q : proc n),
  split Δ Δ1 Δ2 -> Esem k Δ1 P -> Esem k Δ2 Q -> Esem k Δ (P ∥ Q).
Proof.
  elim: k => [//|k IH] n Δ Δ1 Δ2 P Q Hs HP HQ P' Hred.
  case: (par_mred_inv Hred (SC_Refl _)) => P1 [Q1 [HrP HrQ HP']].
  have HP1 : Esem k.+1 Δ1 P1 := Esem_mreduce HrP HP.
  have HQ1 : Esem k.+1 Δ2 Q1 := Esem_mreduce HrQ HQ.
  case: (HP1 _ (MR_refl _)) => CP VP XP.
  case: (HQ1 _ (MR_refl _)) => CQ VQ XQ.
  have HQk : Esem k Δ2 Q1 := Esem_antitone HQ1.
  have HPk : Esem k Δ1 P1 := Esem_antitone HP1.
  split.
  - (* conform *)
    move=> a x F R HFR Hpa.
    have HPQ1 : P1 ∥ Q1 ≅ F ∥ R := SC_Trans (SC_Sym HP') HFR.
    case: (par_expo_inv HPQ1 Hpa) => [[Rp [Hex _]]|[Rq [Hex _]]].
    + case: (CP _ _ _ _ Hex Hpa) => S [HS Ha].
      case: (split_someL Hs HS) => HD _. by exists S.
    + case: (CQ _ _ _ _ Hex Hpa) => S [HS Ha].
      case: (split_someR Hs HS) => HD _. by exists S.
  - (* value clauses *)
    move=> x S HxS.
    case: (Hs x) => [[E1 E2]|[E2 E1]].
    + (* left component owns x *)
      have HxS1 : Δ1 x = Some S by rewrite E1.
      case: S HxS HxS1 => [| |S1 S2|S1 S2] HxS HxS1 /=.
      * move=> K R HFR.
        have HPQ1 : P1 ∥ Q1 ≅ CloseP x K ∥ R := SC_Trans (SC_Sym HP') HFR.
        case: (par_expo_inv HPQ1 (PA_Close x K)) =>
          [[Rp [HexP HRr]]|[Rq [HexQ _]]]; last first.
          case: (CQ _ _ _ _ HexQ (PA_Close x K)) => S' [HS' _].
          by rewrite E2 in HS'.
        move: (VP _ _ HxS1) => /= HVP.
        move: (HVP _ _ HexP) => HK.
        have Hs' := split_cupd None Hs E2.
        have HC := IH _ _ _ _ _ _ Hs' HK HQk.
        apply: Esem_struct HC.
        apply: SC_Trans (SC_Par_Assoc _ _ _) _.
        exact: SC_Cong_Par (SC_Refl _) (SC_Sym HRr).
      * move=> K R HFR.
        have HPQ1 : P1 ∥ Q1 ≅ WaitP x K ∥ R := SC_Trans (SC_Sym HP') HFR.
        case: (par_expo_inv HPQ1 (PA_Wait x K)) =>
          [[Rp [HexP HRr]]|[Rq [HexQ _]]]; last first.
          case: (CQ _ _ _ _ HexQ (PA_Wait x K)) => S' [HS' _].
          by rewrite E2 in HS'.
        move: (VP _ _ HxS1) => /= HVP.
        move: (HVP _ _ HexP) => HK.
        have Hs' := split_cupd None Hs E2.
        have HC := IH _ _ _ _ _ _ Hs' HK HQk.
        apply: Esem_struct HC.
        apply: SC_Trans (SC_Par_Assoc _ _ _) _.
        exact: SC_Cong_Par (SC_Refl _) (SC_Sym HRr).
      * move=> y K R HFR.
        have HPQ1 : P1 ∥ Q1 ≅ DelP x y K ∥ R := SC_Trans (SC_Sym HP') HFR.
        case: (par_expo_inv HPQ1 (PA_DelS x y K)) =>
          [[Rp [HexP HRr]]|[Rq [HexQ _]]]; last first.
          case: (CQ _ _ _ _ HexQ (PA_DelS x y K)) => S' [HS' _].
          by rewrite E2 in HS'.
        move: (VP _ _ HxS1) => /= HVP.
        case: (HVP _ _ _ HexP) => Hy1 HK.
        case: (split_someL Hs Hy1) => HyD Hy2.
        split=> //.
        have Hs' := split_cupd None (split_cupd (Some S2) Hs E2) Hy2.
        have HC := IH _ _ _ _ _ _ Hs' HK HQk.
        apply: Esem_struct HC.
        apply: SC_Trans (SC_Par_Assoc _ _ _) _.
        exact: SC_Cong_Par (SC_Refl _) (SC_Sym HRr).
      * move=> K R HFR.
        have HPQ1 : P1 ∥ Q1 ≅ InSP x K ∥ R := SC_Trans (SC_Sym HP') HFR.
        case: (par_expo_inv HPQ1 (PA_DelR x K)) =>
          [[Rp [HexP HRr]]|[Rq [HexQ _]]]; last first.
          case: (CQ _ _ _ _ HexQ (PA_DelR x K)) => S' [HS' _].
          by rewrite E2 in HS'.
        move: (VP _ _ HxS1) => /= HVP.
        move: (HVP _ _ HexP) => HK.
        (* lift the right component one binder up *)
        have HQsh : Esem k (scons None Δ2) (subst_proc shift Q1).
          apply: Esem_rename HQk; first exact: shift_ok.
          move=> z1 z2 _ _. exact: shift_inj.
        have Hs' := split_scons (Some S1) (split_cupd (Some S2) Hs E2).
        have HC := IH _ _ _ _ _ _ Hs' HK HQsh.
        apply: Esem_struct HC.
        apply: SC_Trans (SC_Par_Assoc _ _ _) _.
        apply: SC_Cong_Par (SC_Refl _) _.
        apply: SC_Sym.
        apply: SC_Trans (struct_eq_ren shift HRr) _.
        exact: SC_Refl.
    + (* right component owns x -- mirror image *)
      have HxS2 : Δ2 x = Some S by rewrite E2.
      case: S HxS HxS2 => [| |S1 S2|S1 S2] HxS HxS2 /=.
      * move=> K R HFR.
        have HPQ1 : P1 ∥ Q1 ≅ CloseP x K ∥ R := SC_Trans (SC_Sym HP') HFR.
        case: (par_expo_inv HPQ1 (PA_Close x K)) =>
          [[Rp [HexP _]]|[Rq [HexQ HRr]]].
          case: (CP _ _ _ _ HexP (PA_Close x K)) => S' [HS' _].
          by rewrite E1 in HS'.
        move: (VQ _ _ HxS2) => /= HVQ.
        move: (HVQ _ _ HexQ) => HK.
        have Hs' := split_cupd None (split_sym Hs) E1.
        have HC := IH _ _ _ _ _ _ Hs' HK HPk.
        apply: Esem_struct HC.
        apply: SC_Trans (SC_Par_Assoc _ _ _) _.
        apply: SC_Cong_Par (SC_Refl _) _.
        apply: SC_Trans (SC_Par_Com _ _) _.
        exact: SC_Sym HRr.
      * move=> K R HFR.
        have HPQ1 : P1 ∥ Q1 ≅ WaitP x K ∥ R := SC_Trans (SC_Sym HP') HFR.
        case: (par_expo_inv HPQ1 (PA_Wait x K)) =>
          [[Rp [HexP _]]|[Rq [HexQ HRr]]].
          case: (CP _ _ _ _ HexP (PA_Wait x K)) => S' [HS' _].
          by rewrite E1 in HS'.
        move: (VQ _ _ HxS2) => /= HVQ.
        move: (HVQ _ _ HexQ) => HK.
        have Hs' := split_cupd None (split_sym Hs) E1.
        have HC := IH _ _ _ _ _ _ Hs' HK HPk.
        apply: Esem_struct HC.
        apply: SC_Trans (SC_Par_Assoc _ _ _) _.
        apply: SC_Cong_Par (SC_Refl _) _.
        apply: SC_Trans (SC_Par_Com _ _) _.
        exact: SC_Sym HRr.
      * move=> y K R HFR.
        have HPQ1 : P1 ∥ Q1 ≅ DelP x y K ∥ R := SC_Trans (SC_Sym HP') HFR.
        case: (par_expo_inv HPQ1 (PA_DelS x y K)) =>
          [[Rp [HexP _]]|[Rq [HexQ HRr]]].
          case: (CP _ _ _ _ HexP (PA_DelS x y K)) => S' [HS' _].
          by rewrite E1 in HS'.
        move: (VQ _ _ HxS2) => /= HVQ.
        case: (HVQ _ _ _ HexQ) => Hy2 HK.
        case: (split_someR Hs Hy2) => HyD Hy1.
        split=> //.
        have Hs' := split_cupd None
                      (split_cupd (Some S2) (split_sym Hs) E1) Hy1.
        have HC := IH _ _ _ _ _ _ Hs' HK HPk.
        apply: Esem_struct HC.
        apply: SC_Trans (SC_Par_Assoc _ _ _) _.
        apply: SC_Cong_Par (SC_Refl _) _.
        apply: SC_Trans (SC_Par_Com _ _) _.
        exact: SC_Sym HRr.
      * move=> K R HFR.
        have HPQ1 : P1 ∥ Q1 ≅ InSP x K ∥ R := SC_Trans (SC_Sym HP') HFR.
        case: (par_expo_inv HPQ1 (PA_DelR x K)) =>
          [[Rp [HexP _]]|[Rq [HexQ HRr]]].
          case: (CP _ _ _ _ HexP (PA_DelR x K)) => S' [HS' _].
          by rewrite E1 in HS'.
        move: (VQ _ _ HxS2) => /= HVQ.
        move: (HVQ _ _ HexQ) => HK.
        have HPsh : Esem k (scons None Δ1) (subst_proc shift P1).
          apply: Esem_rename HPk; first exact: shift_ok.
          move=> z1 z2 _ _. exact: shift_inj.
        have Hs' := split_scons (Some S1)
                      (split_cupd (Some S2) (split_sym Hs) E1).
        have HC := IH _ _ _ _ _ _ Hs' HK HPsh.
        apply: Esem_struct HC.
        apply: SC_Trans (SC_Par_Assoc _ _ _) _.
        apply: SC_Cong_Par (SC_Refl _) _.
        apply: SC_Trans (SC_Par_Com _ _) _.
        exact: SC_Sym (struct_eq_ren shift HRr).
  - (* semantic cut *)
    move=> M HM.
    have HPQ1 : P1 ∥ Q1 ≅ (ν) M := SC_Trans (SC_Sym HP') HM.
    case: (par_res_inv HPQ1) => [[P0 [HnuP HMdec]]|[Q0 [HnuQ HMdec]]].
    + case: (XP _ HnuP) => S0 HP0.
      have HQsh : Esem k (scons None (scons None Δ2))
                         (subst_proc (shift \o shift) Q1).
        apply: Esem_rename HQk; first exact: shift2_ok.
        move=> z1 z2 _ _. exact: shift2_inj.
      have HC := IH _ _ _ _ _ _ (split_cext S0 Hs) HP0 HQsh.
      exists S0. exact: Esem_struct (SC_Sym HMdec) HC.
    + case: (XQ _ HnuQ) => S0 HQ0.
      have HPsh : Esem k (scons None (scons None Δ1))
                         (subst_proc (shift \o shift) P1).
        apply: Esem_rename HPk; first exact: shift2_ok.
        move=> z1 z2 _ _. exact: shift2_inj.
      have HC := IH _ _ _ _ _ _ (split_cextR S0 Hs) HPsh HQ0.
      exists S0. exact: Esem_struct (SC_Sym HMdec) HC.
Qed.

(** *** The semantic communication lemma

    When the two endpoints of a session fire, both continuations stay in
    the relation, at the *advanced* protocol: [cext S] becomes [cext S']
    with [S'] the continuation of [S] (or anything, if the session
    closed).  This is the semantic counterpart of cut reduction. *)
Lemma comm_sem n S (Δ : sctx n) (P P1 : proc n.+2) :
  SEM (cext S Δ) P -> comm P P1 -> exists S', SEM (cext S' Δ) P1.
Proof.
  move=> HP Hc. case: Hc HP.
  - (* close meets wait *)
    move=> Q0 A B Heq HP.
    have HS : S = SWait.
      case: (HP 1 _ (MR_refl _)) => C _ _.
      case: (C _ _ _ _ Heq (PA_Close one A)) => S1 [HS1 Ha] {C}.
      move: HS1; rewrite cext_one => -[HS1].
      rewrite -HS1 in Ha. by case: S HP HS1 Ha => //=.
    subst S.
    exists SClose => k.
    case: (HP k.+2 _ (MR_refl _)) => _ V2 _.
    have HxOne : cext SWait Δ one = Some SClose by [].
    move: (V2 _ _ HxOne) => /= HVA.
    move: (HVA _ _ Heq) => HA1.
    case: (HA1 _ (MR_refl _)) => _ V1 _.
    have HxZero : cupd one None (cext SWait Δ) zero = Some SWait by [].
    move: (V1 _ _ HxZero) => /= HVB.
    move: (HVB _ _ (SC_Par_Com _ _)) => HB.
    have HB' := Esem_ext (ctx_close_after SWait Δ) HB.
    have HB2 := Esem_struct (SC_Par_Com B A) HB'.
    apply: Esem_weaken (HB2). exact: ctx_le_nn_cext.
  - (* wait meets close *)
    move=> Q0 A B Heq HP.
    have HS : S = SClose.
      case: (HP 1 _ (MR_refl _)) => C _ _.
      case: (C _ _ _ _ Heq (PA_Wait one A)) => S1 [HS1 Ha] {C}.
      move: HS1; rewrite cext_one => -[HS1].
      rewrite -HS1 in Ha. by case: S HP HS1 Ha => //=.
    subst S.
    exists SClose => k.
    case: (HP k.+2 _ (MR_refl _)) => _ V2 _.
    have HxOne : cext SClose Δ one = Some SWait by [].
    move: (V2 _ _ HxOne) => /= HVA.
    move: (HVA _ _ Heq) => HA1.
    case: (HA1 _ (MR_refl _)) => _ V1 _.
    have HxZero : cupd one None (cext SClose Δ) zero = Some SClose by [].
    move: (V1 _ _ HxZero) => /= HVB.
    move: (HVB _ _ (SC_Par_Com _ _)) => HB.
    have HB' := Esem_ext (ctx_close_after SClose Δ) HB.
    have HB2 := Esem_struct (SC_Par_Com B A) HB'.
    apply: Esem_weaken (HB2). exact: ctx_le_nn_cext.
  - (* delegation: send at [one], receive at [zero] *)
    move=> Q0 x A B Heq HP.
    have [T [C0 HS]] : exists T C0, S = SRecv T C0.
      case: (HP 1 _ (MR_refl _)) => C _ _.
      case: (C _ _ _ _ Heq (PA_DelS one x A)) => S1 [HS1 Ha] {C}.
      move: HS1; rewrite cext_one => -[HS1].
      rewrite -HS1 in Ha.
      case: S HP HS1 Ha => //= T C0 _ _ _. by exists T, C0.
    subst S.
    exists C0 => k.
    case: (HP k.+2 _ (MR_refl _)) => _ V2 _.
    have HxOne : cext (SRecv T C0) Δ one = Some (SSend T (dual C0)) by [].
    move: (V2 _ _ HxOne) => /= HVA.
    case: (HVA _ _ _ Heq) => HxT HA1.
    have Hxz : x <> zero.
      move=> E. rewrite E in HxT.
      have E2 := f_equal (fun o : option sty =>
                            if o is Some u then u else T) HxT.
      exact: srecv_no_fix E2.
    have Hxo : x <> one.
      move=> E. rewrite E in HxT.
      have E2 := f_equal (fun o : option sty =>
                            if o is Some u then u else T) HxT.
      exact: ssend_no_fix E2.
    have Ezx : ((zero : ch n.+2) == x) = false.
      by apply/eqP => E; apply: Hxz; rewrite E.
    have Eox : ((one : ch n.+2) == x) = false.
      by apply/eqP => E; apply: Hxo; rewrite E.
    case: (HA1 _ (MR_refl _)) => _ V1 _.
    have HxZero : cupd x None (cupd one (Some (dual C0))
                     (cext (SRecv T C0) Δ)) zero = Some (SRecv T C0).
      by rewrite /cupd Ezx.
    move: (V1 _ _ HxZero) => /= HVB.
    move: (HVB _ _ (SC_Par_Com _ _)) => HB.
    have HR : Esem k (cext C0 Δ)
                (subst_proc (scons x id_ren) (B ∥ subst_proc shift A)).
      apply: Esem_rename HB.
      - move=> z. case: z => [z'|]; last first.
        + right. rewrite /=.
          by rewrite (cext_agree C0 (SRecv T C0) Δ Hxz Hxo).
        + case: z' => [[w|]|].
          * case Exw : ((Some (Some w) : ch n.+2) == x).
            -- left. by rewrite /= /cupd Exw.
            -- right. by rewrite /= /cupd Exw.
          * right. by rewrite /= /cupd Eox.
          * right. by [].
      - move=> z1 z2 Hz1 Hz2.
        case: z1 Hz1 => [z1'|] Hz1; case: z2 Hz2 => [z2'|] Hz2 //=.
        + by move=> Ez; congr Some; exact: Ez.

        + move=> Ez. have Ez2 : z1' = x := Ez. exfalso. apply: Hz1.
          by rewrite /= Ez2 /cupd (eq_sym x zero) Ezx eqxx.
        + move=> Ez. have Ez2 : x = z2' := Ez. exfalso. apply: Hz2.
          by rewrite /= -Ez2 /cupd (eq_sym x zero) Ezx eqxx.
    have Hsub : subst_proc (scons x id_ren) (subst_proc shift A) = A.
      rewrite subst_proc_comp
              (subst_proc_ext A (t := id_ren) (fun w : ch n.+2 => erefl)).
      exact: subst_proc_id.
    move: HR. rewrite /= Hsub => HR.
    exact: Esem_struct (SC_Par_Com _ _) HR.
  - (* delegation: receive at [one], send at [zero] *)
    move=> Q0 x A B Heq HP.
    have [T [Cs HS]] : exists T Cs, S = SSend T Cs.
      case: (HP 1 _ (MR_refl _)) => C _ _.
      case: (C _ _ _ _ Heq (PA_DelR one A)) => S1 [HS1 Ha] {C}.
      move: HS1; rewrite cext_one => -[HS1].
      rewrite -HS1 in Ha.
      case: S HP HS1 Ha => //= T Cs _ _ _. by exists T, Cs.
    subst S.
    exists Cs => k.
    case: (HP k.+2 _ (MR_refl _)) => _ V2 _.
    have HxOne : cext (SSend T Cs) Δ one = Some (SRecv T (dual Cs)) by [].
    move: (V2 _ _ HxOne) => /= HVA.
    move: (HVA _ _ Heq) => HA1.
    case: (HA1 _ (MR_refl _)) => _ V1 _.
    have HxZ : scons (Some T) (cupd one (Some (dual Cs))
                 (cext (SSend T Cs) Δ)) (shift zero) = Some (SSend T Cs).
      by [].
    move: (V1 _ _ HxZ) => /= HVB.
    case: (HVB _ _ _ (SC_Par_Com _ _)) => HxT HB.
    have Hxz : x <> zero.
      move=> E. rewrite E in HxT.
      have E2 := f_equal (fun o : option sty =>
                            if o is Some u then u else T) HxT.
      exact: ssend_no_fix E2.
    have HR : Esem k (cext Cs Δ)
                (subst_proc (scons x id_ren) (subst_proc shift B ∥ A)).
      apply: Esem_rename HB.
      - move=> z. case: z => [z'|]; last first.
        + right. rewrite /=.
          move: HxT. rewrite /= /cupd. case: ifP => [/eqP Ex1|Ex1].
          * move=> HT.
            have HT2 := f_equal (fun o : option sty =>
                                   if o is Some u then u else T) HT.
            rewrite /= in HT2. by rewrite Ex1 -HT2.
          * move=> HT.
            have Hxo : x <> one by move=> E; rewrite E eqxx in Ex1.
            by rewrite (cext_agree Cs (SSend T Cs) Δ Hxz Hxo).
        + case Exz : ((Some z' : ch n.+3) == shift x).
          * left. by rewrite /= /cupd Exz.
          * case: z' Exz => [[w|]|] Exz.
            -- right. by rewrite /= /cupd Exz.
            -- right. by rewrite /= /cupd Exz.
            -- right. by rewrite /= /cupd Exz.
      - move=> z1 z2 Hz1 Hz2.
        case: z1 Hz1 => [z1'|] Hz1; case: z2 Hz2 => [z2'|] Hz2 //=.
        + by move=> Ez; congr Some; exact: Ez.

        + move=> Ez. have Ez2 : z1' = x := Ez. exfalso. apply: Hz1.
          have Hsx : (shift x : ch n.+3) = Some x by [].
          by rewrite /= Ez2 /cupd Hsx eqxx.
        + move=> Ez. have Ez2 : x = z2' := Ez. exfalso. apply: Hz2.
          have Hsx : (shift x : ch n.+3) = Some x by [].
          by rewrite /= -Ez2 /cupd Hsx eqxx.
    have Hsub : subst_proc (scons x id_ren) (subst_proc shift B) = B.
      rewrite subst_proc_comp
              (subst_proc_ext B (t := id_ren) (fun w : ch n.+2 => erefl)).
      exact: subst_proc_id.
    move: HR. rewrite /= Hsub => HR.
    exact: Esem_struct (SC_Par_Com _ _) HR.
Qed.

(** *** Multistep decomposition of a restriction (derived) *)
Lemma res_mred_inv n (X R : proc n) : X ⇛* R ->
  forall P : proc n.+2, X ≅ (ν) P ->
  exists P1, hybstar P P1 /\ R ≅ (ν) P1.
Proof.
  elim=> {X R} [X|X Y R Hst _ IH] P Heq.
  - exists P. split; [exact: Hyb_refl | exact: Heq].
  - have HXP : (ν) P ⇛ Y by apply: R_Struct (SC_Sym Heq) Hst (SC_Refl _).
    case: (res_red_inv HXP) => P2 [HY Hcase].
    case: (IH _ HY) => P3 [Hh HR].
    exists P3. split=> //.
    case: Hcase => [Hst2|Hc];
      [exact: Hyb_red Hst2 Hh | exact: Hyb_comm Hc Hh].
Qed.

Lemma hyb_sem n (P P1 : proc n.+2) :
  hybstar P P1 ->
  forall S (Δ : sctx n), SEM (cext S Δ) P ->
  exists S1, SEM (cext S1 Δ) P1.
Proof.
  elim=> {P P1} [P|P Q R0 Hst _ IH|P Q R0 Hc _ IH] S Δ HP.
  - by exists S.
  - apply: (IH S). exact: SEM_step Hst HP.
  - case: (comm_sem HP Hc) => S' HP'. exact: (IH S' _ HP').
Qed.

(** *** Compatibility of restriction *)
Lemma res_combine : forall k n S (Δ : sctx n) (P : proc n.+2),
  SEM (cext S Δ) P -> Esem k Δ ((ν) P).
Proof.
  elim=> [//|k IH] n S Δ P HP P' Hred.
  case: (res_mred_inv Hred (SC_Refl _)) => P1 [Hh HP'].
  case: (hyb_sem Hh HP) => {HP} S1 HP1.
  split.
  - (* conform *)
    move=> a x F R HFR Hpa.
    have Hnu : (ν) P1 ≅ F ∥ R := SC_Trans (SC_Sym HP') HFR.
    case: (res_expo_inv Hnu Hpa) => R0 [Hdec HRd].
    case: (HP1 1 _ (MR_refl _)) => C1 _ _.
    case: (C1 _ _ _ _ Hdec (prefix_at_ren (shift \o shift) Hpa))
      => S2 [HS2 Ha2].
    by exists S2.
  - (* value clauses *)
    move=> x S' HxS'.
    have HxIn : cext S1 Δ (shift (shift x)) = Some S' by exact: HxS'.
    case: S' HxS' HxIn => [| |T1 T2|T1 T2] HxS' HxIn /=.
    + move=> K R HFR.
      have Hnu : (ν) P1 ≅ CloseP x K ∥ R := SC_Trans (SC_Sym HP') HFR.
      case: (res_expo_inv Hnu (PA_Close x K)) => R0 [Hdec HRd].
      have HKsem : SEM (cext S1 (cupd x None Δ))
                     (subst_proc (shift \o shift) K ∥ R0).
        move=> j.
        case: (HP1 j.+1 _ (MR_refl _)) => _ V1 _.
        move: (V1 _ _ HxIn) => /= HV.
        move: (HV _ _ Hdec) => HK.
        exact: Esem_ext (cupd_shift2_cext S1 Δ x None) HK.
      move: (IH _ _ _ _ HKsem) => HC.
      apply: Esem_struct HC.
      apply: SC_Trans (res_pull K R0) _.
      exact: SC_Cong_Par (SC_Refl _) (SC_Sym HRd).
    + move=> K R HFR.
      have Hnu : (ν) P1 ≅ WaitP x K ∥ R := SC_Trans (SC_Sym HP') HFR.
      case: (res_expo_inv Hnu (PA_Wait x K)) => R0 [Hdec HRd].
      have HKsem : SEM (cext S1 (cupd x None Δ))
                     (subst_proc (shift \o shift) K ∥ R0).
        move=> j.
        case: (HP1 j.+1 _ (MR_refl _)) => _ V1 _.
        move: (V1 _ _ HxIn) => /= HV.
        move: (HV _ _ Hdec) => HK.
        exact: Esem_ext (cupd_shift2_cext S1 Δ x None) HK.
      move: (IH _ _ _ _ HKsem) => HC.
      apply: Esem_struct HC.
      apply: SC_Trans (res_pull K R0) _.
      exact: SC_Cong_Par (SC_Refl _) (SC_Sym HRd).
    + (* delegation send *)
      move=> y K R HFR.
      have Hnu : (ν) P1 ≅ DelP x y K ∥ R := SC_Trans (SC_Sym HP') HFR.
      case: (res_expo_inv Hnu (PA_DelS x y K)) => R0 [Hdec HRd].
      have Hy : Δ y = Some T1.
        case: (HP1 1 _ (MR_refl _)) => _ V1 _.
        move: (V1 _ _ HxIn) => /= HV.
        by case: (HV _ _ _ Hdec) => Hy _; exact: Hy.
      split=> //.
      have HKsem : SEM (cext S1 (cupd y None (cupd x (Some T2) Δ)))
                     (subst_proc (shift \o shift) K ∥ R0).
        move=> j.
        case: (HP1 j.+1 _ (MR_refl _)) => _ V1 _.
        move: (V1 _ _ HxIn) => /= HV.
        case: (HV _ _ _ Hdec) => _ HK.
        have Hctx : forall z,
            cupd (shift (shift y)) None
              (cupd (shift (shift x)) (Some T2) (cext S1 Δ)) z
          = cext S1 (cupd y None (cupd x (Some T2) Δ)) z.
          move=> z.
          rewrite -(cupd_shift2_cext S1 (cupd x (Some T2) Δ) y None z).
          rewrite /cupd. case: ifP => // _.
          exact: cupd_shift2_cext.
        exact: Esem_ext Hctx HK.
      move: (IH _ _ _ _ HKsem) => HC.
      apply: Esem_struct HC.
      apply: SC_Trans (res_pull K R0) _.
      exact: SC_Cong_Par (SC_Refl _) (SC_Sym HRd).
    + (* delegation receive: exchange the binders *)
      move=> K R HFR.
      have Hnu : (ν) P1 ≅ InSP x K ∥ R := SC_Trans (SC_Sym HP') HFR.
      case: (res_expo_inv Hnu (PA_DelR x K)) => R0 [Hdec HRd].
      have HeqA : forall z : ch n.+1,
          (rho3 \o up_ch (shift \o shift)) z = (shift \o shift) z.
        by case=> [w|].
      have HeqB : forall z : ch n.+2,
          (rho3 \o shift) z = up_ch (up_ch shift) z.
        by case=> [[w|]|].
      have HKsem : SEM (cext S1 (scons (Some T1) (cupd x (Some T2) Δ)))
                     (subst_proc (shift \o shift) K ∥
                      subst_proc (up_ch (up_ch shift)) R0).
        move=> j.
        case: (HP1 j.+1 _ (MR_refl _)) => _ V1 _.
        move: (V1 _ _ HxIn) => /= HV.
        move: (HV _ _ Hdec) => HK.
        have HK2 : Esem j (cext S1 (scons (Some T1) (cupd x (Some T2) Δ)))
                     (subst_proc rho3
                        (subst_proc (up_ch (shift \o shift)) K ∥
                         subst_proc shift R0)).
          apply: Esem_rename HK.
          - move=> z. right.
            case: z => [[[w|]|]|] //=.
            by rewrite (cupd_shift2_cext S1 Δ x (Some T2) (Some (Some w))).
          - move=> z1 z2 _ _.
            by case: z1 => [[[w1|]|]|]; case: z2 => [[[w2|]|]|] //= E.
        move: HK2. rewrite /= !subst_proc_comp
          (subst_proc_ext K HeqA) (subst_proc_ext R0 HeqB).
        by [].
      move: (IH _ _ _ _ HKsem) => HC.
      apply: Esem_struct HC.
      apply: SC_Trans (res_pull K _) _.
      apply: SC_Cong_Par (SC_Refl _) _.
      apply: SC_Sym.
      exact: (struct_eq_ren shift HRd).
  - (* semantic cut *)
    move=> Q0 HQ.
    have Hnn : (ν) P1 ≅ (ν) Q0 := SC_Trans (SC_Sym HP') HQ.
    case: (res_sem_inv (HP1 k) Hnn) => S'' HQ0.
    by exists S''.
Qed.

(** *** Compatibility of the four prefixes *)

(** Common step: a prefixed process only reduces to itself. *)
Ltac prefix_inert :=
  match goal with
  | [ Hred : ?P ⇛* ?P' |- _ ] =>
      have ? : P' = P by apply: (inert_mreduce _ Hred); done
  end.

Lemma compat_close n (Δ : sctx n) (x : ch n) K :
  Δ x = Some SClose -> cupd x None Δ ⊨ K -> Δ ⊨ CloseP x K.
Proof.
  move=> HxS HK.
  elim=> [//|k IHk] P' Hred.
  have HP' : P' = CloseP x K by apply: (inert_mreduce _ Hred).
  subst P'.
  split.
  - move=> a y F R HFR Hpa.
    case: (close_expo_inv HFR Hpa) => K1 [Ha Hy _ _]. subst a y.
    exists SClose. by rewrite HxS.
  - move=> y S' HyS'.
    case: S' HyS' => [| |S1 S2|S1 S2] HyS' /=.
    + move=> K0 R HFR.
      case: (close_expo_inv HFR (PA_Close y K0)) => K1 [_ Hy HF HKrel].
      subst y. case: HF => HK01. subst K1.
      apply: Esem_struct HKrel _. exact: HK.
    + move=> K0 R HFR.
      by case: (close_expo_inv HFR (PA_Wait y K0)) => K1 [].
    + move=> z K0 R HFR.
      by case: (close_expo_inv HFR (PA_DelS y z K0)) => K1 [].
    + move=> K0 R HFR.
      by case: (close_expo_inv HFR (PA_DelR y K0)) => K1 [].
  - move=> Q HQ.
    case: (prefix_res_inv (PA_Close x K) HQ) => D [HQdec HD0].
    exists SClose.
    have HX : Esem k (cext SClose Δ) (subst_proc (shift \o shift) (CloseP x K)).
      apply: Esem_rename IHk; first exact: shift2_ok.
      move=> z1 z2 _ _. exact: shift2_inj.
    apply: Esem_struct (SC_Sym HQdec) _.
    apply: Esem_struct _ HX.
    apply: SC_Trans (SC_Sym (SC_Par_Inact _)) _.
    exact: SC_Cong_Par (SC_Refl _) (SC_Sym (act0_inact HD0)).
Qed.

Lemma compat_wait n (Δ : sctx n) (x : ch n) K :
  Δ x = Some SWait -> cupd x None Δ ⊨ K -> Δ ⊨ WaitP x K.
Proof.
  move=> HxS HK.
  elim=> [//|k IHk] P' Hred.
  have HP' : P' = WaitP x K by apply: (inert_mreduce _ Hred).
  subst P'.
  split.
  - move=> a y F R HFR Hpa.
    case: (wait_expo_inv HFR Hpa) => K1 [Ha Hy _ _]. subst a y.
    exists SWait. by rewrite HxS.
  - move=> y S' HyS'.
    case: S' HyS' => [| |S1 S2|S1 S2] HyS' /=.
    + move=> K0 R HFR.
      by case: (wait_expo_inv HFR (PA_Close y K0)) => K1 [].
    + move=> K0 R HFR.
      case: (wait_expo_inv HFR (PA_Wait y K0)) => K1 [_ Hy HF HKrel].
      subst y. case: HF => HK01. subst K1.
      apply: Esem_struct HKrel _. exact: HK.
    + move=> z K0 R HFR.
      by case: (wait_expo_inv HFR (PA_DelS y z K0)) => K1 [].
    + move=> K0 R HFR.
      by case: (wait_expo_inv HFR (PA_DelR y K0)) => K1 [].
  - move=> Q HQ.
    case: (prefix_res_inv (PA_Wait x K) HQ) => D [HQdec HD0].
    exists SClose.
    have HX : Esem k (cext SClose Δ) (subst_proc (shift \o shift) (WaitP x K)).
      apply: Esem_rename IHk; first exact: shift2_ok.
      move=> z1 z2 _ _. exact: shift2_inj.
    apply: Esem_struct (SC_Sym HQdec) _.
    apply: Esem_struct _ HX.
    apply: SC_Trans (SC_Sym (SC_Par_Inact _)) _.
    exact: SC_Cong_Par (SC_Refl _) (SC_Sym (act0_inact HD0)).
Qed.

Lemma compat_del n (Δ : sctx n) (x y : ch n) K S1 S2 :
  Δ x = Some (SSend S1 S2) -> Δ y = Some S1 ->
  cupd y None (cupd x (Some S2) Δ) ⊨ K ->
  Δ ⊨ DelP x y K.
Proof.
  move=> HxS HyS HK.
  elim=> [//|k IHk] P' Hred.
  have HP' : P' = DelP x y K by apply: (inert_mreduce _ Hred).
  subst P'.
  split.
  - move=> a w F R HFR Hpa.
    case: (del_expo_inv HFR Hpa) => K1 [Ha Hw _ _]. subst a w.
    exists (SSend S1 S2). by rewrite HxS.
  - move=> w S' HwS'.
    case: S' HwS' => [| |T1 T2|T1 T2] HwS' /=.
    + move=> K0 R HFR.
      by case: (del_expo_inv HFR (PA_Close w K0)) => K1 [].
    + move=> K0 R HFR.
      by case: (del_expo_inv HFR (PA_Wait w K0)) => K1 [].
    + move=> z K0 R HFR.
      case: (del_expo_inv HFR (PA_DelS w z K0)) => K1 [_ Hw HF HKrel].
      subst w.
      case: HF => Hz HK01. subst z K1.
      have [ET1 ET2] : T1 = S1 /\ T2 = S2.
        by move: HwS'; rewrite HxS => -[-> ->].
      subst T1 T2.
      split=> //.
      apply: Esem_struct HKrel _. exact: HK.
    + move=> K0 R HFR.
      by case: (del_expo_inv HFR (PA_DelR w K0)) => K1 [].
  - move=> Q HQ.
    case: (prefix_res_inv (PA_DelS x y K) HQ) => D [HQdec HD0].
    exists SClose.
    have HX : Esem k (cext SClose Δ) (subst_proc (shift \o shift) (DelP x y K)).
      apply: Esem_rename IHk; first exact: shift2_ok.
      move=> z1 z2 _ _. exact: shift2_inj.
    apply: Esem_struct (SC_Sym HQdec) _.
    apply: Esem_struct _ HX.
    apply: SC_Trans (SC_Sym (SC_Par_Inact _)) _.
    exact: SC_Cong_Par (SC_Refl _) (SC_Sym (act0_inact HD0)).
Qed.

Lemma compat_ins n (Δ : sctx n) (x : ch n) (K : proc n.+1) S1 S2 :
  Δ x = Some (SRecv S1 S2) ->
  scons (Some S1) (cupd x (Some S2) Δ) ⊨ K ->
  Δ ⊨ InSP x K.
Proof.
  move=> HxS HK.
  elim=> [//|k IHk] P' Hred.
  have HP' : P' = InSP x K by apply: (inert_mreduce _ Hred).
  subst P'.
  split.
  - move=> a w F R HFR Hpa.
    case: (ins_expo_inv HFR Hpa) => K1 [Ha Hw _ _]. subst a w.
    exists (SRecv S1 S2). by rewrite HxS.
  - move=> w S' HwS'.
    case: S' HwS' => [| |T1 T2|T1 T2] HwS' /=.
    + move=> K0 R HFR.
      by case: (ins_expo_inv HFR (PA_Close w K0)) => K1 [].
    + move=> K0 R HFR.
      by case: (ins_expo_inv HFR (PA_Wait w K0)) => K1 [].
    + move=> z K0 R HFR.
      by case: (ins_expo_inv HFR (PA_DelS w z K0)) => K1 [].
    + move=> K0 R HFR.
      case: (ins_expo_inv HFR (PA_DelR w K0)) => K1 [_ Hw HF HKrel].
      subst w. case: HF => HK01. subst K1.
      have [ET1 ET2] : T1 = S1 /\ T2 = S2.
        by move: HwS'; rewrite HxS => -[-> ->].
      subst T1 T2.
      apply: Esem_struct HKrel _. exact: HK.
  - move=> Q HQ.
    case: (prefix_res_inv (PA_DelR x K) HQ) => D [HQdec HD0].
    exists SClose.
    have HX : Esem k (cext SClose Δ) (subst_proc (shift \o shift) (InSP x K)).
      apply: Esem_rename IHk; first exact: shift2_ok.
      move=> z1 z2 _ _. exact: shift2_inj.
    apply: Esem_struct (SC_Sym HQdec) _.
    apply: Esem_struct _ HX.
    apply: SC_Trans (SC_Sym (SC_Par_Inact _)) _.
    exact: SC_Cong_Par (SC_Refl _) (SC_Sym (act0_inact HD0)).
Qed.

(** *** The fundamental theorem *)
Theorem fundamental n (Δ : sctx n) (P : proc n) : Δ ⊢ P -> Δ ⊨ P.
Proof.
  move=> H; elim: H => {n Δ P}.
  - move=> n Δ _. exact: SEM_end.
  - move=> n Δ x P HxS _ IH. exact: compat_close HxS IH.
  - move=> n Δ x P HxS _ IH. exact: compat_wait HxS IH.
  - move=> n Δ x y P S1 S2 HxS HyS _ IH. exact: compat_del HxS HyS IH.
  - move=> n Δ x P S1 S2 HxS _ IH. exact: compat_ins HxS IH.
  - move=> n Δ Δ1 Δ2 P Q Hs _ IH1 _ IH2 k.
    exact: par_combine Hs (IH1 k) (IH2 k).
  - move=> n Δ S P _ IH k. exact: (res_combine k IH).
Qed.

(** *** End to end: well-typed processes never reach a communication
    error *)
Corollary safe_typed n (Δ : sctx n) (P : proc n) : Δ ⊢ P -> safe P.
Proof. move=> /fundamental. exact: adequacy. Qed.

End AssumedHarmony.

(** The section is closed: the theorems above now carry the interface
    as explicit premises, and depend on no axioms. *)
Print Assumptions fundamental.
Print Assumptions safe_typed.
