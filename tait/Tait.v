(** * How to (Re)Invent Tait's Method  (Robert Harper, Spring 2026)

    A mechanisation of the termination proof for a simply-typed lambda
    calculus with answers, unit, products and functions, via the method of
    hereditary termination (the "computability"/logical-relations method).

    Representation choices (house style, cf. Linearity_Predicates/well_scoped):
      - variables    : [var n], the finite type of n elements built from
                       nested [option] (well-scoped de Bruijn);
      - terms        : [tm n], intrinsically scoped by the number of free vars;
      - substitutions: functions [var n -> tm m], with [scons]/[up]/[shift].
    Typing is a separate relation (extrinsic), so Preservation stays a real
    theorem, matching the note. *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import FunctionalExtensionality Eqdep_dec PeanoNat.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** Types  (A ::= Ans | 1 | A1 * A2 | A1 -> A2) *)
Inductive ty : Set :=
| Ans  : ty
| Unit : ty
| Prod : ty -> ty -> ty
| Arr  : ty -> ty -> ty.

(** ** Variables: the finite type of [n] elements *)
Fixpoint var (n : nat) : Type :=
  match n with
  | 0    => False
  | S m  => option (var m)
  end.

(** ** Terms, indexed by scope size *)
Inductive tm (n : nat) : Type :=
| Var   : var n -> tm n
| Yes   : tm n
| No    : tm n
| UnitI : tm n
| Pair  : tm n -> tm n -> tm n
| Fst   : tm n -> tm n
| Snd   : tm n -> tm n
| Lam   : tm n.+1 -> tm n
| App   : tm n -> tm n -> tm n.

Arguments Var {n}.
Arguments Yes {n}.
Arguments No {n}.
Arguments UnitI {n}.
Arguments Pair {n}.
Arguments Fst {n}.
Arguments Snd {n}.
Arguments Lam {n}.
Arguments App {n}.

(** ** Renamings and substitutions *)
Definition ren (n m : nat) := var n -> var m.
Definition sub (n m : nat) := var n -> tm m.

Definition id_ren {n} : ren n n := fun x => x.

Definition scons {X : Type} {n : nat} (x : X) (s : var n -> X) : var n.+1 -> X :=
  fun z => match z with
           | None   => x
           | Some i => s i
           end.

Definition shift {n : nat} : ren n n.+1 := @Some _.
Definition zero {n : nat} : var n.+1 := None.

Definition up_ren {n m : nat} (xi : ren n m) : ren n.+1 m.+1 :=
  scons zero (fun i => shift (xi i)).

Fixpoint rename {n m : nat} (xi : ren n m) (t : tm n) : tm m :=
  match t with
  | Var x    => Var (xi x)
  | Yes      => Yes
  | No       => No
  | UnitI    => UnitI
  | Pair a b => Pair (rename xi a) (rename xi b)
  | Fst a    => Fst (rename xi a)
  | Snd a    => Snd (rename xi a)
  | Lam b    => Lam (rename (up_ren xi) b)
  | App a b  => App (rename xi a) (rename xi b)
  end.

Definition up_sub {n m : nat} (s : sub n m) : sub n.+1 m.+1 :=
  scons (Var zero) (fun i => rename shift (s i)).

Fixpoint subst {n m : nat} (s : sub n m) (t : tm n) : tm m :=
  match t with
  | Var x    => s x
  | Yes      => Yes
  | No       => No
  | UnitI    => UnitI
  | Pair a b => Pair (subst s a) (subst s b)
  | Fst a    => Fst (subst s a)
  | Snd a    => Snd (subst s a)
  | Lam b    => Lam (subst (up_sub s) b)
  | App a b  => App (subst s a) (subst s b)
  end.

(** Single substitution [ [u/0]t ]. *)
Definition subst1 {n : nat} (u : tm n) (t : tm n.+1) : tm n :=
  subst (scons u (@Var n)) t.

(** ** Substitution fusion laws (Autosubst-style, hand-rolled) *)

Lemma up_ren_comp n m p (xi1 : ren n m) (xi2 : ren m p) :
  up_ren (xi2 \o xi1) = up_ren xi2 \o up_ren xi1.
Proof. apply: functional_extensionality; by case=> [i|]. Qed.

Lemma rename_rename n (t : tm n) : forall m p (xi1 : ren n m) (xi2 : ren m p),
  rename xi2 (rename xi1 t) = rename (xi2 \o xi1) t.
Proof.
  elim: t => [n' v|n'|n'|n'|n' a IHa b IHb|n' a IHa|n' a IHa|n' b IHb|n' a IHa b IHb] m p xi1 xi2 /=;
    rewrite ?IHa ?IHb //.
  by rewrite up_ren_comp.
Qed.

Lemma up_sub_ren n m p (xi : ren n m) (s : sub m p) :
  up_sub s \o up_ren xi = up_sub (s \o xi).
Proof. apply: functional_extensionality; by case=> [i|]. Qed.

Lemma subst_rename n (t : tm n) : forall m p (xi : ren n m) (s : sub m p),
  subst s (rename xi t) = subst (s \o xi) t.
Proof.
  elim: t => [n' v|n'|n'|n'|n' a IHa b IHb|n' a IHa|n' a IHa|n' b IHb|n' a IHa b IHb] m p xi s /=;
    rewrite ?IHa ?IHb //.
  by rewrite up_sub_ren.
Qed.

Lemma up_ren_shift n m (xi : ren n m) : up_ren xi \o shift = shift \o xi.
Proof. apply: functional_extensionality => z; by []. Qed.

Lemma up_ren_sub n m p (xi : ren m p) (s : sub n m) :
  rename (up_ren xi) \o up_sub s = up_sub (rename xi \o s).
Proof.
  apply: functional_extensionality; case=> [i|] //=.
  by rewrite !rename_rename up_ren_shift.
Qed.

Lemma rename_subst n (t : tm n) : forall m p (xi : ren m p) (s : sub n m),
  rename xi (subst s t) = subst (rename xi \o s) t.
Proof.
  elim: t => [n' v|n'|n'|n'|n' a IHa b IHb|n' a IHa|n' a IHa|n' b IHb|n' a IHa b IHb] m p xi s /=;
    rewrite ?IHa ?IHb //.
  by rewrite up_ren_sub.
Qed.

Lemma subst_ext n m (s s' : sub n m) (t : tm n) :
  (forall x, s x = s' x) -> subst s t = subst s' t.
Proof. move=> H; have -> : s = s' by apply: functional_extensionality. by []. Qed.

Lemma up_sub_sub n m p (s1 : sub n m) (s2 : sub m p) :
  subst (up_sub s2) \o up_sub s1 = up_sub (subst s2 \o s1).
Proof.
  apply: functional_extensionality; case=> [i|] //=.
  by rewrite subst_rename rename_subst.
Qed.

Lemma subst_subst n (t : tm n) : forall m p (s1 : sub n m) (s2 : sub m p),
  subst s2 (subst s1 t) = subst (subst s2 \o s1) t.
Proof.
  elim: t => [n' v|n'|n'|n'|n' a IHa b IHb|n' a IHa|n' a IHa|n' b IHb|n' a IHa b IHb] m p s1 s2 /=;
    rewrite ?IHa ?IHb //.
  by rewrite up_sub_sub.
Qed.

Lemma up_sub_id n : up_sub (@Var n) = @Var n.+1.
Proof. apply: functional_extensionality; by case=> [i|]. Qed.

Lemma subst_id n (t : tm n) : subst (@Var n) t = t.
Proof.
  elim: t => [n' v|n'|n'|n'|n' a IHa b IHb|n' a IHa|n' a IHa|n' b IHb|n' a IHa b IHb] /=;
    rewrite ?IHa ?IHb //.
  by rewrite up_sub_id IHb.
Qed.

Lemma scons_var_shift n (u : tm n) : scons u (@Var n) \o shift = @Var n.
Proof. apply: functional_extensionality => z; by []. Qed.

(** The single fact the fundamental theorem needs about substitution:
    substituting [u] for var 0 after pushing a substitution [s] under a
    binder is the same as extending [s] with [u].  This is [ [u/0]((up s) t)
    = (u .: s) t ]. *)
Lemma subst_scons_up n m (u : tm m) (s : sub n m) (t : tm n.+1) :
  subst (scons u (@Var m)) (subst (up_sub s) t) = subst (scons u s) t.
Proof.
  rewrite subst_subst; apply: subst_ext; case=> [i|] //=.
  by rewrite subst_rename scons_var_shift subst_id.
Qed.

Lemma up_ren_id n : up_ren (@id_ren n) = @id_ren n.+1.
Proof. apply: functional_extensionality; by case=> [i|]. Qed.

Lemma rename_id n (t : tm n) : rename (@id_ren n) t = t.
Proof.
  elim: t => [n' v|n'|n'|n'|n' a IHa b IHb|n' a IHa|n' a IHa|n' b IHb|n' a IHa b IHb] /=;
    rewrite ?IHa ?IHb //.
  by rewrite up_ren_id IHb.
Qed.

(** ** Statics  (Figure 1)

    Contexts are functions [var n -> ty]; the VAR rule reads the type off the
    context, and LAM extends it with [scons]. *)
Reserved Notation "Γ ⊢ M ∈ A" (at level 68, M at level 99).
Inductive has_type : forall n, (var n -> ty) -> tm n -> ty -> Prop :=
| T_Var  : forall n (Γ : var n -> ty) x, Γ ⊢ Var x ∈ Γ x
| T_Yes  : forall n (Γ : var n -> ty), Γ ⊢ Yes ∈ Ans
| T_No   : forall n (Γ : var n -> ty), Γ ⊢ No ∈ Ans
| T_Unit : forall n (Γ : var n -> ty), Γ ⊢ UnitI ∈ Unit
| T_Pair : forall n (Γ : var n -> ty) M1 M2 A1 A2,
    Γ ⊢ M1 ∈ A1 -> Γ ⊢ M2 ∈ A2 -> Γ ⊢ Pair M1 M2 ∈ Prod A1 A2
| T_Fst  : forall n (Γ : var n -> ty) M A1 A2,
    Γ ⊢ M ∈ Prod A1 A2 -> Γ ⊢ Fst M ∈ A1
| T_Snd  : forall n (Γ : var n -> ty) M A1 A2,
    Γ ⊢ M ∈ Prod A1 A2 -> Γ ⊢ Snd M ∈ A2
| T_Lam  : forall n (Γ : var n -> ty) M A1 A2,
    scons A1 Γ ⊢ M ∈ A2 -> Γ ⊢ Lam M ∈ Arr A1 A2
| T_App  : forall n (Γ : var n -> ty) M1 M2 A1 A2,
    Γ ⊢ M1 ∈ Arr A1 A2 -> Γ ⊢ M2 ∈ A1 -> Γ ⊢ App M1 M2 ∈ A2
where "Γ ⊢ M ∈ A" := (has_type Γ M A).

(** ** Dynamics  (Figure 2), a deterministic head reduction on closed terms.

    Pairs and lambdas are values regardless of their components (lazy). *)
Inductive value : tm 0 -> Prop :=
| V_Yes  : value Yes
| V_No   : value No
| V_Unit : value UnitI
| V_Pair : forall M1 M2, value (Pair M1 M2)
| V_Lam  : forall M, value (Lam M).

Reserved Notation "M ~> N" (at level 70).
Inductive step : tm 0 -> tm 0 -> Prop :=
| S_Fst     : forall M M', M ~> M' -> Fst M ~> Fst M'
| S_Snd     : forall M M', M ~> M' -> Snd M ~> Snd M'
| S_FstPair : forall M1 M2, Fst (Pair M1 M2) ~> M1
| S_SndPair : forall M1 M2, Snd (Pair M1 M2) ~> M2
| S_App     : forall M1 M1' M2, M1 ~> M1' -> App M1 M2 ~> App M1' M2
| S_AppLam  : forall (M : tm 1) (M2 : tm 0), App (Lam M) M2 ~> subst1 M2 M
where "M ~> N" := (step M N).

(** Reflexive-transitive closure. *)
Reserved Notation "M ~>* N" (at level 70).
Inductive mstep : tm 0 -> tm 0 -> Prop :=
| MS_refl : forall M, M ~>* M
| MS_step : forall M M' M'', M ~> M' -> M' ~>* M'' -> M ~>* M''
where "M ~>* N" := (mstep M N).

Lemma mstep1 M M' : M ~> M' -> M ~>* M'.
Proof. move=> H; apply: MS_step H (MS_refl _). Qed.

Lemma mstep_trans M1 M2 M3 : M1 ~>* M2 -> M2 ~>* M3 -> M1 ~>* M3.
Proof. move=> H; elim: H => [M|Ma Mb Mc Hs _ IH] H23 //. by apply: MS_step Hs (IH H23). Qed.

(** Congruence of multistep with the head-reduction contexts. *)
Lemma mstep_Fst M M' : M ~>* M' -> Fst M ~>* Fst M'.
Proof. elim=> [M0|Ma Mb Mc Hs _ IH]; first exact: MS_refl. by apply: MS_step (S_Fst Hs) IH. Qed.

Lemma mstep_Snd M M' : M ~>* M' -> Snd M ~>* Snd M'.
Proof. elim=> [M0|Ma Mb Mc Hs _ IH]; first exact: MS_refl. by apply: MS_step (S_Snd Hs) IH. Qed.

Lemma mstep_App M M' N : M ~>* M' -> App M N ~>* App M' N.
Proof. elim=> [M0|Ma Mb Mc Hs _ IH]; first exact: MS_refl. by apply: MS_step (S_App N Hs) IH. Qed.

(** ** Hereditary termination  (Figure 3)

    [HT A M] is defined by recursion on the *type* [A]: a hereditarily
    terminating term evaluates to a value of the right shape, whose
    constituents (for compound types) are themselves hereditarily
    terminating -- and, at function type, that maps HT arguments to HT
    results. *)
Fixpoint HT (A : ty) : tm 0 -> Prop :=
  match A with
  | Ans        => fun M => (M ~>* Yes) \/ (M ~>* No)
  | Unit       => fun M => M ~>* UnitI
  | Prod A1 A2 => fun M => exists M1 M2, (M ~>* Pair M1 M2) /\ HT A1 M1 /\ HT A2 M2
  | Arr  A1 A2 => fun M => exists M', (M ~>* Lam M') /\
                                     (forall N, HT A1 N -> HT A2 (subst1 N M'))
  end.

(** *** Lemma 6 (Head Expansion): HT is closed under reverse execution. *)
Lemma head_expansion A M M' : M ~> M' -> HT A M' -> HT A M.
Proof.
  move=> H; case: A => /=.
  - by move=> [Hm|Hm]; [left|right]; apply: MS_step H Hm.
  - by move=> Hm; apply: MS_step H Hm.
  - move=> A1 A2 [M1 [M2 [Hm [H1 H2]]]]. by exists M1, M2; split; [apply: MS_step H Hm|].
  - move=> A1 A2 [M2 [Hm Hf]]. by exists M2; split; [apply: MS_step H Hm|].
Qed.

Lemma head_expansion_multi A M M' : M ~>* M' -> HT A M' -> HT A M.
Proof. elim=> [//|Ma Mb Mc Hs _ IH] Hc. apply: head_expansion Hs _. exact: IH. Qed.

(** ** The fundamental theorem  (Theorem 7)

    Extend HT to closing substitutions [g : var n -> tm 0], then prove every
    well-typed term is hereditarily terminating under any HT closing
    substitution.  [Γ ⊨ M ∈ A] is the note's judgment [Γ ≫ M ∈ A]. *)
Definition HTsub {n} (Γ : var n -> ty) (g : sub n 0) : Prop :=
  forall x, HT (Γ x) (g x).

Definition sem {n} (Γ : var n -> ty) (M : tm n) (A : ty) : Prop :=
  forall g, HTsub Γ g -> HT A (subst g M).
Notation "Γ ⊨ M ∈ A" := (sem Γ M A) (at level 68, M at level 99).

(** Extending a HT closing substitution with a HT term. *)
Lemma HTsub_scons n (Γ : var n -> ty) g A1 N :
  HTsub Γ g -> HT A1 N -> HTsub (scons A1 Γ) (scons N g).
Proof. move=> Hg HN; case=> [i|] /=; [exact: (Hg i) | exact: HN]. Qed.

Theorem fundamental n (Γ : var n -> ty) (M : tm n) A :
  Γ ⊢ M ∈ A -> Γ ⊨ M ∈ A.
Proof.
  move=> H; elim: H => {n Γ M A}.
  - move=> n0 Γ x g Hg /=. exact: (Hg x).
  - move=> n0 Γ g Hg /=. left. exact: MS_refl.
  - move=> n0 Γ g Hg /=. right. exact: MS_refl.
  - move=> n0 Γ g Hg /=. exact: MS_refl.
  - move=> n0 Γ M1 M2 A1 A2 _ IH1 _ IH2 g Hg /=.
    exists (subst g M1), (subst g M2); split; first exact: MS_refl.
    split; [exact: (IH1 g Hg) | exact: (IH2 g Hg)].
  - move=> n0 Γ M0 A1 A2 _ IH g Hg /=.
    move: (IH g Hg) => /= [N1 [N2 [Hm [H1 _]]]].
    apply: (head_expansion_multi (M' := N1)); last exact: H1.
    apply: (mstep_trans (mstep_Fst Hm)). exact: (mstep1 (S_FstPair N1 N2)).
  - move=> n0 Γ M0 A1 A2 _ IH g Hg /=.
    move: (IH g Hg) => /= [N1 [N2 [Hm [_ H2]]]].
    apply: (head_expansion_multi (M' := N2)); last exact: H2.
    apply: (mstep_trans (mstep_Snd Hm)). exact: (mstep1 (S_SndPair N1 N2)).
  - move=> n0 Γ M0 A1 A2 _ IH g Hg /=.
    exists (subst (up_sub g) M0); split; first exact: MS_refl.
    move=> N HN. rewrite /subst1 subst_scons_up. apply: IH. exact: (HTsub_scons Hg HN).
  - move=> n0 Γ M1 M2 A1 A2 _ IH1 _ IH2 g Hg /=.
    move: (IH1 g Hg) => /= [body [Hm Hf]].
    apply: (head_expansion_multi (M' := subst1 (subst g M2) body)); last first.
      apply: Hf. exact: (IH2 g Hg).
    apply: (mstep_trans (mstep_App _ Hm)). exact: (mstep1 (S_AppLam body (subst g M2))).
Qed.

(** *** Theorem 3 (Termination): every closed program of answer type
    accepts or rejects. *)
Theorem termination (M : tm 0) (Γ : var 0 -> ty) :
  Γ ⊢ M ∈ Ans -> (M ~>* Yes) \/ (M ~>* No).
Proof.
  move=> /fundamental Hsem.
  have Hg : HTsub Γ (@Var 0) by case.
  have R := Hsem _ Hg. rewrite subst_id in R. exact: R.
Qed.

(** ** Preservation  (Theorem 2)

    Independent of the termination proof above; included to complete the
    note's stated theorems.  Needs the typing renaming/substitution lemmas
    (a substitution that respects contexts preserves typing), then induction
    on the transition.  Inversions of the (scope-indexed) typing relation are
    packaged as lemmas; the [existT] equalities that [inversion] produces are
    discharged by decidable equality on [nat] (axiom-free). *)

Lemma ty_rename n (Γ : var n -> ty) M A (H : Γ ⊢ M ∈ A) :
  forall m (Δ : var m -> ty) (xi : ren n m),
    (forall x, Δ (xi x) = Γ x) -> Δ ⊢ rename xi M ∈ A.
Proof.
  elim: H => {n Γ M A}.
  - move=> n Γ x m Δ xi Hxi /=. rewrite -(Hxi x). exact: T_Var.
  - move=> n Γ m Δ xi Hxi /=. exact: T_Yes.
  - move=> n Γ m Δ xi Hxi /=. exact: T_No.
  - move=> n Γ m Δ xi Hxi /=. exact: T_Unit.
  - move=> n Γ M1 M2 A1 A2 _ IH1 _ IH2 m Δ xi Hxi /=.
    apply: T_Pair; [exact: (IH1 m Δ xi Hxi) | exact: (IH2 m Δ xi Hxi)].
  - move=> n Γ M0 A1 A2 _ IH m Δ xi Hxi /=. apply: T_Fst. exact: (IH m Δ xi Hxi).
  - move=> n Γ M0 A1 A2 _ IH m Δ xi Hxi /=. apply: T_Snd. exact: (IH m Δ xi Hxi).
  - move=> n Γ M0 A1 A2 _ IH m Δ xi Hxi /=.
    apply: T_Lam. apply: (IH m.+1 (scons A1 Δ) (up_ren xi)).
    by case=> [i|] /=; rewrite ?Hxi.
  - move=> n Γ M1 M2 A1 A2 _ IH1 _ IH2 m Δ xi Hxi /=.
    apply: T_App; [exact: (IH1 m Δ xi Hxi) | exact: (IH2 m Δ xi Hxi)].
Qed.

Lemma ty_weaken n (Γ : var n -> ty) M A B :
  Γ ⊢ M ∈ A -> scons B Γ ⊢ rename shift M ∈ A.
Proof. move=> H; apply: (ty_rename H) => x; exact: erefl. Qed.

Lemma ty_subst n (Γ : var n -> ty) M A (H : Γ ⊢ M ∈ A) :
  forall m (Δ : var m -> ty) (g : sub n m),
    (forall x, Δ ⊢ g x ∈ Γ x) -> Δ ⊢ subst g M ∈ A.
Proof.
  elim: H => {n Γ M A}.
  - move=> n Γ x m Δ g Hg /=. exact: (Hg x).
  - move=> n Γ m Δ g Hg /=. exact: T_Yes.
  - move=> n Γ m Δ g Hg /=. exact: T_No.
  - move=> n Γ m Δ g Hg /=. exact: T_Unit.
  - move=> n Γ M1 M2 A1 A2 _ IH1 _ IH2 m Δ g Hg /=.
    apply: T_Pair; [exact: (IH1 m Δ g Hg) | exact: (IH2 m Δ g Hg)].
  - move=> n Γ M0 A1 A2 _ IH m Δ g Hg /=. apply: T_Fst. exact: (IH m Δ g Hg).
  - move=> n Γ M0 A1 A2 _ IH m Δ g Hg /=. apply: T_Snd. exact: (IH m Δ g Hg).
  - move=> n Γ M0 A1 A2 _ IH m Δ g Hg /=.
    apply: T_Lam. apply: (IH m.+1 (scons A1 Δ) (up_sub g)).
    case=> [i|] /=; [apply: ty_weaken; exact: (Hg i) | exact: T_Var].
  - move=> n Γ M1 M2 A1 A2 _ IH1 _ IH2 m Δ g Hg /=.
    apply: T_App; [exact: (IH1 m Δ g Hg) | exact: (IH2 m Δ g Hg)].
Qed.

Lemma ty_subst1 n (Γ : var n -> ty) M2 M A1 A :
  scons A1 Γ ⊢ M ∈ A -> Γ ⊢ M2 ∈ A1 -> Γ ⊢ subst1 M2 M ∈ A.
Proof.
  move=> HM HM2. rewrite /subst1. apply: (ty_subst HM).
  case=> [i|] /=; [exact: T_Var | exact: HM2].
Qed.

(** Inversions of the typing relation at scope 0. *)
Ltac ht_inv H :=
  inversion H; subst;
  repeat match goal with
  | [ E : existT _ ?k _ = existT _ ?k _ |- _ ] =>
      apply (inj_pair2_eq_dec _ Nat.eq_dec) in E; subst
  end.

Lemma ty_Fst_inv (Γ : var 0 -> ty) M A :
  Γ ⊢ Fst M ∈ A -> exists A2, Γ ⊢ M ∈ Prod A A2.
Proof. move=> H; ht_inv H; by exists A2. Qed.

Lemma ty_Snd_inv (Γ : var 0 -> ty) M A :
  Γ ⊢ Snd M ∈ A -> exists A1, Γ ⊢ M ∈ Prod A1 A.
Proof. move=> H; ht_inv H; by exists A1. Qed.

Lemma ty_Pair_inv (Γ : var 0 -> ty) M1 M2 B1 B2 :
  Γ ⊢ Pair M1 M2 ∈ Prod B1 B2 -> (Γ ⊢ M1 ∈ B1) /\ (Γ ⊢ M2 ∈ B2).
Proof. move=> H; ht_inv H; by split. Qed.

Lemma ty_Lam_inv (Γ : var 0 -> ty) M A1 A2 :
  Γ ⊢ Lam M ∈ Arr A1 A2 -> scons A1 Γ ⊢ M ∈ A2.
Proof. move=> H; ht_inv H; assumption. Qed.

Lemma ty_App_inv (Γ : var 0 -> ty) M1 M2 A :
  Γ ⊢ App M1 M2 ∈ A -> exists A1, (Γ ⊢ M1 ∈ Arr A1 A) /\ (Γ ⊢ M2 ∈ A1).
Proof. move=> H; ht_inv H; exists A1; by split. Qed.

(** *** Theorem 2 (Preservation), by induction on the transition. *)
Theorem preservation (M M' : tm 0) (A : ty) (Γ : var 0 -> ty) :
  M ~> M' -> Γ ⊢ M ∈ A -> Γ ⊢ M' ∈ A.
Proof.
  move=> H; move: A; elim: H => {M M'}.
  - move=> M0 M0' _ IH A /ty_Fst_inv [A2 HM]. apply: T_Fst. exact: (IH _ HM).
  - move=> M0 M0' _ IH A /ty_Snd_inv [A1 HM]. apply: T_Snd. exact: (IH _ HM).
  - move=> M1 M2 A /ty_Fst_inv [A2 /ty_Pair_inv [H1 _]]. exact: H1.
  - move=> M1 M2 A /ty_Snd_inv [A1 /ty_Pair_inv [_ H2]]. exact: H2.
  - move=> M1 M1' M2 _ IH A /ty_App_inv [A1 [HM1 HM2]].
    apply: T_App; [exact: (IH _ HM1) | exact: HM2].
  - move=> M0 M2 A /ty_App_inv [A1 [/ty_Lam_inv HM HM2]]. exact: (ty_subst1 HM HM2).
Qed.

(** ** Axiom audit

    [Print Assumptions] reports every axiom -- and any [Admitted] proof, which
    becomes an axiom -- that a result transitively depends on.  These run on
    every build, so the footprint is visible in the compile log.  Note also
    that every proof here ends in [Qed]: an incomplete proof would already
    fail to compile, so the only way to smuggle in a hole is [Admitted], which
    this audit would then expose.

    Expected:
      - [preservation] : Closed under the global context (axiom-free).
      - [fundamental], [termination] : only [functional_extensionality_dep]
        (inherent to the substitutions-as-functions encoding). *)
Print Assumptions preservation.
Print Assumptions fundamental.
Print Assumptions termination.
