(** * Foundations: names, renamings, and finite search

    The scope infrastructure the whole development rests on.  Names
    are well-scoped de Bruijn indices: [ch n] is the finite type of
    names in scope [n], built from nested [option]s, and a renaming
    is a plain function [ch n -> ch m].  Because [ch n] is finite and
    has decidable equality, a predicate over it can be searched
    ([find_ch]) -- which is what makes the pushforward of a context
    along a renaming computable, in [PolSem.v] and [PolFN.v].

    HISTORY.  This material was split across [synsem.v] (whose process
    syntax, structural congruence and reduction belonged to the
    ≅-based presentation) and the equivariance file of the
    double-binder presentation.  Both presentations are in
    [cemetery/], which keeps the originals; the process syntax of the
    live line is [PolProc.v].  In particular the old process
    notations ([∅], [∥], [(ν)], ...) are gone, so [pol_scope] owns
    them now without shadowing. *)

From mathcomp Require Import all_ssreflect.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** Names *)

Fixpoint ch (n : nat) : Type :=
  match n with
  | 0 => False
  | S m => option (ch m)
  end.

Lemma ch_eq_dec {n : nat} (x y : ch n) : {x = y} + {x <> y}.
  induction n as [|m IHm] => //.
  decide equality.
Defined.

Definition ch_eqb {n : nat} (x y : ch n) : bool :=
  if ch_eq_dec x y then true else false.

Lemma ch_eqP {n : nat} : Equality.axiom (@ch_eqb n).
Proof.
  move=> x y. rewrite /ch_eqb.
  destruct (ch_eq_dec x y); now constructor.
Qed.

HB.instance Definition _ n := hasDecEq.Build (ch n) ch_eqP.

(** ** Renamings *)

Definition ren n m := ch n -> ch m.

Definition id_ren {n} : ren n n := fun x => x.

(** Extending a map by a value at the fresh name. *)
Definition scons {X : Type} {n : nat}
  (x : X) (sigma : ch n -> X) (z : ch n.+1) : X :=
  match z with
  | None => x
  | Some i => sigma i
  end.

Definition shift {n : nat} : ren n n.+1 := Some.

Definition zero {n : nat} : ch n.+1 := None.
Definition one {n : nat} : ch n.+2 := shift zero.

(** Lifting a renaming under a binder. *)
Definition up_ch {n m : nat} (sigma : ren n m) : ren n.+1 m.+1 :=
  @scons _ n zero (fun i => shift (sigma i)).

(** Transposition of two names. *)
Definition swap_ch {n : nat} (n1 n2 : ch n) :=
  fun n => if n == n1 then n2 else if n == n2 then n1 else n.

(** ** Searching the finite name space

    [ch m] has [m] inhabitants, so a decidable predicate over it can
    be decided by exhaustive search. *)

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
