From mathcomp Require Import all_ssreflect.
From HB Require Import structures.

  Set Implicit Arguments.

  (* Endpoints *) 
  Fixpoint ch (n : nat) : Type :=
    match n with
    | 0 => False
    | S m => option (ch m)
    end.

  (* Decidability of equality on fin and ch *) 
  Lemma ch_eq_dec {n : nat} (x y : ch n) : {x = y} + {x <> y}.
    induction n as [|m IHm] => //.
    decide equality.
  Defined.
  
  (* Boolean equality for fin - here called ch *)
  Definition ch_eqb {n : nat} (x y : ch n) : bool :=
    if ch_eq_dec x y then true else false.

  (* Proof that fin_eq reflects Leibniz equality *)
  Lemma ch_eqP {n : nat} : Equality.axiom (@ch_eqb n).
  Proof.
    move=> x y. rewrite /ch_eqb.
    destruct (ch_eq_dec x y);  now constructor.
  Qed.
  
  HB.instance Definition _ n := hasDecEq.Build (ch n) ch_eqP.

(* StartProc *) 
  Inductive proc (n : nat) : Type :=
  | EndP : proc n
  | WaitP : ch n -> proc n -> proc n
  | CloseP : ch n -> proc n -> proc n
  | ResP : proc n.+2 -> proc n
  | ParP : proc n -> proc n -> proc n
  | InSP : ch n -> proc n.+1 -> proc n
  | DelP : ch n -> ch n -> proc n -> proc n.
  (* EndProc *) 

  Notation "∅" := EndP .
  Infix "∥" := ParP (at level 48, left associativity).
  Notation "(ν) p " := (ResP p) (at level 44, right associativity).
  Notation "x ? (_)․ P" :=
    (InSP x P) (at level 44, right associativity).
  Notation "x ? ․ P" :=
    (WaitP x P) (at level 44, right associativity).
  Notation "x ! ․ P" :=
    (CloseP x P) (at level 44, right associativity).
  Notation "x ! y ․ P" :=
    (DelP x y P) (at level 44, right associativity).

  (* Substitution type (renaming) *)
  Definition ren n m := ch n -> ch m.

  (* Identity *) 
  Definition id_ren {n} : ren n n := fun x => x.

  (* scons for pi-calculus standard substitution *) 
  Definition scons {X : Type} {n : nat}
    (x : X) (sigma : ch n -> X) (z : ch n.+1) :  X :=
    match z with
    | None => x
    | Some i => sigma i
    end.

  
  Notation "s .: sigma" := (scons s sigma) (at level 55, sigma at next level, right associativity) : subst_scope.
  Notation "s '..'" := (scons s id_ren) (at level 1, format "s ..") : subst_scope.

  (* shifting of names *) 
  Definition shift {n : nat} : ren n n.+1 := Some . 

  Definition zero {n : nat} : ch n.+1 := None.
  Definition one {n : nat} : ch n.+2 := shift zero.
  Definition two {n : nat} : ch n.+3 := shift one.
  Definition three {n : nat} : ch n.+4 := shift two.
  
  (* lifing up a substitution to a +1 world *) 
  Definition up_ch {n m : nat} (sigma : ren n m) : ren n.+1 m.+1 :=
    @scons _ n zero (fun i => shift (sigma i)).
  
  (* process substitution *) 
  Fixpoint subst_proc {n m : nat} (
      sigma : ren n m) (P : proc n) : proc m :=
    match P with
    | ∅ _ => ∅ m
  | x ? ․ Q => sigma x ? ․ subst_proc sigma Q
  | x ! ․ Q => sigma x ! ․ subst_proc sigma Q
  | (ν) Q => (ν) subst_proc (up_ch (up_ch sigma)) Q
  | P1 ∥ P2 => subst_proc sigma P1 ∥ subst_proc sigma P2
  | x ? (_)․Q => sigma x ? (_)․subst_proc  (up_ch sigma) Q
  | x ! y ․ Q => sigma x ! sigma y ․ subst_proc sigma Q
  end.

  Notation "< sigma >" := (subst_proc sigma).
 
  Definition swap_ch {n : nat} (n1 n2 : ch n) :=
    fun n => if n == n1 then n2 else if n == n2 then n1 else n. 

  
  (* Structural Equivalence (or Congruence) *)
  Reserved Notation "P '≅' Q" (at level 60, right associativity).
  (* StartSE *)
  Inductive struct_eq {n:nat} : (proc n) -> (proc n) -> Prop :=
  | SC_Par_Com : forall P Q : proc n, P ∥ Q ≅ Q ∥ P
  | SC_Par_Assoc : forall P Q R : proc n, P ∥ Q ∥ R ≅ P ∥ (Q ∥ R)
  | SC_Par_Inact : forall P : proc n, P ∥  ∅ _ ≅ P
  | SC_Res_Scope : forall (P : proc n.+2) (Q : proc n),
      (ν) P ∥ Q ≅  (ν) (P ∥ (< (shift \o shift) >) Q)
  | SC_Res_SwapC : forall P : proc n.+2,
      (ν) P ≅ (ν) (< swap_ch zero one >) P
  | SC_Res_SwapB : forall P : proc n.+4,
      (ν) (ν) P ≅ (ν) (ν) (< swap_ch one three >)
        ((< swap_ch zero two >) P)  (* EndSE *)
  (*  StartInact *)
  | SC_Res_Inact : (ν) ∅ _ ≅ ∅ _ (*  EndInact *)                       
  | SC_Refl : forall P : proc n, P ≅ P
                                   
  | SC_Sym : forall P Q : proc n,  P ≅ Q -> Q ≅ P
                 
  | SC_Trans : forall P Q R : proc n, P ≅ Q -> Q ≅ R -> P ≅ R
                                                          
  | SC_Cong_Par : forall P P' Q Q' : proc n,
      P ≅ P' -> Q ≅ Q' -> P ∥ Q ≅ P' ∥ Q'
                            
  | SC_Cong_Res : forall P P' : proc n.+2, P ≅ P' -> (ν) P ≅ (ν) P'
                                                         
  | SC_Cong_Close : forall (P P' : proc n) (x : ch n),
      P ≅ P' -> x ! ․ P ≅ x ! ․ P'
                   
  | SC_Cong_Wait : forall (P P' : proc n) (x : ch n),
      P ≅ P' -> x ? ․ P ≅ x ? ․ P'
                  
  | SC_Cong_OutS : forall (P P' : proc n) (x y : ch n),
      P ≅ P' -> x ! y ․ P ≅ x ! y ․ P'
                  
  | SC_Cong_InsP : forall (P P' : proc n.+1) (x : ch n),
      P ≅ P' -> x ? (_)․P ≅ x ? (_)․P'
                  
  where   "P '≅' Q" := (struct_eq P Q).
  
  Reserved Notation " P '⇛' Q " (at level 50, left associativity).  
(* StartRed *)
  Inductive reduce {n:nat} : proc n -> proc n -> Prop :=
  | R_Res : forall P Q : proc n.+2, P ⇛ Q -> (ν) P ⇛ (ν) Q
  | R_Par : forall P Q R : proc n, P ⇛ Q -> P ∥ R ⇛ Q ∥ R
  | R_Struct : forall P P' Q Q' : proc n,
      P ≅ P' -> P' ⇛ Q' -> Q' ≅ Q -> P ⇛ Q
  | R_Close : forall P Q : proc n.+2,
      (ν) (one ! ․ P ∥ zero ? ․ Q) ⇛ ((ν) (P ∥ Q))
  | R_Com : forall (x : ch n.+2)(P : proc n.+2) (Q : proc n.+3),
      (ν) (one ! x ․ P ∥ zero ? (_)․Q) ⇛
        (ν) (P ∥ (<scons x id_ren> Q)) 
(* EndRed *)            
  where " P '⇛' Q " := (reduce P Q).

