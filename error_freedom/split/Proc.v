(** * Polarized process syntax

    Session channels are *names* [ch n]; an *endpoint* is a name
    together with a polarity, [pch n := ch n * pol].  The co-endpoint
    of [(x, ρ)] is [(x, flip ρ)] -- a total syntactic function, also
    on free channels.  This is what the double-binder representation
    ([Base.v]'s [ResP : proc n.+2 -> proc n]) cannot offer: there,
    the pairing of the two endpoints exists only at their binder, so
    communication must be located at the ν, and every semantic
    argument about a synchronization has to descend the term to find
    it.  With polarities, communication is a rule of parallel
    composition (see [LTS.v]) and the restriction stays inert.

    The receive prefix carries the polarity it expects,
    [PIns c ρ K] = "receive on [c] an endpoint of polarity [ρ]".
    Substitution transports *names* only; polarities are written at
    the occurrences and are untouched by renaming.  Without the
    annotation, receiving [(y, pos)] into a body that mentions
    [(zero, neg)] would silently grant access to the co-endpoint --
    the substitution disaster for subject reduction.

    Scope discipline is well-scoped de Bruijn as in [Base.v], but
    the restriction binds ONE name (both its polarities):
    [PRes : procP n.+1 -> procP n]. *)

From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
From Tait Require Import Base.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** Polarities *)
Inductive pol : Set := pos | neg.

Definition flipp (r : pol) : pol := if r is pos then neg else pos.

Lemma flipp_invol r : flipp (flipp r) = r.
Proof. by case: r. Qed.

Definition pol_eqb (a b : pol) : bool :=
  match a, b with pos, pos | neg, neg => true | _, _ => false end.

Lemma pol_eqP : Equality.axiom pol_eqb.
Proof. by case=> [] []; constructor. Qed.

(** Polarities form an eqType, hence so do endpoints [pch n = ch n * pol]:
    typing contexts are indexed by endpoints and must compare them. *)
HB.instance Definition _ := hasDecEq.Build pol pol_eqP.

Lemma pol_dec (a b : pol) : {a = b} + {a <> b}.
Proof. by decide equality. Qed.

(** ** Endpoints: name × polarity *)
Definition pch (n : nat) : Type := (ch n * pol)%type.

Definition pflip {n : nat} (c : pch n) : pch n := (c.1, flipp c.2).

(** Renamings act on the name and leave the polarity alone. *)
Definition pren {m n : nat} (s : ren m n) (c : pch m) : pch n :=
  (s c.1, c.2).

Lemma pren_id n (c : pch n) : pren id_ren c = c.
Proof. by case: c. Qed.

Lemma pren_comp m n p (s : ren m n) (t : ren n p) (c : pch m) :
  pren t (pren s c) = pren (fun z => t (s z)) c.
Proof. by case: c. Qed.

(** ** Processes *)
Inductive procP (n : nat) : Type :=
| PEnd   : procP n
| PWait  : pch n -> procP n -> procP n            (* c ?․ P   *)
| PClose : pch n -> procP n -> procP n            (* c !․ P   *)
| PRes   : procP n.+1 -> procP n                  (* (ν) P    *)
| PPar   : procP n -> procP n -> procP n          (* P ∥ Q    *)
| PIns   : pch n -> pol -> procP n.+1 -> procP n  (* c ?(ρ)․ P *)
| PDel   : pch n -> pch n -> procP n -> procP n   (* c ! d ․ P *)
| PSel   : pch n -> bool -> procP n -> procP n    (* c ◁ b ․ P *)
| PBra   : pch n -> procP n -> procP n -> procP n. (* c ▷ (P|Q) *)

Arguments PEnd {n}.

Declare Scope pol_scope.
Delimit Scope pol_scope with P.
Bind Scope pol_scope with procP.
Open Scope pol_scope.

Notation "∅" := PEnd : pol_scope.
Infix "∥" := PPar (at level 48, left associativity) : pol_scope.
Notation "(ν) P" := (PRes P) (at level 44, right associativity) : pol_scope.
Notation "c ?․ P" := (PWait c P) (at level 44, right associativity) : pol_scope.
Notation "c !․ P" := (PClose c P) (at level 44, right associativity) : pol_scope.
Notation "c ?( r )․ P" :=
  (PIns c r P) (at level 44, right associativity) : pol_scope.
Notation "c ◁ b ․ P" :=
  (PSel c b P) (at level 44, right associativity) : pol_scope.
Notation "c ▷ ( P | Q )" :=
  (PBra c P Q) (at level 44, right associativity) : pol_scope.
Notation "c ! d ․ P" :=
  (PDel c d P) (at level 44, right associativity) : pol_scope.

(** ** Renaming of processes *)
Fixpoint psubst {m n : nat} (s : ren m n) (P : procP m) : procP n :=
  match P with
  | PEnd => PEnd
  | PWait c K => PWait (pren s c) (psubst s K)
  | PClose c K => PClose (pren s c) (psubst s K)
  | PRes B => PRes (psubst (up_ch s) B)
  | PPar A B => PPar (psubst s A) (psubst s B)
  | PIns c r K => PIns (pren s c) r (psubst (up_ch s) K)
  | PDel c d K => PDel (pren s c) (pren s d) (psubst s K)
  | PSel c b K => PSel (pren s c) b (psubst s K)
  | PBra c K1 K2 => PBra (pren s c) (psubst s K1) (psubst s K2)
  end.

Notation "⟨ s ⟩ P" := (psubst s P) (at level 30) : pol_scope.

(** The three renaming laws, funext-free. *)
Lemma psubst_ext m n (s t : ren m n) (P : procP m) :
  (forall z, s z = t z) -> psubst s P = psubst t P.
Proof.
  elim: P n s t => //=
    [ m' c K IH | m' c K IH | m' B IH | m' A IHA B IHB
    | m' c r K IH | m' c d K IH | m' c b K IH
    | m' c K1 IH1 K2 IH2 ] n s t E.
  - by rewrite /pren E (IH _ _ _ E).
  - by rewrite /pren E (IH _ _ _ E).
  - congr PRes. apply: IH => -[z|] //=. by rewrite E.
  - by rewrite (IHA _ _ _ E) (IHB _ _ _ E).
  - rewrite /pren E. congr PIns. apply: IH => -[z|] //=. by rewrite E.
  - by rewrite /pren !E (IH _ _ _ E).
  - by rewrite /pren E (IH _ _ _ E).
  - by rewrite /pren E (IH1 _ _ _ E) (IH2 _ _ _ E).
Qed.

Lemma psubst_comp m n p (s : ren m n) (t : ren n p) (P : procP m) :
  psubst t (psubst s P) = psubst (fun z => t (s z)) P.
Proof.
  elim: P n p s t => //=
    [ m' c K IH | m' c K IH | m' B IH | m' A IHA B IHB
    | m' c r K IH | m' c d K IH | m' c b K IH
    | m' c K1 IH1 K2 IH2 ] n p s t.
  - by rewrite pren_comp IH.
  - by rewrite pren_comp IH.
  - congr PRes. rewrite IH. by apply: psubst_ext => -[z|].
  - by rewrite IHA IHB.
  - rewrite pren_comp. congr PIns. rewrite IH.
    by apply: psubst_ext => -[z|].
  - by rewrite !pren_comp IH.
  - by rewrite pren_comp IH.
  - by rewrite pren_comp IH1 IH2.
Qed.

Lemma psubst_id n (P : procP n) : psubst id_ren P = P.
Proof.
  elim: P => //=
    [ n' c K IH | n' c K IH | n' B IH | n' A IHA B IHB
    | n' c r K IH | n' c d K IH | n' c b K IH
    | n' c K1 IH1 K2 IH2 ].
  - by rewrite pren_id IH.
  - by rewrite pren_id IH.
  - congr PRes. rewrite -[in RHS]IH. by apply: psubst_ext => -[z|].
  - by rewrite IHA IHB.
  - rewrite pren_id. congr PIns. rewrite -[in RHS]IH.
    by apply: psubst_ext => -[z|].
  - by rewrite !pren_id IH.
  - by rewrite pren_id IH.
  - by rewrite pren_id IH1 IH2.
Qed.

(** ** Swap of the top two names is an involution *)

Lemma swap01_invol n (z : ch n.+2) :
  swap_ch zero one (swap_ch zero one z) = z.
Proof. by case: z => [[z|]|]. Qed.

Lemma psubst_swap01_invol n (P : procP n.+2) :
  psubst (swap_ch zero one) (psubst (swap_ch zero one) P) = P.
Proof.
  rewrite psubst_comp -[RHS]psubst_id.
  apply: psubst_ext => z. exact: swap01_invol.
Qed.
