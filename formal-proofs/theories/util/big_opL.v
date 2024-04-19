From iris.algebra Require Import cmra gset numbers big_op.
From iris.staging.algebra Require Import list.

Lemma big_opL_replicate_irrelevant_element
      (M: ofe) (o: M -> M -> M) (H': Monoid o)
      {A: Type} (P: nat -> A -> M) (a: A) n:
  ([^o list] i ↦ k ∈ replicate n a, P i k) =
  ([^o list] i ↦ _ ∈ replicate n a, P i a).
Proof.
  apply big_opL_gen_proper; try apply _.
  intros ? ?; rewrite lookup_replicate; case; by intros ->.
Qed.

Lemma big_opL_take_drop_middle (M: ofe) (o : M → M → M) (H': Monoid o) (A: Type)
      (f: nat → A → M) (l: list A) (id: nat) (x: A):
  l !! id = Some x →
  ([^o list] k ↦ y ∈ l, f k y) ≡
    (o ([^o list] k ↦ y ∈ take id l, f k y)
       (o (f id x) ([^o list] k ↦ y ∈ drop (S id) l, f (id + S k) y))).
Proof.
  intros HEl.
  erewrite <-(take_drop_middle l); last done.
  assert (id < length l)%nat by (eapply lookup_lt_Some; eassumption).
  rewrite big_opL_app take_app_alt.
  rewrite drop_app_ge.
  all: rewrite take_length_le //=; try lia.
  replace (S id - id)%nat with 1 by lia. simpl.
  by rewrite drop_0 Nat.add_0_r.
Qed.

Lemma big_opL_op_prodR r (A B : ucmra) (C : Type)
      (f : nat → C → A) (g : nat → C → B) (l : list C):
  ([^op list] k↦x ∈ l, ((f (r + k) x, g (r + k) x) : prodR A B)) ≡
  (([^op list] k↦x ∈ l, f (r + k) x), ([^op list] k↦x ∈ l, g (r + k) x)).
Proof.
  generalize dependent r.
  induction l as [|v l']=> //= r.
  setoid_rewrite <-plus_n_Sm.
  by rewrite Nat.add_0_r pair_op (IHl' (S r)).
Qed.

Lemma big_opL_op_ucmra_unit (A: ucmra) (C : Type) (l : list C):
  ([^op list] _ ∈ l, (ε: A)) ≡ ε.
Proof. induction l=>//=. rewrite IHl ucmra_unit_left_id //. Qed.

(* a.d. TODO I had to add this local hint for typeclass resolution to work.
   This was used in old iris, new iris uses (refine (ofe_equiv _)) which somehow fails. *)
Local Hint Extern 0 (Equiv _) => eapply (@ofe_equiv _) : typeclass_instances.
Lemma big_opL_op_gset n m:
  GSet (set_seq n m) ≡ [^op list] x ∈ seq n m, GSet {[x]}.
Proof.
  move: m n. elim=> //= m IHm n. rewrite -(IHm (S n)).
  rewrite -gset_op gset_disj_union //=.
  apply set_seq_S_start_disjoint.
Qed.

Global Instance max_monoid: Monoid max.
Proof.
  apply (Build_Monoid natO max 0)=> //; try apply _.
  - intros x y z. rewrite leibniz_equiv_iff. apply Max.max_assoc.
  - intros x y. rewrite leibniz_equiv_iff. apply Max.max_comm.
Defined.

Global Instance max_nat_homomorphism:
  MonoidHomomorphism max op equiv MaxNat.
Proof.
  econstructor; last done.
  econstructor; try apply _.
  intros. by rewrite max_nat_op.
Qed.

Lemma big_opL_op_max_nat {A: Type} (f: nat → A -> max_natR) (l: list A):
  MaxNat ([^max list] k ↦ x ∈ l, max_nat_car (f k x)) ≡
  ([^op list] k ↦ x ∈ l, f k x).
Proof.
  rewrite (big_opL_commute _). apply big_opL_proper. intros. by destruct (f _ _).
Qed.

Lemma big_opL_op_nat {A: Type} (f: nat → A -> natR) (l: list A):
  ([^Nat.add list] k ↦ x ∈ l, f k x) ≡
  ([^op list] k ↦ x ∈ l, f k x).
Proof. done. Qed.

Lemma big_opL_op_nat' {A: Type} (i: nat) (l: list A):
  length l * i ≡ ([^op list] k ↦ x ∈ l, i).
Proof. induction l=> //=. by rewrite IHl. Qed.
