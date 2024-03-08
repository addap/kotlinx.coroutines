From iris.algebra Require Import cmra list.
From iris.staging.algebra Require Import list.

(* list_op is now in iris_staging *)
Lemma replicate_op {A: ucmra} (a b: A) n:
  replicate n (a ⋅ b) = replicate n a ⋅ replicate n b.
Proof. apply list_eq. induction n; simpl. done. case; done. Qed.

Lemma included_None {A: cmra} (a : option A):
  (a ≼ None) -> a = None.
Proof.
  rewrite option_included. case; first done.
  intros (? & ? & _ & HContra & _). discriminate.
Qed.

Lemma None_least (A: cmra) (a: option A): None ≼ a.
Proof. by apply option_included; left. Qed.

Theorem prod_included':
  forall (A B: cmra) (x y: (A * B)), x.1 ≼ y.1 ∧ x.2 ≼ y.2 -> x ≼ y.
Proof.
    by intros; apply prod_included.
Qed.

Lemma None_op_left_id {A: cmra} (a: option A): None ⋅ a = a.
Proof. rewrite /op /cmra_op /=. by destruct a. Qed.

Theorem prod_included'':
  forall (A B: cmra) (x y: (A * B)), x ≼ y -> x.1 ≼ y.1 ∧ x.2 ≼ y.2.
Proof.
    by intros; apply prod_included.
Qed.

Theorem prod_included''':
  forall (A B: cmra) (x x' : A) (y y': B), (x, y) ≼ (x', y') -> x ≼ x' ∧ y ≼ y'.
Proof.
  intros ? ? ? ? ? ? HEv.
  apply prod_included'' in HEv.
  by simpl in *.
Qed.


Lemma list_validN_app {A: ucmra} (x y : list A) (n: nat):
  ✓{n} (x ++ y) <-> ✓{n} x ∧ ✓{n} y.
Proof. apply Forall_app. Qed.
