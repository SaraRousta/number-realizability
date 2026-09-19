From SyntheticComputability Require Import Definitions.

Lemma ex_P_and_False (A : Type) (P : A -> Prop) :
  (exists x, P x /\ False) <-> False.
Proof.
  split; intros []. destruct H; assumption.
Qed.

Lemma ex_all_equiv (A : Type) (P : A -> Prop):
  (forall x, ~P(x)) <-> ~ exists x, P(x).
Proof.
  split; intros H.
  - intros [x Hx]. apply (H x). assumption.
  - intros x Hx. apply H. exists x. assumption.
Qed.

Definition DNE := forall (P : Prop), ~~ P -> P.

Definition MP_bool := 
  forall (f : nat -> bool), 
    (~~ exists n, f n = true) -> exists n, f n = true.

Definition MP_Prop := 
  forall (P : nat -> Prop), 
    (decidable P) -> 
      (~~ exists n : nat, P n) -> exists n : nat, P n.


Lemma quant_dist_all_ex {X : Type} (P : X -> Prop) (Q : Prop) : 
  (forall x, (P x -> Q)) <-> ((exists x, P x) -> Q).
Proof.
  split.
  intros ? [].
  eapply H; eassumption.
  intros. apply H.
  exists x. assumption.
Qed.

Definition AC_nat :=  forall R : nat -> nat -> Prop, (forall x, exists y, R x y) -> exists f : nat -> nat, forall x, R x (f x).

Lemma iff_neg (P Q : Prop) : (P <-> Q) -> (~P <-> ~Q).
Proof.
  intros H. intuition.
Qed.

Lemma false_not_true (f : nat -> bool) (n : nat) : f n = false -> ~(f n = true).
Proof.
  intuition. congruence.
Qed.
