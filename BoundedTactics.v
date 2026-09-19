From SyntheticComputability Require Import EPF partial equiv_on Definitions reductions embed_nat.
From Stdlib Require Import Lia Arith Vector.
From Equations Require Import Equations.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Program.Equality.

Import EmbedNatNotations.
Import VectorNotations.

From Stdlib Require Import List.
Import ListNotations.

From NumberRealizability Require Import Core Facts.


Section BoundedFacts.


Lemma bounded_L_cons {f : falsity_flag} n (φ : form) (Γ : list form) :
  bounded_L n (φ :: Γ) <-> bounded n φ /\ bounded_L n Γ.
Proof.
  unfold bounded_L.
  firstorder. subst. auto.
Qed.

Lemma bounded_L_map {f : falsity_flag} n m g Γ :
  (forall φ, bounded n φ -> bounded m (g φ)) ->
  bounded_L n Γ -> bounded_L m (map g Γ).
Proof.
  intros. induction Γ; cbn.
  - firstorder.
  - intros ? [<- | ?]; firstorder.
Qed.

Lemma bounded_up_L {f : falsity_flag} n k (Γ : list form) :
  bounded_L n Γ -> k >= n -> bounded_L k Γ.
Proof.
  unfold bounded_L. eauto using bounded_up.
Qed.

Lemma bounded_nil {f : falsity_flag} : forall n, @bounded_L _ _ _ f n List.nil.
Proof.
  intros _ _ [].
Qed. 

Lemma bounded_subst_num {f : falsity_flag} (φ : form) n : 
  bounded 1 φ -> bounded 0 (φ [(num n)..]).
Proof.
  apply subst_bounded_max with (n := 1); try assumption.
  intros [] ?. apply num_bound.
  enough (~ forall n, S n < 1).
  all : lia.
Qed.

End BoundedFacts.


Ltac decompose_bounded :=
  match goal with
  | H : bounded_L _ (_ :: _) |- _ => apply bounded_L_cons in H as []
  | H : bounded _ (atom _) |- _ => depelim H
  | H : bounded _ (bin _ _ _) |- _ => depelim H
  | H : bounded _ (quant _ _) |- _ => depelim H
  end.


Ltac prove_bounded :=
  match goal with
  | |- bounded_L _ (_ :: _) => apply bounded_L_cons ; split
  | |- bounded_L _ List.nil => apply bounded_nil
  | |- _ => assumption
  | |- bounded _ (atom _) => econstructor
  | |- bounded _ (bin _ _ _) => econstructor
  | |- bounded _ (subst_form _ _) => eapply subst_bounded_max; [ | eassumption];
                                   intros [] ?; cbn;
                                   [ 
                                     eapply bounded_up_t; [ eassumption | lia]
                                   | econstructor; lia]
  | |- bounded_L _ (map _ _) =>  
      eapply bounded_L_map;  [ | eassumption ];
      intros; eapply subst_bounded_max; [ | eassumption]; econstructor; lia
  | H : bounded _ ?φ |- bounded _ ?φ => eapply bounded_up; [ eassumption | lia]
  | H : bounded_t _ ?t |- bounded_t _ ?t => eapply bounded_up_t; [ eassumption | lia]
  | H : bounded_L _ ?Γ |- bounded_L _ ?Γ => eapply bounded_up_L; [ eassumption | lia]
  end.

Ltac solve_bounded :=
  repeat decompose_bounded ;
  repeat prove_bounded.

Ltac solve_form_closed :=
  repeat match goal with
  | H : _ = _ |- _ => rewrite <- H
  | |- bounded _ _ => constructor
  end.

Ltac solve_term_closed := 
  repeat match goal with 
  | H : _ = _ |- _ => rewrite H
  | |- bounded_t _ _ => constructor
  | |- forall _, _ -> _ => intros
  | H : Vector.In _ _ |- _ => depelim H
  | H : _ \/ _ |- _ => destruct H
  | |- _ > _ => lia
  end.

Ltac solve_bounded_closed := 
  solve_form_closed ;
  solve_term_closed.

