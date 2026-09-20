From SyntheticComputability Require Import EPF partial equiv_on Definitions reductions embed_nat.
From Stdlib Require Import Vector.
From Equations Require Import Equations.
From FOL Require Import FullSyntax Arithmetics.

Import EmbedNatNotations.
Import VectorNotations.

From Stdlib Require Import List.
Import ListNotations.

(** * Definition of Number Realizability *)

Equations eval (α : env nat) (t : @term PA_funcs_signature) : nat :=
  eval α (var x) := α x ;
  eval α (func Zero _) := 0 ;
  eval α (func Succ ([t])%vector) := S (eval α t) ;
  eval α (func Plus ([t1 ; t2])%vector) := eval α t1 + eval α t2 ;
  eval α (func Mult ([t1 ; t2])%vector) := eval α t1 * eval α t2.

Section Realizability.
  Variable Part : partiality.
  Variable θ : nat -> nat ↛ nat.

    Fixpoint realizes {f : falsity_flag}
      (α : env nat) (c : nat) (φ : @form _ _ _ f) : Prop := 
    match φ with 
    | falsity => False
    | atom Eq (Vector.cons t1 (Vector.cons t2 Vector.nil)) => eval α t1 = eval α t2
    | bin Conj φ1 φ2 => exists c1 c2, realizes α c1 φ1 /\ realizes α c2 φ2 /\ c = ⟨c1, c2⟩ 
    | bin Disj φ1 φ2 => (exists c1, c = ⟨ 0, c1 ⟩ /\ realizes α c1 φ1) \/ (exists c2, c = ⟨ 1, c2 ⟩ /\ realizes α c2 φ2) 
    | bin Impl φ1 φ2 => forall c1, realizes α c1 φ1 -> exists v : nat, θ c c1 =! v /\ realizes α v φ2 
    | quant All φ => forall x : nat, exists v, θ c x =! v /\ realizes (scons x α) v φ 
    | quant Ex φ  => exists x y : nat, realizes (scons x α) y φ /\ c = ⟨ x, y ⟩
    | _ => False
    end. 

Fixpoint realizes_ctx {f : falsity_flag}
  (α : env nat) (c : nat) (Γ : list (@form _ _ _ f)) : Prop := 
  match Γ with 
  | [] => True 
  | φ :: Γ => exists c1 : nat, realizes α c1 φ /\ 
              exists c2 : nat, realizes_ctx α c2 Γ /\ 
              c = ⟨c1, c2⟩
  end.

End Realizability.
