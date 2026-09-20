From SyntheticComputability Require Import EPF partial equiv_on Definitions reductions embed_nat.
From Stdlib Require Import Lia.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Program.Equality.

Import EmbedNatNotations.

From Stdlib Require Import List.
Import ListNotations.

From FOL.Incompleteness Require Import qdec sigma1.
From NumberRealizability Require Import Core Facts RealizingEnvTerms BoundedTactics Soundness RealizingArithmetic.

(** * Σ₁-properties *)

Section Sigma1.
  Variable Part : partiality.
  Variable θ : nat -> nat ↛ nat.
  Variable epf : EPF_nonparam_for θ.
  Variable epf_param : EPF_for θ.
  Local Notation "c ⊩[ α ] φ" :=
    (realizes (Part := Part) θ α c φ)
    (at level 70, format "c  ⊩[ α ]  φ").
  Local Notation "c ⊩ φ" :=
    (realizes (Part := Part) θ (fun _ => 0) c φ)
    (at level 70).
  Local Notation "c ⊩ctx[ α ] Γ" :=
    (realizes_ctx (Part := Part) θ α c Γ)
    (at level 70, format "c  ⊩ctx[ α ]  Γ").
  Local Notation "c ⊩ctx Γ" :=
    (realizes_ctx (Part := Part) θ (fun _ => 0) c Γ)
    (at level 70).
  Local Notation "code ⊩env[ n ] α" :=
    (realizes_env n code α)
    (at level 70, format "code  ⊩env[ n ]  α").

  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

(** ** Realizable Σ₁-formulas are True *)

Lemma real_sig1_true (φ : form) (α : env nat) (n code_α : nat)
  (Henv : code_α ⊩env[n] α):
  Σ1 φ -> bounded n φ -> forall c, c ⊩[α] φ -> sat interp_nat α φ.
Proof.
  intros Hsig. 
  induction Hsig in Henv, code_α, n, α |-*.
  - simpl. intros Hbd c (x & y & Hy & Hp).
    solve_bounded. exists x. 
    eapply IHHsig; try eassumption. 
    eapply realizes_env_S; eassumption.
  - intros Hbd c Hc. 
    assert (forall k : nat, bounded_t 0 ((fun x : nat => num (α x)) k)) as Hnum.
    {
      intros k. eapply num_bound.
    }
    destruct (H intu (fun x => num (α x)) Hnum) as [Hφ | Hnφ].
    + apply soundness in Hφ.
      assert (forall ψ, In ψ Qeq -> sat interp_nat α ψ) as Qmod.
      { apply nat_is_Q_model. } 
      specialize (Hφ nat interp_nat α Qmod).
      eapply sat_subst. 2: eassumption.
      cbn. intros x. 
      rewrite nat_eval_num.
      reflexivity.
    + eapply (realizes_sound_ND (Part := Part) (θ := θ) epf epf_param (n := n)) in Hnφ.
      2 : { 
            solve_bounded. 
            eapply subst_bounded_max.
            2 : eassumption.
            intros. eapply num_bound.
            eapply bounded_falsity.
            eapply bounded_up_L. 
            eapply bounded_Qeq. lia. 
            } 
      destruct (encode_Qeq epf epf_param α) as [code_Γ Hctx].
      destruct Hnφ as [? Hφ].
      destruct (Hφ α code_α Henv code_Γ Hctx) as (u & ? & Hreal).
      enough (u ⊩[α] ¬ α0) as Hnφ.
      destruct (Hnφ c Hc) as (? & ? & contra).
      inversion contra.
      change (u ⊩[α] (¬ α0) [fun x : nat => num (α x)]) in Hreal.
      apply realizes_subst in Hreal.
      eapply realizes_ext_iff; try eassumption.
      intros. simpl.
      rewrite eval_num. reflexivity.
Qed.


Lemma real_closed_sig1_true (φ : form) : 
  Σ1 φ -> bounded 0 φ -> forall c, c ⊩ φ -> sat interp_nat (fun _ => 0) φ.
Proof.
  intros Hsig1 Hbd c Hc.
  eapply real_sig1_true; try eassumption.
  eapply zero_realizes_triv_env.
Qed.

(** ** Σ₁-completeness for Realizable Formulas *)

Theorem real_Σ1_completeness (φ : form) : Σ1 φ -> bounded 0 φ -> forall c, c ⊩ φ -> Qeq ⊢I φ.
Proof.
  intros Hsig Hbd c Hreal.
  apply Σ1_completeness; try assumption.
  apply real_closed_sig1_true in Hreal; try assumption.
  intros α. apply sat_closed_env_gen with (α := α) in Hreal; assumption.
Qed.

(** ** Σ₁-witness *)

Lemma real_Σ1_witness (φ : form) : Σ1 φ -> bounded 1 φ -> Qeq ⊢I ∃φ -> exists x, Qeq ⊢I φ[(num x)..].
Proof.
  intros Hsig Hbd Hprv.
  apply (realizes_sound_ND (Part := Part) (θ := θ) epf epf_param (n := 0))  in Hprv.
  destruct Hprv as [c Hprv].
  destruct (encode_Qeq epf epf_param (fun _ => 0)) as [cΓ HΓ].
  unshelve edestruct Hprv as (e & Hval & Hreal).
  exact (fun _ => 0). exact 0.
  exact cΓ. 
  apply zero_realizes_triv_env.
  assumption.
  2 : { solve_bounded. constructor. apply Hbd. apply bounded_Qeq. }
  destruct Hreal as (n & r & Hr & _).
  assert (H : r ⊩ φ[(num n)..]). apply real_num_subst; assumption.
  assert (Hbdn : bounded 0 φ [(num n)..]). apply bounded_subst_num; assumption.
  assert (Hsign : Σ1 (φ [(num n)..])). apply Σ1_subst; assumption.
  exists n.  
  eapply real_Σ1_completeness; try eassumption.
Qed.


End Sigma1.
