From SyntheticComputability Require Import EPF partial equiv_on Definitions reductions embed_nat.
From FOL Require Import FullSyntax Arithmetics.

Import EmbedNatNotations.

From Stdlib Require Import List.
Import ListNotations.

From FOL.Incompleteness Require Import qdec sigma1.
From NumberRealizability Require Import LogicalFacts Core Facts RealizingEnvTerms BoundedTactics Soundness RealizingArithmetic RealizingMP Sigma1Realizability.

(** * Markov's Principle for Q-Representable Predicates *)

Section QreprMP.
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

(** ** Q-representability and MP_Q *)

Definition Q_repr (P : nat -> Prop) := exists φ, bounded 1 φ /\ Σ1 φ /\ forall x, P x <-> Qeq ⊢I φ[(num x)..].

Definition MP_Q (P : nat -> Prop) := Q_repr P -> decidable P -> (~~ exists n, P n) -> exists n, P n.

(** ** Realizability of MP_HA forces MP_Q *)

Lemma Pdec_imp_Fdec (P : nat -> Prop) : 
  AC_nat -> 
  decidable P ->
  forall φ, bounded 1 φ ->  Σ1 φ -> (forall n, P n <-> Qeq ⊢I φ[(num n)..]) ->
  exists c, c ⊩ ∀ (φ ∨ (¬ φ)).
Proof.
  intros ac dec φ Hbd Hsig Hrep.
  destruct dec as [f Hdec].
  assert (forall n : nat, Qeq ⊢I φ [(num n)..] <-> exists e, e ⊩ φ[(num n)..]).
  {
    intros n. split.
    - intros Hprv. apply (realizes_sound_ND (Part := Part) (θ := θ) epf epf_param (n := 0)) in Hprv.
      + destruct Hprv as [code_φ Hprv].
        destruct (encode_Qeq epf epf_param (fun _ => 0)) as [cqeq Hqeq].
        unshelve edestruct Hprv as (e & Hval & Hreal).
        exact (fun _ => 0). exact 0.
        exact cqeq. 
        apply zero_realizes_triv_env.
        assumption.
        exists e; assumption.
      + solve_bounded.
        apply bounded_subst_num; assumption.
        apply bounded_Qeq.
    - intros [e Hreal]. eapply real_Σ1_completeness; try eassumption.
      apply Σ1_subst; assumption.
      apply bounded_subst_num; assumption.
  }
  unfold decider in Hdec. unfold reflects in Hdec.
  assert (Hf : forall n, f n = true <-> exists e : nat, e ⊩ φ [(num n)..]).
  {
    intros n. rewrite <- (Hdec n). rewrite (Hrep n). apply H.  
  }
  assert (HR : forall n, exists e, e ⊩ (φ [(num n)..]) ∨ (¬ φ [(num n)..])).
  {
    intros n. destruct (f n) eqn: Heq.
    - apply Hf in Heq. destruct Heq as [e He].
    exists ⟨0, e⟩. simpl. left. exists e. split; [reflexivity | assumption].
    - assert (Hneg : ~ exists e, e ⊩ φ [(num n)..]).
      {
        apply false_not_true in Heq. specialize (Hf n). 
        apply iff_neg in Hf. apply Hf in Heq. apply Heq. 
      }
      exists ⟨1, 0⟩. right. exists 0.
      split; try reflexivity.
      apply realizes_neg_iff. assumption.
  }
  apply ac in HR.
  destruct HR as [g Hg].
  destruct (epf (fun n => ret (g n))) as [c Hc].
  exists c. simpl.
  intros n.
  destruct (Hg n) as [Hφ | Hnφ].
  - destruct Hφ as (e & Hgeq & Hreal).
    exists ⟨0, e⟩. split. 
    apply Hc. rewrite Hgeq. apply ret_hasvalue.
    left. exists e. split; try reflexivity.
    apply <- real_num_subst in Hreal.
    exact Hreal.
  - destruct Hnφ as (e & Hgeq & Hreal).
    exists ⟨1, e⟩. split. 
    apply Hc. rewrite Hgeq. apply ret_hasvalue.
    right. exists e. split; try reflexivity.
    intros m Hm.
    apply (Hreal m).
    apply real_num_subst; assumption.
Qed.

Lemma nnP_imp_real_nnp (P : nat -> Prop) :
  forall φ, bounded 1 φ -> (forall n, P n <-> Qeq ⊢I φ[(num n)..]) ->
  (~~ exists n, P n) -> 0 ⊩ ¬¬∃φ.
Proof.
  intros φ Hbd Hrep HnnP.
  rewrite realizes_double_negation_iff.
  assert (H : forall n, P n -> exists e, e ⊩ ∃φ).
  {
    intros n Hpn.
    apply Hrep in Hpn.
    apply realizes_exists.
    exists n.  
    apply (realizes_sound_ND (Part := Part) (θ := θ) epf epf_param (n := 0)) in Hpn.
    + destruct Hpn as [code_φ Hprv].
      destruct (encode_Qeq epf epf_param (fun _ => 0)) as [cqeq Hqeq].
      unshelve edestruct Hprv as (e & Hval & Hreal).
      exact (fun _ => 0). exact 0.
      exact cqeq. 
      apply zero_realizes_triv_env.
      assumption.
      exists e.
      apply real_num_subst; assumption.   
    + solve_bounded.
      apply bounded_subst_num; assumption.
      apply bounded_Qeq.
  }
  rewrite quant_dist_all_ex in H.
  intuition.
Qed.

Theorem MP_PROP_HA_imp_MP_Q (P : nat -> Prop) : 
  AC_nat ->
  (forall φ, exists c, c ⊩ MP_Prop_HA φ) ->
  MP_Q P.
Proof.
  intros ac mp Hrep Hdec Hpn.
  destruct Hrep as (φ & Hbd & Hsig & Hrep).
  assert (He : exists e, e ⊩ ∀ (φ ∨ (¬ φ))). apply Pdec_imp_Fdec with (P := P); assumption.
  destruct He as [e He].
  assert (Hnp : 0 ⊩ ¬¬∃φ). apply nnP_imp_real_nnp with (P := P); assumption.
  destruct (mp φ) as [c Hc].
  specialize (Hc e He).
  assert (H : exists v, θ c e =! v /\ v ⊩ (¬ (¬ (∃ φ)) → (∃ φ))) by apply Hc.
  clear Hc.
  destruct H as (v & Hvalv & Hrealv).
  specialize (Hrealv 0 Hnp).
  assert (H : exists u, θ v 0 =! u /\ u ⊩ (∃ φ)) by apply Hrealv.
  clear Hrealv.
  destruct H as (u & Hvalu & Hrealu).
  destruct Hrealu as (n & r & Hr & _).
  assert (H : r ⊩ φ[(num n)..]). apply real_num_subst; assumption.
  assert (Hbdn : bounded 0 φ [(num n)..]). apply bounded_subst_num; assumption.
  assert (Hsign : Σ1 (φ [(num n)..])). apply Σ1_subst; assumption.
  exists n.  
  apply Hrep.  
  eapply real_Σ1_completeness; try eassumption.
Qed.

End QreprMP.
