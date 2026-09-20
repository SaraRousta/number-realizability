From SyntheticComputability Require Import EPF partial equiv_on Definitions reductions embed_nat.
From Stdlib Require Import Arith Vector.
From Equations Require Import Equations.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Program.Equality.

Import EmbedNatNotations.

From Stdlib Require Import List.
Import ListNotations.

From NumberRealizability Require Import LogicalFacts Core Facts RealizingEnvTerms BoundedTactics.

(** * Almost-Negative Formulas *)

Section AlmostNegative.
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

(** ** Definition of Almost Negative Formulas *)

Inductive almost_negative : form -> Prop := 
| an_bot : almost_negative ⊥
| an_atomic (P : preds) (v : t term (ar_preds P)) : almost_negative (atom P v)
| an_ex (P : preds) (v : t term (ar_preds P)) : almost_negative (∃ (atom P v))
| an_conj (φ ψ : form) : almost_negative φ -> almost_negative ψ -> almost_negative  (bin Conj φ ψ)
| an_impl (φ ψ : form) : almost_negative φ -> almost_negative ψ -> almost_negative  (bin Impl φ ψ)
| an_all (φ : form) : almost_negative φ -> almost_negative (∀ φ).

(** ** Self-realizability *)

Proposition realizable_anforms_true (φ : form) (Han : almost_negative φ) (n : nat) (Hbd : bounded n φ) : 
  forall (α : env nat) code_α, code_α ⊩env[n] α ->
  (exists e, exists v, θ e code_α =! v /\ v ⊩[α] φ) -> sat interp_nat α φ

  with true_anforms_realizable (φ : form) (Han : almost_negative φ) (n : nat) (Hbd : bounded n φ): 
    exists e, forall (α : env nat) (code_α : nat), code_α ⊩env[n] α ->
    sat interp_nat α φ -> exists v, θ e code_α =! v /\ v ⊩[α] φ.
Proof.
  {
    induction Han in Hbd, n|-*.
    - setoid_rewrite ex_P_and_False. 
      intros ? ? ? []. assumption.
    - destruct P. repeat depelim v. simpl.
      intros α code Hcode (e & u & Hvalu & Hrealu).
      repeat rewrite <- eval_real_stdmodel.
      assumption.
    - destruct P. repeat depelim v. 
      simpl. solve_bounded.
      intros α code Hcode (? & ? & ? & x & ? & H & ?).
      exists x. 
      repeat rewrite <- eval_real_stdmodel.
      assumption. 
    - simpl; intros α code Hcode [e H].
      solve_bounded. split. 
      + eapply IHHan1; try eassumption. 
        destruct (epf (fun c => bind (θ e c) (fun! ⟨x, y⟩ => ret x))) as [r Hr].
        exists r. 
        destruct H as (v & Hv & c1 & c2 & Hc1 & Hc2 & Hp).
        exists c1. split; try assumption.
        apply Hr. apply bind_hasvalue. exists v. split; try assumption.
        rewrite Hp. rewrite embedP. apply ret_hasvalue.
      + eapply IHHan2; try eassumption.
        destruct (epf (fun c => bind (θ e c) (fun! ⟨x, y⟩ => ret y))) as [r Hr].
        exists r. 
        destruct H as (v & Hv & c1 & c2 & Hc1 & Hc2 & Hp).
        exists c2. split; try assumption.
        apply Hr. apply bind_hasvalue. exists v. split; try assumption.
        rewrite Hp. rewrite embedP. apply ret_hasvalue.
    - simpl. intros α code Hcode (e & H) Hφ. solve_bounded.
      destruct (true_anforms_realizable φ Han1 n Hbd1) as [c Hc].
      eapply IHHan2; try eassumption.
      destruct (epf (fun code => bind (θ e code) (fun v => bind (θ c code) (fun u => θ v u)))) as [r Hr].
      exists r. 
      destruct (Hc α code Hcode Hφ) as (v & Hvalv & Hrealv).
      destruct H as (u & Hvalu & H).
      destruct (H v Hrealv) as (w & Hvalw & Hrealw).
      exists w. split; try assumption.
      apply Hr. apply bind_hasvalue.
      exists u. split; try assumption.
      apply bind_hasvalue. exists v. split; try assumption. 
    - simpl. intros α code Hcode (e & H) x. 
      solve_bounded.
      eapply IHHan; try eassumption. eapply realizes_env_S; try eassumption.
      destruct (epf (fun! ⟨x, code⟩ => bind (θ e code) (fun v => θ v x))) as [r Hr].
      exists r. 
      destruct H as (v & Hvalv & Hv).
      destruct (Hv x) as (u & Hvalu & Hrealu).
      exists u. split; try assumption.
      apply Hr. rewrite embedP.
      apply bind_hasvalue. exists v. split; try assumption.
  }
  {
    induction Han in Hbd, n |-*.
    - exists 0. intros ? ? ? contra. destruct contra. 
    - destruct P. repeat depelim v. simpl.
      destruct (epf (fun v => ret 0)) as [r Hr].
      exists r. intros. 
      exists 0. split.
      apply Hr. apply ret_hasvalue.
      repeat rewrite eval_real_stdmodel.
      assumption.
    - destruct P. repeat depelim v. 
      simpl. solve_bounded. 
      destruct (epf (fun code => 
        bind (mu (fun x => ret (
        Nat.eqb (eval (x .: fun m => nth m (decode_env_to_list code n) 0) h) (eval (x .: fun m => nth m (decode_env_to_list code n) 0) h0)))) (fun n => ret ⟨n, 0⟩))) as [r Hr].
      exists r. intros α code Hcode [x Heq].
      repeat rewrite <- eval_real_stdmodel in Heq.
      assert (Hter : exists v, mu (fun x => ret (
        Nat.eqb (eval (x .: fun m => nth m (decode_env_to_list code n) 0) h) (eval (x .: fun m => nth m (decode_env_to_list code n) 0) h0))) =! v).
      {
      apply mu_ter.
      exists x.
      split.
      + erewrite <- eval_env_proj_S; try eassumption.
        erewrite <- eval_env_proj_S; try eassumption.
        rewrite <- Nat.eqb_eq in Heq.
        rewrite Heq. 
        apply ret_hasvalue.
      + intros y Hyx.
        erewrite <- eval_env_proj_S; try eassumption.
        erewrite <- eval_env_proj_S; try eassumption.
        destruct (Nat.eq_dec (eval (y .: α) h) (eval (y .: α) h0)) as [H | H].
        * exists true.  
          rewrite <- Nat.eqb_eq in H.
          rewrite H.
          apply ret_hasvalue.
        * exists false.
          rewrite <- Nat.eqb_eq in H.
          rewrite Bool.not_true_iff_false in H.
          rewrite H.
          apply ret_hasvalue.
      }
      destruct Hter as [v Hvalv].
      exists ⟨v, 0⟩.
      split. apply Hr.
      apply bind_hasvalue.
      exists v. split; try assumption. apply ret_hasvalue.
      exists v. exists 0. split; try reflexivity.
      apply mu_hasvalue in Hvalv.
      destruct Hvalv as [Hvalv _].
      erewrite <- eval_env_proj_S in Hvalv; try eassumption.
      erewrite <- eval_env_proj_S in Hvalv; try eassumption.
      rewrite <- Nat.eqb_eq.
      apply ret_hasvalue_inv.
      assumption.
    - solve_bounded. simpl.
      destruct (IHHan1 n Hbd1) as (c1 & Hc1).
      destruct (IHHan2 n Hbd2) as (c2 & Hc2).
      destruct (epf (fun code => 
        bind (θ c1 code) (fun v => bind (θ c2 code) (fun u => ret ⟨v, u⟩)))) as [r Hr].
      exists r. intros α code Hcode [Hφ Hψ].
      destruct (Hc1 α code Hcode Hφ) as (v & Hvalv & Hrealv).
      destruct (Hc2 α code Hcode Hψ) as (u & Hvalu & Hrealu).
      exists ⟨v, u⟩. split. 
      apply Hr. apply bind_hasvalue. exists v. split; try assumption.
      apply bind_hasvalue. exists u. split; try assumption. apply ret_hasvalue.
      exists v. exists u. intuition.
    - simpl. solve_bounded. destruct (IHHan2 n Hbd2) as [e He].
      destruct (epf_param (fun code => fun _ => θ e code)) as [γ Hγ].
      destruct (epf (fun code => ret (γ code))) as [r Hr].
      exists r. intros α code Hcode Himp.
      exists (γ code). split.
      apply Hr. apply ret_hasvalue.
      intros c Hc.
      enough (exists e v, θ e code =! v /\ v ⊩[α] φ) as H.
      + specialize (realizable_anforms_true φ Han1 n Hbd1 α code Hcode H).
        apply Himp in realizable_anforms_true.
        destruct (He α code Hcode realizable_anforms_true) as (v & Hvalv & Hrealv).
        exists v. split; try assumption.
        apply Hγ; assumption.
      + destruct (epf (fun _=> ret c)) as [d Hd].
        exists d. intros. exists c. split; try assumption.
       apply Hd. apply ret_hasvalue.
    - simpl. solve_bounded.
      destruct (IHHan (S n) Hbd) as [e He].
      destruct (epf_param (fun code => fun x => (θ e ⟨x, code⟩))) as [γ Hγ].
      destruct (epf (fun code => ret (γ code))) as [r Hr].
      exists r. intros α code Hcode H.
      exists (γ code). split. apply Hr; apply ret_hasvalue.
      intros x. assert (Henv : ⟨x, code⟩ ⊩env[S n] (x .: α)).
      { eapply realizes_env_S; assumption.  }
      destruct (He (x .: α) ⟨x, code⟩ Henv (H x)) as (v & Hvalv & Hrealv).
      exists v. split.
      apply Hγ. all : assumption.    
  }
Qed.

Corollary self_realizing_forms (φ : form) :
  almost_negative φ ->
  bounded 0 φ -> 
  (exists c, c ⊩ φ) <-> sat interp_nat (fun _ => 0) φ.
Proof.
  intros Han Hbd. 
  pose (zero_realizes_triv_env) as Henv.
  split.
  - intros [c Hc].
    eapply realizable_anforms_true; try eassumption.
    destruct (epf (fun _ => ret c)) as [e He].
    exists e. exists c. split; try assumption.
    apply He. apply ret_hasvalue.
  - intros H. destruct ( @true_anforms_realizable φ Han 0 Hbd) as [e He].
    destruct (He (fun _ => 0) 0 Henv H) as (c & _ & Hc).
    exists c. assumption.
Qed. 


End AlmostNegative.
