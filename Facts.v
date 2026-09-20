From SyntheticComputability Require Import EPF partial equiv_on Definitions reductions embed_nat.
From Stdlib Require Import Vector.
From Equations Require Import Equations.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Program.Equality.

Import EmbedNatNotations.

From Stdlib Require Import List.
Import ListNotations.

From NumberRealizability Require Import LogicalFacts Core.

(** * Facts about Number Realizability *)

(** ** Evaluation: Substitution and Extensionality *)

Section Eval.

Lemma eval_subst (α : env nat) (t : term) (ρ : nat -> term) :
  eval α t`[ρ] = eval (fun x : nat => eval α (ρ x)) t.
Proof.
  induction t.
  - simp eval. reflexivity.
  - destruct F.
    + simp eval. tauto.
    + simpl in *. repeat depelim v. simpl. simp eval.
      f_equal. apply IH. apply In_cons_hd.
    + simpl in *. depelim v. depelim v. depelim v.
      simp eval. simpl. simp eval. repeat rewrite IH.
      reflexivity.
      apply In_cons_tl. apply In_cons_hd.
      apply In_cons_hd.
    + simpl in *. depelim v. depelim v. depelim v.
      simp eval. simpl. simp eval. repeat rewrite IH.
      reflexivity.
      apply In_cons_tl. apply In_cons_hd.
      apply In_cons_hd.
Qed.

Lemma eval_term_ext (α α' : env nat) :
  forall t : term, (forall x : nat, α x = α' x) -> eval α t = eval α' t.
Proof.
  induction t.
  - simp eval.
  - intros Hext. induction F.
    + reflexivity.
    + repeat depelim v. simp eval. f_equal.
      apply IH; [apply In_cons_hd | apply Hext].
    + repeat depelim v. simp eval. repeat rewrite IH.
      reflexivity.
      apply In_cons_tl. apply In_cons_hd. apply Hext.
      apply In_cons_hd. apply Hext.
    + repeat depelim v. simp eval. repeat rewrite IH.
      reflexivity.
      apply In_cons_tl. apply In_cons_hd. apply Hext.
      apply In_cons_hd. apply Hext.
Qed.

Lemma eval_real_stdmodel (t : term) (α : env nat) :
  eval α t = @FullCore.eval _ _ _ interp_nat α t.
Proof.
  induction t.
  - reflexivity.
  - destruct F.
    + reflexivity.
    + repeat depelim v. simpl. simp eval.
      erewrite IH. reflexivity.
      apply In_cons_hd.
    + repeat depelim v. simpl. simp eval.
      erewrite (IH h). erewrite (IH h0). reflexivity.
      apply In_cons_tl. apply In_cons_hd.
      apply In_cons_hd.
    + repeat depelim v. simpl. simp eval.
      erewrite (IH h). erewrite (IH h0). reflexivity.
      apply In_cons_tl. apply In_cons_hd.
      apply In_cons_hd.
Qed.

Lemma eval_num (α : env nat) (n : nat) : eval α (num n) = n.
Proof.
  induction n as [| n IH]; cbn; simp eval; auto.
Qed.

End Eval.

Section NumberRealizability.

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

(** ** Realizability: Substitution and Extensionality *)

Section Real.

Lemma realizes_ext {f : falsity_flag} α α' c (φ : form) :
  (forall x, α x = α' x) -> (c ⊩[α] φ -> c ⊩[α'] φ).
Proof.
  induction φ in c, α, α' |-*. 
  - intros Hext. simpl. tauto.
  - induction P. 
    repeat depelim t. rename h into t1, h0 into t2.
    intros Hext. simpl. 
    pose proof (eval_term_ext t1 Hext).
    pose proof (eval_term_ext t2 Hext).
    firstorder; congruence.
  - destruct b0.
    + intros Hext. simpl. 
      intros (c1 & c2 & Hc1 & Hc2 & Heq).
      exists c1. exists c2. split. 
      apply (IHφ1 α α' c1 Hext). apply Hc1. split.
      apply (IHφ2 α α' c2 Hext). apply Hc2. apply Heq. 
    + intros Hext. 
      intros [(c1 & Heq & Hc1) | (c1 & Heq & Hc1)].
          * left. exists c1. split.
            apply Heq.
            apply (IHφ1 α  α' c1 Hext).
            apply Hc1.
          * right. exists c1. split.
            apply Heq.
            apply (IHφ2 α  α' c1 Hext).
            apply Hc1.
    + intros Hext. 
      intros H c1 Hc1.
      simpl in H.
      destruct (H c1) as (v & Hvalv & Hrealv).
      eapply (IHφ1 α' α); try assumption.
      intros x; symmetry; apply Hext.
      exists v. split.
      apply Hvalv.
      apply (IHφ2 α  α' v Hext). apply Hrealv.
  - destruct q.
    + intros Hext. 
      intros H c1.
      simpl in H.
      destruct (H c1) as (v & Hvalv & Hrealv).
      exists v. split.
      apply Hvalv.
      assert (Hext' : forall z, (c1 .: α) z = (c1 .: α') z).
      { intros []; [reflexivity | simpl; apply Hext]. }
      apply (IHφ (c1 .: α) (c1 .: α') v Hext'). apply Hrealv.
    + intros Hext. 
      intros (x & y & Hrealy & Heq).
      exists x. exists y. split.
      assert (Hext' : forall z, (x .: α) z = (x .: α') z).
      { intros []; [reflexivity | simpl; apply Hext]. }
      apply (IHφ (x .: α) (x .: α') y Hext'). apply Hrealy.
      apply Heq.        
  Qed.

  Lemma realizes_ext_iff {f : falsity_flag} α α' c (φ : form) :
  (forall x, α x = α' x) -> c ⊩[α] φ <-> c ⊩[α'] φ.
  Proof.
    intros Hext. split.
    - eapply realizes_ext; try assumption.
    - eapply realizes_ext. intros x; symmetry; apply Hext.
  Qed.

  Lemma realizes_subst {f : falsity_flag} α c ρ (φ : form) :
    c ⊩[α] (subst_form ρ φ) <->
    c ⊩[fun x => eval α (ρ x)] φ.
  Proof.
    induction φ in c, α, ρ |-*.
    - tauto.
    - destruct P. repeat depelim t. cbn. repeat rewrite eval_subst. tauto.
    - destruct b0. 
      + simpl. split.
        {
          intros (c1 & c2 & Hc1 & Hc2 & Heq).
          exists c1. exists c2. split. 
          apply (IHφ1 α c1). apply Hc1. split.
          apply (IHφ2 α c2). apply Hc2. apply Heq. 
        } 
        {
          intros (c1 & c2 & Hc1 & Hc2 & Heq).
          exists c1. exists c2. split. 
          apply (IHφ1 α c1). apply Hc1. split.
          apply (IHφ2 α c2). apply Hc2. apply Heq. 
        }
      + simpl. split.
        {
          intros [(c1 & Heq & Hc1) | (c1 & Heq & Hc1)].
          - left. exists c1. split.
            apply Heq.
            apply (IHφ1 α c1).
            apply Hc1.
          - right. exists c1. split.
            apply Heq.
            apply (IHφ2 α c1).
            apply Hc1.
        }
        {
          intros [(c1 & Heq & Hc1) | (c1 & Heq & Hc1)].
          - left. exists c1. split.
            apply Heq.
            apply (IHφ1 α c1).
            apply Hc1.
          - right. exists c1. split.
            apply Heq.
            apply (IHφ2 α c1).
            apply Hc1.
        }         
      + simpl. split.
        {
          intros H c1 Hc1.
          destruct (H c1) as (v & Hvalv & Hrealv).
          apply (IHφ1 α c1). apply Hc1.
          exists v. split.
          apply Hvalv.
          apply IHφ2. apply Hrealv.
        }
        {
          intros H c1 Hc1.
          destruct (H c1) as (v & Hvalv & Hrealv).
          apply (IHφ1 α c1). apply Hc1.
          exists v. split.
          apply Hvalv.
          apply IHφ2. apply Hrealv.
        }        
  - destruct q.
    + simpl. split.
        {
          intros H c1. 
          destruct (H c1) as (v & Hvalv & Hrealv).
          exists v. split.
          apply Hvalv.  
          apply IHφ in Hrealv.
          eapply realizes_ext_iff. 2:apply Hrealv. 
          intros []; try reflexivity. cbn.
          unfold funcomp. rewrite eval_subst. reflexivity.
        }
        {
          intros H c1.
          destruct (H c1) as (v & Hvalv & Hrealv).
          exists v. split.
          apply Hvalv. apply IHφ.  
          eapply realizes_ext_iff; try apply Hrealv. 
          intros []. 
          reflexivity.  
          cbn. unfold funcomp. rewrite eval_subst. reflexivity.
        }
    + simpl. split.
        {
          intros (x & y & Hrealy & Heq).
          exists x. exists y. split. 2: assumption.
          specialize (IHφ (x .: α) y (up ρ)).
          destruct IHφ as [H _].
          specialize (H Hrealy).
          eapply realizes_ext_iff; try apply H.
          intros []. 
          reflexivity.
          cbn. unfold funcomp. rewrite eval_subst. reflexivity.           
        }
        {
          intros (x & y & Hrealy & Heq).
          exists x. exists y. split. 2: assumption.
          specialize (IHφ (x .: α) y (up ρ)).
          destruct IHφ as [_ H].
          apply H.
          eapply realizes_ext_iff; try apply Hrealy.
          intros []. 
          reflexivity.
          cbn. unfold funcomp. rewrite eval_subst. reflexivity. 
        }
  Qed.

Lemma real_subst {f : falsity_flag} α ρ (φ : form) c :
  (forall x, eval α (ρ x) = α x) -> c ⊩[α] φ <-> c ⊩[α] (subst_form ρ φ).
Proof.
  intros H. rewrite realizes_subst.
  rewrite realizes_ext_iff with
    (α := fun x : nat => eval α (ρ x)) (α' := α).
  reflexivity. assumption.
Qed.

Lemma real_num_subst {f : falsity_flag} (φ : form) α c n :
  c ⊩[(n .: α)] φ <-> c ⊩[α] φ[(num n)..].
Proof.
  rewrite realizes_subst.
  rewrite realizes_ext_iff with
    (α := (n .: α)) (α' := fun x : nat => eval α ((num n).. x)).
  reflexivity.
  intros []. symmetry. apply eval_num.
  simpl. simp eval. reflexivity.
Qed.

End Real.

(** ** Contexts: Substitution and Extensionality *)

Section Ctx.

Lemma env_extend_ext (α α' : env nat) (c : nat) :
  (forall x : nat, α x = α' x) ->
  forall x, (c .: α) x = (c .: α') x.
Proof.
  intros H x. destruct x.
  - reflexivity.
  - simpl. apply H.
Qed.

Lemma realizes_ext_iff_ctx {f : falsity_flag} α α' c
  (Γ : list form) :
    (forall x, α x = α' x) ->
    c ⊩ctx[α] Γ <-> c ⊩ctx[α'] Γ.
Proof.
  induction Γ in c |-*.
  - tauto.
  - simpl. intros Hext. split.
    {
      intros (c1 & Hrealc1 & (c2 & Hrealc2 & Heq)).
      exists c1. split. 
      eapply (realizes_ext_iff _ _ Hext). apply Hrealc1.
      exists c2. split. 2: assumption.
      apply IHΓ. apply Hext. apply Hrealc2.
    } 
    {
      intros (c1 & Hrealc1 & (c2 & Hrealc2 & Heq)).
      exists c1. split. 
      eapply (realizes_ext_iff _ _ Hext). apply Hrealc1.
      exists c2. split. 2: assumption.
      apply IHΓ. apply Hext. apply Hrealc2.
    }
Qed.


Lemma realizes_subst_ctx {f : falsity_flag} α c ρ
  (Γ : list form) :
  c ⊩ctx[α] (map (subst_form ρ) Γ) <->
  c ⊩ctx[fun x => eval α (ρ x)] Γ.
Proof.
  induction Γ in c |-*.
  - tauto.
  - simpl. split.
    {
      intros (c1 & Hrealc1 & (c2 & Hrealc2 & Heq)).
      exists c1. split.
      apply realizes_subst. apply Hrealc1.
      exists c2. split. 2: assumption.
      apply IHΓ. apply Hrealc2.
    }
    {
      intros (c1 & Hrealc1 & (c2 & Hrealc2 & Heq)).
      exists c1. split.
      apply realizes_subst. apply Hrealc1.
      exists c2. split. 2: assumption.
      apply IHΓ. apply Hrealc2.
    }
Qed.

End Ctx.

(** ** Simple Properties of Realizability *)

Section RealizabilityFacts.

Lemma realizes_neg_iff (φ : form) (α : env nat): 
  forall c, c ⊩[α] (¬ φ) <-> (~ exists m, m ⊩[α] φ).
Proof.
  intros c. split; simpl; intros H.
  setoid_rewrite ex_P_and_False in H.
  setoid_rewrite ex_all_equiv in H.
  apply H.
  setoid_rewrite ex_P_and_False.
  setoid_rewrite ex_all_equiv.
  assumption.
Qed.

Lemma realizes_double_negation_iff (φ : form) (α : env nat): 
  forall c : nat, c ⊩[α] (¬¬ φ) <-> ~~ exists m, m ⊩[α] φ.
Proof.
  simpl. intros c; split.
  {
    intros Hcdn. 
    setoid_rewrite ex_P_and_False in Hcdn.
    specialize (Hcdn 0).
    setoid_rewrite ex_all_equiv in Hcdn.
    assumption.
  }
  {
    intros Hdn x.
    setoid_rewrite ex_P_and_False.
    setoid_rewrite ex_all_equiv.
    assumption.
  } 
Qed.

Lemma realizes_exists {f : falsity_flag} (φ : form) (α : env nat) : 
  (exists m : nat, m ⊩[α] (∃ φ)) <->
  (exists x, exists m, m ⊩[x .: α] φ).
Proof.
  simpl; split; intros H.
  destruct H as (m & x & y & Hrealy & Heq).
  exists x. exists y. assumption.
  destruct H as (x & y & Hrealy).
  exists ⟨x, y⟩. exists x. exists y.
  split; [assumption | reflexivity].
Qed.

End RealizabilityFacts.

(** ** Environment Independence of Closed Formulas *)

Section ClosedForms.

Lemma sat_closed {f : falsity_flag} (φ : form) (α : env nat) : 
  bounded 0 φ -> forall ρ, sat interp_nat α φ <-> sat interp_nat α φ[ρ].
Proof.
  intros Hbd ρ.
  apply subst_closed with (sigma := ρ) in Hbd.
  rewrite Hbd. 
  trivial.
Qed.

Lemma sat_closed_env_gen {f : falsity_flag} (φ : form) (α : env nat) : 
  bounded 0 φ -> sat interp_nat (fun _ => 0) φ -> sat interp_nat α φ.
Proof.
  intros Hbd Hsat.
  assert (Hsub : sat interp_nat (fun _ => 0) φ[(fun n => num (α n))]).
  {
    apply sat_closed; assumption.
  }
  rewrite sat_comp in Hsub.
  unfold ">>" in Hsub.
  assert (forall x, @FullCore.eval _ _ _ interp_nat(fun _ : nat => 0) (num (α x)) = α x) as Hext.
  intros x. rewrite nat_eval_num. reflexivity.
  eapply sat_ext.
  symmetry. exact (Hext x).
  apply Hsub.
Qed. 


Lemma real_closed {f : falsity_flag} (φ : form) (α : env nat) (c : nat) : 
  bounded 0 φ -> forall ρ, c ⊩[α] φ <-> c ⊩[α] φ[ρ].
Proof.
  intros Hbd ρ.
  apply subst_closed with (sigma := ρ) in Hbd.
  rewrite Hbd. 
  trivial.
Qed.

Lemma real_closed_env_gen {f : falsity_flag} (φ : form) (α : env nat) : 
  bounded 0 φ -> forall c, c ⊩ φ -> c ⊩[α] φ.
Proof.
  intros Hbd c Hreal.
  assert (Hsub : c ⊩ φ[(fun n => num (α n))]).
  {
    apply real_closed; assumption.
  }
  rewrite realizes_subst in Hsub.
  assert (forall x, eval (fun _ : nat => 0) (num (α x)) = α x) as Hext.
  intros x. rewrite eval_num. reflexivity.
  apply realizes_ext with (α := fun x : nat => eval (fun _ : nat => 0) (num (α x))). 
  all : assumption. 
Qed.

End ClosedForms.

End NumberRealizability.
