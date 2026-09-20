From SyntheticComputability Require Import EPF partial equiv_on Definitions reductions embed_nat.
From Stdlib Require Import Vector.
From Equations Require Import Equations.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Program.Equality.

Import EmbedNatNotations.

From Stdlib Require Import List.
Import ListNotations.

From NumberRealizability Require Import LogicalFacts Core Facts RealizingEnvTerms AlmostNegative.

(** * Characterization of Number Realizability *)

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
  Local Notation "code ⊩env[ n ] α" :=
    (realizes_env n code α)
    (at level 70, format "code  ⊩env[ n ]  α").

Section AlmostNegative.

(** ** Almost-Negative Predicates *)

  Inductive AN_pred : forall X, (X -> Prop) -> Prop := 
  | AN_semi_dec {X} (P : X -> Prop) : semi_decidable P -> AN_pred P
  | AN_conj {X} (P Q : X -> Prop) : AN_pred P -> AN_pred Q -> AN_pred (fun x => P x /\ Q x)
  | AN_imp {X} (P Q : X -> Prop) : AN_pred P -> AN_pred Q -> AN_pred (fun x => P x -> Q x)
  | AN_forall {X Y} (P : Y -> X -> Prop) : (forall y, AN_pred (fun x => P y x)) -> AN_pred (fun x => forall y, P y x).

End AlmostNegative.

(** ** Semidecidability and Pairing *)

Section ComputabilityFacts.

  Definition H := fun '(c, x) => exists n, seval (θ c x) n <> None.
  Definition V := fun '(c, (x, v)) => exists n, seval (θ c x) n = Some v.

  Lemma dec_mat_H : decidable (fun '(n , (c, x)) => seval (θ c x) n <> None).
  Proof.
    unshelve eexists.
    - intros (n, (c, x)).
      destruct (seval (θ c x) n).
      + exact true.
      + exact false.
    - intros (n, (c, x)).
      split; intros H; destruct (seval (θ c x) n); cbn in H; congruence.
  Qed.

  Lemma dec_mat_V : decidable (fun '(n, (c, (x, v))) => seval (θ c x) n = Some v).
  Proof.
    unshelve eexists.
    - intros (n, (c, (x, v))).
      destruct (seval (θ c x) n) eqn : H.
      + destruct (eq_dec v n0).
        * exact true.
        * exact false.
      + exact false.
    - intros (n, (c, (x, v))).
      split; intros H; cbn in H.
      + destruct (seval (θ c x) n) as [u| ]. 
        destruct (eq_dec u v) as [eq | neq] eqn : Heq.
        cbn. subst. rewrite Heq. reflexivity.
        exfalso. apply neq. injection H. tauto.
        congruence.
      + destruct (seval (θ c x) n) as [u |] eqn:Heq.
        2: congruence.
        destruct (eq_dec v u) as [eq | neq] eqn : ?.
        subst. reflexivity.
        congruence.
  Qed.


  Lemma semi_decidable_H : semi_decidable H.
  Proof.
    apply SemiDecidabilityFacts.semi_decidable_projection_iff.
    exists (fun '(n, (c, x)) => (seval (θ c x) n <> None)). split. 
    apply dec_mat_H. 
    intros [c x]. reflexivity.
  Qed.

  Lemma semi_decidable_V : semi_decidable V.
  Proof.
    apply SemiDecidabilityFacts.semi_decidable_projection_iff.
    exists (fun '(n, (c, (x, v))) => seval (θ c x) n = Some v). split.
    apply dec_mat_V. 
    intros (c & x & v). reflexivity.
  Qed.

  Definition π0 := fun! ⟨x, y⟩ => x.
  Definition π1 := fun! ⟨x, y⟩ => y.

  Lemma embed_proj (n : nat) : n = ⟨π0 n, π1 n⟩.
  Proof.
    unfold π0, π1.
    destruct (unembed n) as [x y] eqn:H.
    rewrite <- H. symmetry. apply unembedP.
  Qed.

  Lemma π0_embed x y : π0 ⟨x,y⟩ = x.
  Proof.
    unfold π0. 
    rewrite embedP. 
    reflexivity.
  Qed.

  Lemma π1_embed x y : π1 ⟨x,y⟩ = y.
  Proof.
    unfold π1.
    rewrite embedP.
    reflexivity.
  Qed.

  Lemma decidable_tag : decidable (fun p : env nat * nat => (π0 (snd p) = 0 \/ π0 (snd p) = 1)).
  Proof.
    unshelve eexists.
    - intros [α c]. destruct (eq_dec (π0 c) 0).
      + exact true.
      + destruct (eq_dec (π0 c) 1).
        * exact true.
        * exact false.
    - intros [α c]. destruct (eq_dec (π0 c) 0); cbn.
      split; tauto.
      destruct (eq_dec (π0 c) 1); cbn.
      split; tauto.
      split. intros []; exfalso; tauto.
      congruence.
  Qed.

  Lemma decidable_to_semi_decidable {X} (P : X -> Prop) : decidable P -> semi_decidable P.
  Proof.
    intros [g H].
    exists (fun x => fun n => g x).
    intros x. split.
    intros px. exists 0. apply H. assumption.
    intros []. apply H. assumption.
  Qed.

  Lemma semi_decidable_tag : semi_decidable (fun p : env nat * nat => (π0 (snd p) = 0 \/ π0 (snd p) = 1)).
  Proof.
    apply decidable_to_semi_decidable.
    apply decidable_tag.
  Qed.

  Lemma semi_decidable_eql (v : nat) : semi_decidable (fun u => u = v).
  Proof.
    apply decidable_to_semi_decidable.
    unshelve eexists.
    - intros u. destruct (eq_dec u v).
      exact true. exact false.
    - intros u. destruct (eq_dec u v); cbn. 
      split; tauto.
      split; congruence.
  Qed.

End ComputabilityFacts.

(** ** The Auxiliary Predicate R *)

Section RealizabilityPredicate.

  Fixpoint R {f: falsity_flag} (α : env nat) (c : nat) (φ : form) : Prop := 
    match φ with 
    | falsity => False
    | atom Eq (Vector.cons t1 (Vector.cons t2 Vector.nil)) => eval α t1 = eval α t2
    | bin Conj φ1 φ2 => R α (π0 c) φ1 /\ R α (π1 c) φ2
    | bin Disj φ1 φ2 => (π0 c = 0 \/ π0 c = 1) /\ (π0 c = 0 -> R α (π1 c) φ1) /\ (π0 c = 1 -> R α (π1 c) φ2) 
    | bin Impl φ1 φ2 => forall x, (R α x φ1 -> (H (c, x) /\ forall v, ((V (c , (x ,v)) -> R α v φ2))))
    | quant All φ => forall x, ((H (c, x)) /\ forall v, ((V (c, (x, v)) -> R (x .: α) v φ)))
    | quant Ex φ  => R (π0 c .: α) (π1 c) φ
    | _ => False
    end.

  Lemma AN_pred_comp {X Y} (P : Y -> Prop) (g : X -> Y) :
    AN_pred P -> AN_pred (fun x => P (g x)).
  Proof.
    intros H.
    induction H as [Y P H | Y P Q Hp IHp Hq IHq | Y P Q Hp IHp Hq IHq | Y Z P H IH].
    - constructor. destruct H as [d Hd].
      exists (fun x n => d (g x) n).
      intro x. apply Hd.
    - constructor 2. apply IHp. apply IHq.
    - constructor 3. apply IHp. apply IHq.
    - constructor 4. intros z. apply IH.
  Qed.   

  Lemma AN_pred_R {f : falsity_flag} (φ : form) : AN_pred (fun p : env nat * nat => R (fst p) (snd p) φ).
  Proof.
    induction φ.
    - simpl. constructor. apply decidable_to_semi_decidable.
      exists (fun _ => false).
      intros [α c]. split. tauto. congruence.
    - destruct P. repeat depelim t.
      constructor. apply decidable_to_semi_decidable. simpl.
      unshelve eexists.
      + intros [α c]. 
        destruct (eq_dec (eval α h) (eval α h0)).
        exact true.
        exact false.
      + intros [α c]. destruct (eq_dec (eval α h) (eval α h0)).
        cbn. split; tauto.
        cbn. split; congruence.
    - destruct b0.
      + simpl. constructor 2.
        change (AN_pred (fun p : env nat * nat => (fun q : env nat * nat => R (fst q) (snd q) φ1) (fst p, π0 (snd p)))).
        eapply AN_pred_comp. apply IHφ1.
        change (AN_pred (fun p : env nat * nat => (fun q : env nat * nat => R (fst q) (snd q) φ2) (fst p, π1 (snd p)))).
        eapply AN_pred_comp. apply IHφ2.
      + simpl. constructor 2. constructor 1. apply semi_decidable_tag.
        constructor 2; constructor 3.
        * change (AN_pred (fun p : env nat * nat => (fun v : nat => v = 0) (π0 (snd p)))).
          eapply AN_pred_comp. constructor. eapply semi_decidable_eql.
        * change (AN_pred (fun p : env nat * nat => (fun c : env nat * nat => R (fst c) (snd c) φ1) (fst p, π1 (snd p)))).
          eapply AN_pred_comp. apply IHφ1.
        * change (AN_pred (fun p : env nat * nat => (fun v : nat => v = 1) (π0 (snd p)))).
          eapply AN_pred_comp. constructor. eapply semi_decidable_eql.
        * change (AN_pred (fun p : env nat * nat => (fun c : env nat * nat => R (fst c) (snd c) φ2) (fst p, π1 (snd p)))).
          eapply AN_pred_comp. apply IHφ2.
      + simpl. constructor 4. intros c1.
        constructor 3.
        change (AN_pred (fun p : env nat * nat => (fun c : env nat * nat => R (fst c) (snd c) φ1) (fst p, c1))).
        eapply AN_pred_comp. apply IHφ1.
        constructor 2. 
        change (AN_pred (fun p : env nat * nat => H ((snd p), c1))).
        change (AN_pred (fun p : env nat * nat => (fun y : nat * nat => H y) (snd p, c1))).
        eapply AN_pred_comp. constructor. apply semi_decidable_H.
        constructor 4. intros v.
        constructor 3.
        change (AN_pred (fun p : env nat * nat => V ((snd p), (c1, v)))). 
        change (AN_pred (fun p : env nat * nat => V ((fun y : env nat * nat => (snd y, (c1, v))) p))).
        eapply AN_pred_comp. constructor. apply semi_decidable_V.
        change (AN_pred (fun p : env nat * nat => (fun c : env nat * nat => R (fst c) (snd c) φ2) (fst p, v))).
        eapply AN_pred_comp. apply IHφ2.
    - destruct q. 
      + simpl. constructor 4. 
        intros c1. constructor 2.
        change (AN_pred (fun p : env nat * nat => (fun y : nat * nat => H y) (snd p, c1))).
        eapply AN_pred_comp. constructor. apply semi_decidable_H.
        constructor 4. intros v. constructor 3.
        change (AN_pred (fun p : env nat * nat => V ((fun y : env nat * nat => (snd y, (c1, v))) p))).
        eapply AN_pred_comp. constructor. apply semi_decidable_V.
        change (AN_pred (fun p : env nat * nat => (fun c : env nat * nat => R (fst c) (snd c) φ) ((c1 .: fst p), v))).
        eapply AN_pred_comp. apply IHφ.
      + simpl. change (AN_pred (fun p : env nat * nat => (fun c => R (fst c) (snd c) φ) (((π0 (snd p)) .: fst p), π1 (snd p)))).
      eapply AN_pred_comp. assumption.
  Qed.

  Lemma real_equiv_R {f : falsity_flag} (α : env nat) (c : nat) (φ : form) :
    R α c φ <-> c ⊩[α] φ.
  Proof.
    induction φ in α, c |-*.
    - tauto.
    - tauto.
    - destruct b0.
      + simpl. split.
        * intros []. exists (π0 c). exists (π1 c). repeat split; try assumption. apply IHφ1; assumption. apply IHφ2; assumption. apply embed_proj.
        * intros (c1 & c2 & Hc1 & Hc2 & Heq). subst. rewrite π0_embed. rewrite π1_embed. split. apply IHφ1; assumption. apply IHφ2; assumption.
      + simpl. split.
        * intros (Hdec & Hl & Hr).
          destruct Hdec as [H | H]. 
          left. exists (π1 c). split. rewrite <- H. apply embed_proj. apply IHφ1. apply Hl. assumption. 
          right. exists (π1 c). split. rewrite <- H. apply embed_proj. apply IHφ2. apply Hr. assumption.
        * intros [(c1 & Heq & Hc1) | (c1 & Heq & Hc1)].
          repeat split. left. subst. apply π0_embed. 
          intros. subst. rewrite π1_embed. apply IHφ1. assumption. 
          intros. enough (π0 c = 0) by congruence. subst. apply π0_embed.
          repeat split. right. subst. apply π0_embed. 
          intros. enough (π0 c = 1) by congruence. subst. apply π0_embed.
          intros. subst. rewrite π1_embed. apply IHφ2. assumption.
      + simpl. split.
        * intros H c1 Hc1. apply IHφ1 in Hc1. specialize (H c1 Hc1). destruct H as [Hex H].
          destruct Hex as [n Hex].
          destruct (seval (θ c c1) n) as [v | ] eqn: Hv.
          exists v. split. apply seval_hasvalue. exists n. apply Hv.
          apply IHφ2. apply H. exists n. apply Hv.
          congruence.
        * intros H c1 Hc1. apply IHφ1 in Hc1. split; specialize (H c1 Hc1); destruct H as (v & Hvalv & Hrealv).
          apply seval_hasvalue in Hvalv. destruct Hvalv as [n Hvalv].
          exists n. congruence.
          intros u Hu. apply seval_hasvalue in Hu. 
          enough (v = u). subst; apply IHφ2; assumption.
          eapply hasvalue_det; eassumption.
    - destruct q.
      + simpl. split. 
        * intros H x. specialize (H x). destruct H as [Hex H].
          destruct Hex as [n Hex].
          destruct (seval (θ c x) n) as [v | ] eqn: Hv.
          exists v. split. apply seval_hasvalue. exists n. apply Hv.
          apply IHφ. apply H. exists n. apply Hv.
          congruence.
        * intros H x. split; specialize (H x); destruct H as (v & Hvalv & Hrealv).
          apply seval_hasvalue in Hvalv. destruct Hvalv as [n Hvalv].
          exists n. congruence.
          intros u Hu. apply seval_hasvalue in Hu. 
          enough (v = u). subst; apply IHφ; assumption.
          eapply hasvalue_det; eassumption.
      + simpl. split. 
        * intros H. exists (π0 c). exists (π1 c). split; [apply IHφ; assumption | apply embed_proj].
        * intros H. destruct H as (x & y & Hreal & Heq).
          subst. rewrite π0_embed. rewrite π1_embed. apply IHφ. assumption.
  Qed.

  Definition AN_prop (Q : Prop) := AN_pred (fun _ : unit => Q).

  Lemma AN_prop_R {f : falsity_flag} (α : env nat) (c : nat) (φ : form) : AN_prop (R α c φ).
  Proof.
    unfold AN_prop. 
    change (AN_pred (fun u : unit => (fun p : env nat * nat => R (fst p) (snd p) φ) (α, c))).
    eapply AN_pred_comp.
    apply AN_pred_R.
  Qed.

End RealizabilityPredicate.

(** ** The Characterization Theorem *)

Section Characterization.

  Definition IP_AN_prop_nat := forall (Q : Prop) (P : nat -> Prop), AN_prop Q -> (Q -> exists n, P n) -> exists n, (Q -> P n).

  Theorem real_equiv_stdmodel {f : falsity_flag} (φ : form) (α : env nat) :
    AC_nat -> IP_AN_prop_nat -> (exists c, c ⊩[α] φ) <-> sat interp_nat α φ.
  Proof.
    intros ac ip.
    induction φ in α |-*.
    - simpl. firstorder.
    - destruct P. repeat depelim t. simpl.
      split. intros []. repeat rewrite <- eval_real_stdmodel. assumption.
      intros. exists 0. repeat rewrite eval_real_stdmodel. assumption.
    - destruct b0.
      + simpl.
        split. 
        * intros (c & c1 & c2 & Hc1 & Hc2 & Heq). split. 
          apply IHφ1. eexists. eassumption.
          apply IHφ2. eexists. eassumption.
        * intros [H1 H2]. 
          apply IHφ1 in H1. destruct H1 as [c1 H1].
          apply IHφ2 in H2. destruct H2 as [c2 H2].
          exists ⟨c1, c2⟩. exists c1. exists c2.
          repeat split; try assumption; try reflexivity.
      + split.
        * simpl. intros [x H].
          destruct H as [H | H]. 
          left. apply IHφ1. destruct H as (c & Heq & Hc). exists c. assumption.
          right. apply IHφ2. destruct H as (c & Heq & Hc). exists c. assumption.
        * simpl. intros H.
          destruct H as [H | H].
          apply IHφ1 in H. destruct H.
          exists ⟨0, x⟩.
          left. exists x. split.
          reflexivity. assumption.
          apply IHφ2 in H. destruct H.
          exists ⟨1, x⟩.
          right. exists x. split.
          reflexivity. assumption.
      + simpl. split. 
        * intros [c Hc]. intros H1.
          apply IHφ1 in H1. destruct H1 as [c1 Hc1].
          specialize (Hc c1 Hc1). destruct Hc as (v & Hvalv & Hrealv).
          apply IHφ2. exists v. assumption.
        * simpl. intros Himp.
          (* amounts to ECT0 *)
          assert (H : forall x, exists y, (R α x φ1 -> y ⊩[α] φ2)).
          {
            intros x. eapply ip. apply (AN_prop_R α x φ1).
            intros Hr. apply real_equiv_R in Hr. apply IHφ2. apply Himp. apply IHφ1. exists x. assumption. 
          }
          apply ac in H. 
          destruct H as [f H].
          destruct (epf (fun x => ret (f x))) as [c Hc].
          exists c. intros c1 Hc1.
          exists (f c1). split. 
          apply Hc. apply ret_hasvalue.
          apply H. apply real_equiv_R. assumption.
    - destruct q.
      + simpl. split.
        * intros [c Hc].
          intros d. specialize (Hc d). destruct Hc as (v & Hvalv & Hrealv).
          apply IHφ. exists v. assumption.
        * intros H. 
          (* amount to CT0 *)
          assert (forall d, exists e, e ⊩[(d .: α)] φ) as Hac.
          { intros d. specialize (H d). apply IHφ in H. assumption. }
          apply ac in Hac. 
          destruct Hac as [f Hac].
          destruct (epf (fun x => ret (f x))) as [c Hc].
          exists c. intros d.
          exists (f d). split. 
          apply Hc. apply ret_hasvalue.
          apply Hac. 
      + simpl. split.
        * simpl. intros (c & x & y & ? & ?).
          exists x.
          apply IHφ. exists y. assumption.
        * simpl. intros [d Hd].
          apply IHφ in Hd.
          destruct Hd.
          exists ⟨d, x⟩.
          exists d. exists x.
          split. assumption. reflexivity.
  Qed.
      

End Characterization.

End NumberRealizability.
