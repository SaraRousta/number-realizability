From SyntheticComputability Require Import EPF partial equiv_on Definitions reductions embed_nat.
From Stdlib Require Import Arith.
From Equations Require Import Equations.
From FOL Require Import FullSyntax Arithmetics.

Import EmbedNatNotations.

From Stdlib Require Import List.
Import ListNotations.

From NumberRealizability Require Import LogicalFacts Core Facts.

(** * Realizability of Markov's Principle *)


Section RealizingMP.
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

(** ** Markov's principle for HA *)

Definition MP_Prop_HA (φ : form) : form :=
  (∀ (φ ∨ ¬φ)) → (¬¬(∃ φ)) → ∃ φ.

(** ** Total partial functions are total *)

Section PartialityFacts.

Lemma ex_value (A : Type) : forall (x : part A), (exists a, x =! a) -> {a : A | x =! a}.
Proof.
  intros x H.
  assert (exists n, seval x n <> None) as Heval.
  {
    destruct H as [y Hvaly].
    apply seval_hasvalue in Hvaly.
    destruct Hvaly as [n Hvaly].
    exists n.
    rewrite Hvaly. congruence.
  }
  apply ConstructiveEpsilon.constructive_indefinite_ground_description_nat in Heval.
  2 : { intros n. destruct (seval x n). left. congruence. right. congruence. }
  destruct Heval as [n Heval].
  destruct (seval x n) as [v | ] eqn: Hv.
  exists v.
  apply seval_hasvalue.
  exists n. apply Hv.
  congruence.
Qed.

Lemma total_partial_total (A B : Type) (f : A -> part B) :
  (forall x, exists y, f x =! y) ->  exists g, forall x, f x =! g x.
Proof.
  intros H.
  unshelve eexists.
  - intros x.
    specialize (H x).
    eapply ex_value in H.
    destruct H as [y Hy].
    exact y.
  - intros x; simpl.
    destruct ex_value as [y Hy].
    assumption.
Qed.

End PartialityFacts.

(** ** Realizing Markov's Principle *)

Lemma HA_dec_imp_dec_ex_real (φ : form) (d: nat) (α : env nat): 
  d ⊩[α] (∀ (φ ∨ ¬φ)) ->
  decidable (fun x => exists m, m ⊩[x .: α] φ).
Proof.
  simpl. intros Hdec.
  assert (forall x, exists y, θ d x =! y) by firstorder.
  apply total_partial_total in H.
  destruct H as [g Hg].
  exists (fun x => match (fst (unembed (g x))) =? 0 with 
                  | true => true
                  | false => false
                    end).
  intros x.
  destruct (Hdec x) as (v & Hvalv & []).
  all: pose proof (hasvalue_det (Hg x) Hvalv) as Heq.
  all:  destruct H as (u & Hequ & Hrealu); subst.
  all:  rewrite Heq; rewrite embedP. 
  - firstorder.
  - setoid_rewrite ex_P_and_False in Hrealu.
    setoid_rewrite ex_all_equiv in Hrealu.
    cbn. split. tauto. congruence.
Qed.


Lemma real_dec_imp_mu_ter (φ : form) (α : env nat) (d e : nat) :
  d ⊩[α] ∀ φ ∨ (¬ φ) ->
  e ⊩[α] ∃ φ ->
  exists v : nat, mu (fun n : nat => bind (θ d n) (fun! ⟨ u, _ ⟩ => ret (u =? 0))) =! v.
Proof.
  intros Hdec Hexm.
  apply mu_ter.
  destruct Hexm as (x & y & Hy & Heq).
  exists x. split. 
  - apply bind_hasvalue.
    destruct (Hdec x) as (v & Hvalv & Hd).
    exists v. split; try assumption.
    destruct Hd as [Hφ | Hnφ]. 
    + destruct Hφ as (u & Hveq & Hφ).
      rewrite Hveq. rewrite embedP. 
      apply ret_hasvalue.
    + destruct Hnφ as (u & Hveq & Hnφ).
      specialize (Hnφ y).
      specialize (Hnφ Hy).
      rewrite ex_P_and_False in Hnφ.
      destruct Hnφ.
  - intros n Hleq.
    destruct (Hdec n) as (v & Hvalv & Hd).
    destruct Hd as [Hφ | Hnφ].
    + exists true.
      apply bind_hasvalue. 
      exists v. split; try assumption.
      destruct Hφ as (u & Hveq & Hφ).
      rewrite Hveq. rewrite embedP. 
      apply ret_hasvalue.
    + exists false.
      apply bind_hasvalue. 
      exists v. split; try assumption.
      destruct Hnφ as (u & Hveq & Hnφ).
      rewrite Hveq. rewrite embedP. 
      apply ret_hasvalue.
Qed.


Definition real_MP_HA := fun d => 
                         fun _ : nat => 
                         bind (mu (fun n => bind (θ d n) (fun! ⟨u, v⟩ => ret (Nat.eqb u 0)))) (fun m => bind (θ d m) (fun! ⟨_, v⟩ => ret ⟨m, v⟩)).

Lemma mu_ter_imp_MP_HA (φ : form) (d e v : nat) (α : env nat) (γ : nat -> nat) :
  d ⊩[α] ∀ φ ∨ (¬ φ) ->
  e ⊩[α] ¬ (¬ (∃ φ)) ->
  mu (fun n : nat => bind (θ d n) (fun! ⟨ u, _ ⟩ => ret (u =? 0))) =! v ->
  (forall x : nat, θ (γ x) ≡{ nat ↛ nat} real_MP_HA x) ->
  exists u : nat, θ (γ d) e =! u /\ u ⊩[α] ∃ φ.
Proof.
  intros Hdec _ Hter Hγ.
  destruct (Hdec v) as (u & Hvalu & H).
  destruct H; destruct H as (w & Hequ & Hrelw).
  {
    exists ⟨v, w⟩; split.
    apply Hγ.
    apply bind_hasvalue.
    exists v; split; try assumption.
    apply bind_hasvalue.
    exists u; split; try assumption.
    rewrite Hequ. rewrite embedP.
    apply ret_hasvalue.
    exists v. exists w.
    split; [assumption | reflexivity].
  }
  {
    apply mu_hasvalue in Hter.
    destruct Hter as [Hval _].
    apply bind_hasvalue in Hval.
    destruct Hval as (u' & Hvalu' & Hval).
    enough (u = u') as Heq.
    {
      rewrite <- Heq in Hval.
      rewrite Hequ in Hval.
      rewrite embedP in Hval.
      simpl in Hval.
      apply ret_hasvalue_inv in Hval.
      discriminate.
    }
    eapply hasvalue_det; [apply Hvalu | apply Hvalu'].
  }
Qed.


(** *** From DNE *)

Lemma DNE_imp_real_ex (φ : form) (e d : nat) : 
  DNE -> 
  e ⊩ ¬ (¬ (∃ φ)) ->
  exists m, m ⊩ ∃ φ.
Proof.
  intros dne Hedn.
  apply realizes_double_negation_iff in Hedn as Hexm.
  apply dne in Hexm.
  assumption.
Qed.


Lemma DNE_realizes_MP (φ : form) : 
  DNE ->
  bounded 1 φ -> 
  exists c, c ⊩ (MP_Prop_HA φ).
Proof.
  intros dne bnd.
  destruct (epf_param real_MP_HA) as [γ Hγ].

  destruct (epf (fun x => ret (γ x))) as [c Hc].

  exists c.
  intros d Hdec.
  exists (γ d); split.

  apply Hc. apply ret_hasvalue.
  intros e Hedn.

  assert (Hexm : exists m : nat, m ⊩ (∃ φ)).
  { eapply DNE_imp_real_ex; eassumption. }

  destruct Hexm as [m Hexm].

  assert (Hter : exists v, (mu (fun n => bind (θ d n) (fun! ⟨u, v⟩ => ret (Nat.eqb u 0)))) =! v). 
  { eapply real_dec_imp_mu_ter; eassumption. }

  destruct Hter as (v & Hter).

  eapply mu_ter_imp_MP_HA; eassumption.
Qed.

(** *** From MP_bool *)

Lemma MP_bool_imp_real_ex (φ : form) (α : env nat) (e d : nat) : 
  MP_bool -> 
  d ⊩[α] ∀ φ ∨ (¬ φ) ->
  e ⊩[α] ¬ (¬ (∃ φ)) ->
  exists m, m ⊩[α] ∃ φ.
Proof.
  intros mp Hdec Hedn.
  apply realizes_double_negation_iff in Hedn as Hdnexm.
  rewrite realizes_exists in Hdnexm.
  rewrite realizes_exists.
  apply HA_dec_imp_dec_ex_real in Hdec.
  destruct Hdec as [f Hdec].
  unfold decider in Hdec. unfold reflects in Hdec.
  setoid_rewrite Hdec. 
  apply mp.
  setoid_rewrite <- Hdec.
  assumption.
Qed.


Lemma MP_bool_real_MP (φ : form) (α : env nat): 
  MP_bool ->
  exists c, c ⊩[α] (MP_Prop_HA φ).
Proof.
  intros mp.
  destruct (epf_param real_MP_HA) as [γ Hγ].

  destruct (epf (fun x => ret (γ x))) as [c Hc].

  exists c.
  intros d Hdec.
  exists (γ d); split.

  apply Hc. apply ret_hasvalue.
  intros e Hedn.

  assert (Hexm : exists m : nat, m ⊩[α] (∃ φ)).
  { eapply MP_bool_imp_real_ex; eassumption. }

  destruct Hexm as [m Hexm].
 
  assert (Hter : exists v, (mu (fun n => bind (θ d n) (fun! ⟨u, v⟩ => ret (Nat.eqb u 0)))) =! v). 
  { eapply real_dec_imp_mu_ter; eassumption. }

  destruct Hter as (v & Hter).

  eapply mu_ter_imp_MP_HA; eassumption.
Qed.

(** *** From MP_decidable *)

Lemma MP_decidable_imp_real_ex (φ : form) (e d : nat) : 
  MP_decidable -> 
  d ⊩ ∀ φ ∨ (¬ φ) ->
  e ⊩ ¬ (¬ (∃ φ)) ->
  exists m, m ⊩ ∃ φ.
Proof.
  intros mp Hdec Hedn.
  apply realizes_double_negation_iff in Hedn as Hexm.
  rewrite realizes_exists in Hexm.
  rewrite realizes_exists. 
  apply mp.
  eapply HA_dec_imp_dec_ex_real.
  apply Hdec.
  assumption.
Qed.


Lemma MP_decidable_realizes_MP (φ : form):
  MP_decidable ->
  bounded 1 φ -> 
  exists c, c ⊩ (MP_Prop_HA φ).
Proof.
  intros mp bnd.
  destruct (epf_param real_MP_HA) as [γ Hγ].
  destruct (epf (fun x => ret (γ x))) as [c Hc].

  exists c.
  intros d Hdec.
  exists (γ d); split.

  apply Hc. apply ret_hasvalue.
  intros e Hedn.

  assert (Hexm : exists m : nat, m ⊩ (∃ φ)).
  { eapply MP_decidable_imp_real_ex; eassumption. }

  destruct Hexm as [m Hexm].
  
  assert (Hter : exists v, (mu (fun n => bind (θ d n) (fun! ⟨u, v⟩ => ret (Nat.eqb u 0)))) =! v). 
  { eapply real_dec_imp_mu_ter; eassumption. }

  destruct Hter as (v & Hter).

  eapply mu_ter_imp_MP_HA; eassumption.
Qed.


End RealizingMP.
