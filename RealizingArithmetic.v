From SyntheticComputability Require Import EPF partial equiv_on Definitions reductions embed_nat.
From Stdlib Require Import Vector.
From Equations Require Import Equations.
From FOL Require Import FullSyntax Arithmetics.

Import EmbedNatNotations.

From Stdlib Require Import List.
Import ListNotations.

From NumberRealizability Require Import Core Facts BoundedTactics.

(** * Realizing the Axioms of Arithmetic *)

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

  Ltac unfold_goals_list := 
  repeat match goal with 
    | H : In _ _ |- _ => destruct H
  end.

  Ltac unfold_goals := 
    repeat match goal with 
      | H : _ = _ |- _ => rewrite <- H
      | H : _ \/ _ |- _ => destruct H
      | H : False |- _ => destruct H
    end.

Section RealizingAxioms.


  Lemma realizes_ax_refl (α : env nat) : exists e, e ⊩[α] ax_refl.
  Proof.
    destruct (epf (fun _ => ret 0)) as [e He].
    exists e. simpl.
    intros x. exists 0. 
    split. apply He. apply ret_hasvalue.
    reflexivity.
  Qed.


  Lemma realizes_ax_sym (α : env nat) : exists e, e ⊩[α] ax_sym.
  Proof.
    destruct (epf_param (fun _ => fun _ => ret 0)) as [γ1 Hγ1].
    destruct (epf_param (fun x => fun y => ret (γ1 ⟨x, y⟩))) as [γ2 Hγ2].
    destruct (epf (fun x => ret (γ2 x))) as [e He].
    exists e. intros x. exists (γ2 x). split.
    apply He. apply ret_hasvalue. intros y. exists (γ1 ⟨x, y⟩). split.
    apply Hγ2. apply ret_hasvalue. intros h. simpl. simp eval. simpl.
    intros H. exists 0. split. apply Hγ1. apply ret_hasvalue.
    symmetry. assumption.
  Qed. 

  Lemma realizes_ax_trans (α : env nat) : exists e, e ⊩[α] ax_trans.
  Proof.
    destruct (epf_param (fun _ => fun _ => ret 0)) as [γ1 Hγ1].
    destruct (epf_param (fun q => fun u => ret (γ1 ⟨q, u⟩))) as [γ2 Hγ2].
    destruct (epf_param (fun p => fun z => ret (γ2 ⟨p, z⟩))) as [γ3 Hγ3].
    destruct (epf_param (fun x => fun y => ret (γ3 ⟨x, y⟩))) as [γ4 Hγ4].
    destruct (epf (fun x => ret (γ4 x))) as [e He].
    exists e. intros x. exists (γ4 x). split.
    apply He. apply ret_hasvalue. intros y. exists (γ3 ⟨x, y⟩). split.
    apply Hγ4. apply ret_hasvalue. intros z. exists (γ2 ⟨⟨x, y⟩, z⟩). split.
    apply Hγ3. apply ret_hasvalue. intros u. 
    simpl. simp eval. simpl. 
    intros H1. exists (γ1 ⟨⟨⟨x, y⟩, z⟩, u⟩). split.
    apply Hγ2. apply ret_hasvalue. intros v H2. exists 0. split. 
    apply Hγ1. apply ret_hasvalue.
    rewrite H1. assumption.
  Qed.
  
  Lemma realizes_ax_succ_congr (α : env nat) : exists e, e ⊩[α] ax_succ_congr.
  Proof.
    destruct (epf_param (fun _ => fun _ => ret 0)) as [γ1 Hγ1].
    destruct (epf_param (fun x => fun y => ret (γ1 ⟨x, y⟩))) as [γ2 Hγ2].
    destruct (epf (fun x => ret (γ2 x))) as [e He].
    exists e. intros x. exists (γ2 x). split.
    apply He. apply ret_hasvalue. intros y. exists (γ1 ⟨x, y⟩). split.
    apply Hγ2. apply ret_hasvalue. intros h. simpl. simp eval. simpl.
    intros H. exists 0. split. apply Hγ1. apply ret_hasvalue.
    f_equal. assumption.
  Qed.

  Lemma realizes_ax_add_congr (α : env nat) : exists e, e ⊩[α] ax_add_congr.
    destruct (epf_param (fun _ => fun _ => ret 0)) as [γ1 Hγ1].
    destruct (epf_param (fun r => fun v => ret (γ1 ⟨r, v⟩))) as [γ2 Hγ2].
    destruct (epf_param (fun q => fun u => ret (γ2 ⟨q, u⟩))) as [γ3 Hγ3].
    destruct (epf_param (fun p => fun z => ret (γ3 ⟨p, z⟩))) as [γ4 Hγ4].
    destruct (epf_param (fun x => fun y => ret (γ4 ⟨x, y⟩))) as [γ5 Hγ5].
    destruct (epf (fun x => ret (γ5 x))) as [e He].
    exists e. intros x. exists (γ5 x). split.
    apply He. apply ret_hasvalue. intros y. 
    exists (γ4 ⟨x, y⟩). split.
    apply Hγ5. apply ret_hasvalue. intros z.
    exists (γ3 ⟨⟨x, y⟩, z⟩). split.
    apply Hγ4. apply ret_hasvalue. intros u. 
    simpl. simp eval. simpl.
    exists (γ2 ⟨⟨⟨x, y⟩, z⟩, u⟩). split. 
    apply Hγ3. apply ret_hasvalue. intros v. 
    intros H1. 
    exists (γ1 ⟨⟨⟨⟨x, y⟩, z⟩, u⟩, v⟩). split.
    apply Hγ2. apply ret_hasvalue. intros w H2. 
    exists 0. split. 
    apply Hγ1. apply ret_hasvalue.
    rewrite H1. rewrite H2. reflexivity.
  Qed.

  Lemma realizes_ax_mult_congr (α : env nat) : exists e, e ⊩[α] ax_mult_congr.
    destruct (epf_param (fun _ => fun _ => ret 0)) as [γ1 Hγ1].
    destruct (epf_param (fun r => fun v => ret (γ1 ⟨r, v⟩))) as [γ2 Hγ2].
    destruct (epf_param (fun q => fun u => ret (γ2 ⟨q, u⟩))) as [γ3 Hγ3].
    destruct (epf_param (fun p => fun z => ret (γ3 ⟨p, z⟩))) as [γ4 Hγ4].
    destruct (epf_param (fun x => fun y => ret (γ4 ⟨x, y⟩))) as [γ5 Hγ5].
    destruct (epf (fun x => ret (γ5 x))) as [e He].
    exists e. intros x. exists (γ5 x). split.
    apply He. apply ret_hasvalue. intros y. 
    exists (γ4 ⟨x, y⟩). split.
    apply Hγ5. apply ret_hasvalue. intros z.
    exists (γ3 ⟨⟨x, y⟩, z⟩). split.
    apply Hγ4. apply ret_hasvalue. intros u. 
    simpl. simp eval. simpl.
    exists (γ2 ⟨⟨⟨x, y⟩, z⟩, u⟩). split. 
    apply Hγ3. apply ret_hasvalue. intros v. 
    intros H1. 
    exists (γ1 ⟨⟨⟨⟨x, y⟩, z⟩, u⟩, v⟩). split.
    apply Hγ2. apply ret_hasvalue. intros w H2. 
    exists 0. split. 
    apply Hγ1. apply ret_hasvalue.
    rewrite H1. rewrite H2. reflexivity.
  Qed.

  Lemma realizes_ax_add_zero (α : env nat) : exists e, e ⊩[α] ax_add_zero.
  Proof.
    destruct (epf (fun _ => ret 0)) as [e He].
    exists e. intros x. 
    exists 0. split. 
    apply He. apply ret_hasvalue.
    simp eval. simpl. reflexivity.
  Qed.

  Lemma realizes_ax_add_rec (α : env nat) : exists e, e ⊩[α] ax_add_rec. 
  Proof.
    destruct (epf_param (fun _ => fun _ => ret 0)) as [γ Hγ].
    destruct (epf (fun x => ret (γ x))) as [e He].
    exists e. intros x.
    exists (γ x). split. 
    apply He. apply ret_hasvalue. 
    exists 0. split. 
    apply Hγ. apply ret_hasvalue.
    simpl. simp eval. simpl. reflexivity.
  Qed.

  Lemma realizes_ax_mult_zero (α : env nat): exists e, e ⊩[α] ax_mult_zero.
  Proof.
    destruct (epf (fun _ => ret 0)) as [e He].
    exists e. intros x. 
    exists 0. split. 
    apply He. apply ret_hasvalue.
    simp eval. simpl. reflexivity.
  Qed.

  Lemma realizes_ax_mult_rec (α : env nat): exists e, e ⊩[α] ax_mult_rec.
  Proof.
    destruct (epf_param (fun _ => fun _ => ret 0)) as [γ Hγ].
    destruct (epf (fun x => ret (γ x))) as [e He].
    exists e. intros x.
    exists (γ x). split. 
    apply He. apply ret_hasvalue. 
    exists 0. split. 
    apply Hγ. apply ret_hasvalue.
    simpl. simp eval. simpl. reflexivity.
  Qed.

  Lemma realizes_ax_zero_succ (α : env nat): exists e : nat, e ⊩[α] ax_zero_succ.
  Proof.
    destruct (epf (fun _ => ret 0)) as [e He].
    exists e. intros x. 
    exists 0. split. 
    apply He. apply ret_hasvalue.
    simpl. simp eval. simpl. intros ? contra. 
    inversion contra. 
  Qed.


  Lemma realizes_ax_succ_inj (α : env nat): exists e : nat, e ⊩[α] ax_succ_inj.
  Proof.
    destruct (epf_param (fun _ => fun _ => ret 0)) as [γ1 Hγ1].
    destruct (epf_param (fun x => fun y => ret (γ1 ⟨x, y⟩))) as [γ2 Hγ2].
    destruct (epf (fun x => ret (γ2 x))) as [e He].
    exists e. intros x. exists (γ2 x). split.
    apply He. apply ret_hasvalue. intros y. exists (γ1 ⟨x, y⟩). split.
    apply Hγ2. apply ret_hasvalue. intros h. simpl. simp eval. simpl.
    intros H. exists 0. split. apply Hγ1. apply ret_hasvalue.
    injection H as H. assumption.
  Qed.

  Lemma realizes_ax_induction (φ : form) (α : env nat): exists e : nat, e ⊩[α] ax_induction φ.
  Proof.
    destruct (epf_param (fun! ⟨z, i⟩ => fix ind (n : nat) {struct n} : part nat :=
                                          match n with 
                                          | 0   => ret z 
                                          | S m => bind (θ i m) 
                                                    (fun v => bind (ind m) (fun u => θ v u))
                                          end)) as [γ1 Hγ1].
    destruct (epf_param (fun z => fun i => ret (γ1 ⟨z, i⟩))) as [γ2 Hγ2].
    destruct (epf (fun z => ret (γ2 z))) as [e He].
    exists e. intros z Hz.
    exists (γ2 z). split. 
    apply He. apply ret_hasvalue. intros i Hi.
    exists (γ1 ⟨z, i⟩). split.
    apply Hγ2. apply ret_hasvalue.
    intros x. induction x as [| m Hm].
    {
      exists z. split. 
      apply Hγ1. rewrite embedP. apply ret_hasvalue.
      eapply realizes_subst in Hz.
      eapply realizes_ext_iff. 2: apply Hz.
      destruct x. 
      all : simpl; simp eval; reflexivity.
    }
    {
      simpl in Hi. destruct (Hi m) as (v & Hvalv & Hrealv). 
      destruct Hm as (u & Hvalu & Hrealu).
      destruct (Hrealv u Hrealu) as (w & Hvalw & Hrealw).
      exists w. split.
      apply Hγ1. rewrite embedP. 
      apply bind_hasvalue. exists v. split; try assumption.
      apply bind_hasvalue. exists u. split; try assumption.
      apply Hγ1 in Hvalu. rewrite embedP in Hvalu; assumption.
      eapply realizes_subst in Hrealw.
      eapply realizes_ext_iff. 2: apply Hrealw.
      destruct x.
      all : simpl; simp eval; reflexivity.   
    }
  Qed.

  Lemma realizes_ax_cases (α : env nat) : exists e, e ⊩[α] ax_cases.
  Proof.
    unfold ax_cases.
    destruct (epf (fun x => match x with 
                            | 0   => ret ⟨0, 0⟩
                            | S n => ret ⟨1, ⟨n, 0⟩⟩
                            end)) as [e He].
    exists e. intros [].
    - exists ⟨0, 0⟩. split.
      apply He. apply ret_hasvalue.
      left. exists 0. split; reflexivity.
    - exists ⟨1, ⟨n, 0⟩⟩. split.
      apply He. apply ret_hasvalue.
      right. exists ⟨ n, 0 ⟩. split.
      reflexivity.
      exists n. exists 0. split; reflexivity.
  Qed.

  Lemma realizes_Qeq (φ : form) (α : env nat) : In φ Qeq -> exists e, e ⊩[α] φ.
  Proof.
    intros Hin.
    unfold_goals_list; rewrite <- H.
    - apply realizes_ax_refl.
    - apply realizes_ax_sym.
    - apply realizes_ax_trans.
    - apply realizes_ax_succ_congr.
    - apply realizes_ax_add_congr. 
    - apply realizes_ax_mult_congr. 
    - apply realizes_ax_add_zero. 
    - apply realizes_ax_add_rec. 
    - apply realizes_ax_mult_zero. 
    - apply realizes_ax_mult_rec. 
    - apply realizes_ax_zero_succ.
    - apply realizes_ax_succ_inj.
    - apply realizes_ax_cases. 
  Qed.

  Lemma realizes_PAeq (φ : form) : PAeq φ -> exists e : nat, e ⊩ φ.
    induction 1.
    simpl in H.
    unfold_goals.
    - apply realizes_ax_refl.
    - apply realizes_ax_sym.
    - apply realizes_ax_trans.
    - apply realizes_ax_succ_congr.
    - apply realizes_ax_add_congr. 
    - apply realizes_ax_mult_congr. 
    - apply realizes_ax_add_zero. 
    - apply realizes_ax_add_rec. 
    - apply realizes_ax_mult_zero. 
    - apply realizes_ax_mult_rec. 
    - apply realizes_ax_zero_succ.
    - apply realizes_ax_succ_inj.
    - apply realizes_ax_induction. 
  Qed.


End RealizingAxioms.

(** ** Encoding Intuitionistic Robinson Arithmetic *)

Section EncodeQeq.

Lemma bounded_Qeq : bounded_L 0 Qeq.
Proof.
  intros φ Hin.
  unfold_goals_list.
  all : solve_bounded_closed.
Qed.

Lemma encode_Qeq (α : env nat) : exists code_Γ, code_Γ ⊩ctx[α] Qeq.
Proof.
  destruct (realizes_ax_refl α) as [c1 H1].
  destruct (realizes_ax_sym α) as [c2 H2].
  destruct (realizes_ax_trans α) as [c3 H3].
  destruct (realizes_ax_succ_congr α) as [c4 H4].
  destruct (realizes_ax_add_congr α) as [c5 H5].
  destruct (realizes_ax_mult_congr α) as [c6 H6].
  destruct (realizes_ax_add_zero α) as [c7 H7].
  destruct (realizes_ax_add_rec α) as [c8 H8].
  destruct (realizes_ax_mult_zero α) as [c9 H9].
  destruct (realizes_ax_mult_rec α) as [c10 H10].
  destruct (realizes_ax_zero_succ α) as [c11 H11].
  destruct (realizes_ax_succ_inj α) as [c12 H12].
  destruct (realizes_ax_cases α) as [c13 H13].
  exists ⟨c1, ⟨c2, ⟨c3, ⟨c4, ⟨c5, ⟨c6, ⟨c7, ⟨c8, ⟨c9, ⟨c10, ⟨c11, ⟨c12, ⟨c13, 0⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩.
  exists c1; split; try assumption.
  exists ⟨c2, ⟨c3, ⟨c4, ⟨c5, ⟨c6, ⟨c7, ⟨c8, ⟨c9, ⟨c10, ⟨c11, ⟨c12, ⟨c13, 0⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩; split; try reflexivity.
  exists c2; split; try assumption.
  exists ⟨c3, ⟨c4, ⟨c5, ⟨c6, ⟨c7, ⟨c8, ⟨c9, ⟨c10, ⟨c11, ⟨c12, ⟨c13, 0⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩; split; try reflexivity.
  exists c3; split; try assumption.
  exists ⟨c4, ⟨c5, ⟨c6, ⟨c7, ⟨c8, ⟨c9, ⟨c10, ⟨c11, ⟨c12, ⟨c13, 0⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩; split; try reflexivity.
  exists c4; split; try assumption.
  exists ⟨c5, ⟨c6, ⟨c7, ⟨c8, ⟨c9, ⟨c10, ⟨c11, ⟨c12, ⟨c13, 0⟩⟩⟩⟩⟩⟩⟩⟩⟩; split; try reflexivity.
  exists c5; split; try assumption.
  exists ⟨c6, ⟨c7, ⟨c8, ⟨c9, ⟨c10, ⟨c11, ⟨c12, ⟨c13, 0⟩⟩⟩⟩⟩⟩⟩⟩; split; try reflexivity.
  exists c6; split; try assumption.
  exists ⟨c7, ⟨c8, ⟨c9, ⟨c10, ⟨c11, ⟨c12, ⟨c13, 0⟩⟩⟩⟩⟩⟩⟩; split; try reflexivity.
  exists c7; split; try assumption.
  exists ⟨c8, ⟨c9, ⟨c10, ⟨c11, ⟨c12, ⟨c13, 0⟩⟩⟩⟩⟩⟩; split; try reflexivity.
  exists c8; split; try assumption.
  exists ⟨c9, ⟨c10, ⟨c11, ⟨c12, ⟨c13, 0⟩⟩⟩⟩⟩; split; try reflexivity.
  exists c9; split; try assumption.
  exists ⟨c10, ⟨c11, ⟨c12, ⟨c13, 0⟩⟩⟩⟩; split; try reflexivity.
  exists c10; split; try assumption.
  exists ⟨c11, ⟨c12, ⟨c13, 0⟩⟩⟩; split; try reflexivity.
  exists c11; split; try assumption.
  exists ⟨c12, ⟨c13, 0⟩⟩; split; try reflexivity.
  exists c12; split; try assumption.
  exists ⟨c13, 0⟩. split.
  exists c13. split; try assumption.
  exists 0. split; try apply I.
  all : reflexivity. 
Qed.

End EncodeQeq.

End NumberRealizability.
