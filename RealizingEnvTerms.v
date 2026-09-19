From SyntheticComputability Require Import EPF partial equiv_on Definitions reductions embed_nat.
From Stdlib Require Import Lia Arith Vector.
From Equations Require Import Equations.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Program.Equality.

Import EmbedNatNotations.

From Stdlib Require Import List.
Import ListNotations.

From NumberRealizability Require Import Core Facts.

Section NumberRealizability.

  Variable Part : partiality.
  Variable θ : nat -> nat ↛ nat.
  Variable epf : EPF_nonparam_for θ.
  Variable epf_param : EPF_for θ.

(** Realizing environments *)

Definition realizes_env n code_α α :=
  code_α = fold_right (fun a b => embed (a, b)) 0 (map α (seq 0 n))
  
  /\ forall m, m >= n -> α m = 0. (* finite environment *)

Local Notation "code ⊩env[ n ] α" :=
  (realizes_env n code α)
  (at level 70, format "code  ⊩env[ n ]  α").

Section EnvironmentRealizability.


Lemma zero_realizes_triv_env :
  0 ⊩env[0] (fun _ => 0).
Proof.
  unfold realizes_env. cbn. tauto.
Qed.


Lemma map_scons (α : env nat) (x n : nat) : 
  map (x .: α) (seq 1 n) = map α (seq 0 n).
Proof.
  apply nth_ext with (d := (x .: α) 1) (d' := α 0).
  - repeat rewrite length_map. 
    repeat rewrite length_seq.
    reflexivity. 
  - rewrite length_map. 
    rewrite length_seq.
    intros m Hle.
    rewrite (map_nth (x .: α) (seq 1 n) 1 m).
    rewrite (map_nth α (seq 0 n) 0 m).
    rewrite (seq_nth 1 1 Hle).
    rewrite (seq_nth 0 0 Hle).
    reflexivity.
Qed.

Lemma env_fin_S (α : env nat) (x n : nat) : 
  (forall m : nat, m >= n -> α m = 0) ->
    forall m : nat, m >= S n -> (x .: α) m = 0.
Proof.
  intros H m Hm.
  destruct m.
  inversion Hm.
  simpl. apply H. lia.
Qed.

Lemma realizes_env_S (α : env nat) (x n code_α: nat) :
  code_α ⊩env[n] α -> ⟨x, code_α⟩ ⊩env[S n] (x .: α).
Proof.
  unfold realizes_env. cbn.
  intros [H Hfin].
  rewrite map_scons.
  split.
  rewrite H.
  reflexivity.
  apply env_fin_S; assumption.
Qed.


Fixpoint decode_env_to_list (code_α len : nat) : list nat := 
  match len with 
  | 0 => []
  | S n => fst (unembed code_α) :: decode_env_to_list (snd (unembed code_α)) n 
  end.


Lemma map_env_shift (α : env nat) (n : nat) : 
  map (fun x : nat => α (1 + x)) (seq 0 n) = map α (seq 1 n).
Proof.
  apply nth_ext with (d := α 1) (d' := α 0).
  - repeat rewrite length_map. 
    repeat rewrite length_seq.
    reflexivity.
  - rewrite length_map.
    rewrite length_seq.
    intros m Hle.
    change (α 1) with ((fun x : nat => α (1 + x)) 0).
    repeat rewrite map_nth. 
    repeat erewrite seq_nth; try assumption.
    reflexivity.
Qed.

Lemma decode_map_seq (α : env nat) (code_α n : nat) :
  code_α ⊩env[n] α -> decode_env_to_list code_α n = map α (seq 0 n).
Proof.
  induction n as [| n IH] in α, code_α |-*.
  - reflexivity.
  - unfold realizes_env in *.
    simpl. intros [H Hfin].
    rewrite H. rewrite embedP. 
    simpl. f_equal.
    specialize (IH (fun x => α (1 + x)) (fold_right (fun a b : nat => ⟨ a, b ⟩) 0 (map α (seq 1 n)))).
    erewrite <- map_scons in IH. 
    rewrite <- map_env_shift in IH.
    erewrite <- map_scons in IH.
    assert (Hge : forall m : nat, m >= n -> α (1 + m) = 0).
    { simpl. intros m Hle. apply Hfin. lia. }
    specialize (IH (conj eq_refl Hge)).
    rewrite <- map_env_shift.
    erewrite <- map_scons.
    apply IH.
    Unshelve.
    exact (α 0).
Qed.

Lemma realizes_env_ge (α : env nat) (code_α n : nat) :
  code_α ⊩env[n] α -> forall m, n <= m -> code_α ⊩env[m] α.
Proof.
  unfold realizes_env.
  intros [Henv Hfin] m Hge.
  split.
  2: { firstorder lia. }
  eapply numbers.Nat.le_sum in Hge as [z ->].
  rewrite seq_app, map_app, fold_right_app.
  replace ((fold_right (fun a b : nat => ⟨ a, b ⟩) 0 (map α (seq (0 + n) z)))) with 0.
  assumption.
  clear - Hfin. symmetry.
  induction z in n, Hfin |- *.
  - cbn. reflexivity.
  - cbn. rewrite Hfin. 2: lia.
    cbn in IHz. rewrite IHz. reflexivity.
    firstorder lia.
Qed.

Lemma map_env_seq (α : env nat) (x n : nat) : 
  map (x .: α) (seq 0 (S n)) = x :: map α (seq 0 n).
Proof.
  change (seq 0 (S n)) with (0 :: seq 1 n). 
  rewrite <- (seq_shift n 0).
  cbn [map]. rewrite map_map. reflexivity. 
Qed.
  

Lemma realizes_env_S_inv (α : env nat) (x n codeS : nat) :
  codeS ⊩env[S n] (x .: α) ->
  (snd (unembed codeS) ⊩env[n] α /\ codeS = ⟨x, snd (unembed codeS)⟩).
Proof.
  unfold realizes_env. intros [Hcode Hzero].
  rewrite Hcode.
  rewrite map_env_seq.
  cbn [fold_right].
  rewrite embedP.
  cbn [snd].
  repeat split.
  intros m Hm. 
  specialize (Hzero (S m) (le_n_S _ _ Hm)).
  simpl in Hzero. 
  assumption.
Qed.

Lemma env_proj_ext (α : env nat) (code_α n : nat) :
  code_α ⊩env[n] α ->
  forall m, α m = (fun m : nat => nth m (decode_env_to_list code_α n) 0) m.
Proof.
  intros Henv m.
  erewrite decode_map_seq; try eassumption.
  destruct Henv as [Heq Hfin].
  destruct (Nat.lt_ge_cases m n) as [Hmn | Hmn].
  - erewrite nth_indep with (d' := α 0).
    2: rewrite length_map, length_seq; lia.
    rewrite map_nth.
    rewrite seq_nth; [reflexivity | assumption].
  - rewrite nth_overflow.
    2: rewrite length_map, length_seq; lia.
    apply Hfin; assumption.
Qed.

Lemma eval_env_proj_S (α : env nat) (t : term) (y n code_α : nat) :
  code_α ⊩env[n] α ->
    eval (y .: α) t = eval (y .: (fun m : nat => nth m (decode_env_to_list code_α n) 0)) t.
Proof.
  intros Henv. eapply eval_term_ext. intros []. 
    + reflexivity.
    + eapply realizes_env_S in Henv as HcodeS. 
      erewrite env_proj_ext; try eassumption. cbn.
  rewrite embedP. reflexivity.
Qed. 


(** Realizing terms *)

End EnvironmentRealizability.

Section TermRealizability.

Lemma realize_terms (t : term) (n : nat) : 
  bounded_t n t -> 
  exists r : nat, 
    forall α : env nat, 
    forall code_α : nat,
    code_α ⊩env[n] α ->
    exists u, 
      θ r code_α =! u /\ eval α t = u. 
Proof.
  intros Hbnd. 
  induction t.
  - (* Base case : variable *) 
    destruct (epf (fun code_α => ret (nth x (decode_env_to_list code_α n) 0))) as [r Hr]. (* projections *)
    exists r.
    intros α code_α Henv.
    exists (α x).
    split; try reflexivity.
    inversion Hbnd. subst.
    apply Hr. 
    rewrite (decode_map_seq Henv).
    erewrite nth_indep with (d' := α 0);
      try erewrite length_map;
      try erewrite length_seq; 
      try assumption. 
    rewrite map_nth.
    rewrite seq_nth; try assumption.
    apply ret_hasvalue.   
  - induction F.
    + (* Zero *)
      destruct (epf (fun code_α => ret 0)) as [r Hr].
      exists r. 
      intros α code_α Henv.
      exists 0.
      split; try reflexivity.
      apply Hr.
      apply ret_hasvalue.
    + (* Succ *)
      dependent destruction Hbnd.
      dependent elimination v. 
      dependent elimination t0.
      destruct (IH h (In_cons_hd _ _) (H h (In_cons_hd _ _))) as (r & Hr).
      destruct (epf (fun code_α => 
                        bind (θ r code_α) (fun u => ret (S u)))) as [c Hc].
      exists c.
      intros α code_α Henv.
      destruct (Hr α code_α Henv) as (u & Hvalu & Hevalu).
      exists (S u).
      split.
      apply Hc. apply bind_hasvalue.
      exists u. 
      split; [assumption | apply ret_hasvalue].
      simp eval; subst; reflexivity.
    + (* Plus *)
      dependent destruction Hbnd.
      dependent elimination v.
      repeat dependent elimination t0.
      destruct (IH h (In_cons_hd _ _) (H h (In_cons_hd _ _))) as (r & Hr).
      destruct (IH h0 (In_cons_tl _ _ _ (In_cons_hd _ _) ) (H h0 (In_cons_tl _ _ _ (In_cons_hd _ _)))) as (s & Hs).
      destruct (epf (fun code_α =>
                      bind (θ r code_α) 
                        (fun u => bind (θ s code_α)
                                    (fun v => ret (u + v))))) as [c Hc].
      exists c.
      intros α code_α Henv.
      destruct (Hr α code_α Henv) as (u & Hvalu & Hevalu).
      destruct (Hs α code_α Henv) as (v & Hvalv & Hevalv).
      exists (u + v).
      split.
      apply Hc. apply bind_hasvalue.
      exists u.
      split; [assumption |].
      apply bind_hasvalue.
      exists v.
      split; [assumption | apply ret_hasvalue].
      simp eval; subst; reflexivity.
    + (* Mult *)
      dependent destruction Hbnd.
      dependent elimination v.
      repeat dependent elimination t0.
      destruct (IH h (In_cons_hd _ _) (H h (In_cons_hd _ _))) as (r & Hr).
      destruct (IH h0 (In_cons_tl _ _ _ (In_cons_hd _ _) ) (H h0 (In_cons_tl _ _ _ (In_cons_hd _ _)))) as (s & Hs).
      destruct (epf (fun code_α =>
                      bind (θ r code_α) 
                        (fun u => bind (θ s code_α)
                                    (fun v => ret (u * v))))) as [c Hc].
      exists c.
      intros α code_α Henv.
      destruct (Hr α code_α Henv) as (u & Hvalu & Hevalu).
      destruct (Hs α code_α Henv) as (v & Hvalv & Hevalv).
      exists (u * v).
      split.
      apply Hc. apply bind_hasvalue.
      exists u.
      split; [assumption |].
      apply bind_hasvalue.
      exists v.
      split; [assumption | apply ret_hasvalue].
      simp eval; subst; reflexivity.
Qed.

End TermRealizability.

End NumberRealizability.
