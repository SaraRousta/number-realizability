From SyntheticComputability Require Import EPF partial equiv_on Definitions reductions embed_nat.
From Stdlib Require Import Lia Vector.
From FOL Require Import FullSyntax Arithmetics.

Import EmbedNatNotations.

From Stdlib Require Import List.
Import ListNotations.

From NumberRealizability Require Import LogicalFacts Core Facts RealizingEnvTerms BoundedTactics.

(** * Soundness and Consistency for Intuitionistic ND *)

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

(** ** Soundness *)

Section Soundness.

(** Soundness *)


Lemma realizes_sound_ND {f : falsity_flag} (Γ : list form) (φ : form) (n : nat) : 
    bounded_L n (φ :: Γ) ->
    Γ ⊢I φ -> 
    exists code_φ : nat,
      forall α : env nat,
      forall code_α : nat,
      code_α ⊩env[n] α ->
      forall code_Γ : nat,
      code_Γ ⊩ctx[α] Γ ->
      exists u : nat, θ code_φ ⟨code_α, code_Γ⟩ =! u /\ u ⊩[α] φ.
Proof with try reflexivity.
  intros Hbdd Hprv.
  remember intu as peirce_flag.
  induction Hprv as
    [ ff p Γ φ ψ Hprv IHHprv
    | ff p Γ φ ψ Hprv1 IHHprv1 Hprv2 IHHprv2
    | ff p Γ φ Hprv IHHprv
    | ff p Γ t φ Hprv IHHprv
    | ff p Γ t φ Hprv IHHprv
    | ff p Γ φ ψ Hprv1 IHHprv1 Hprv2 IHHprv2
    | p Γ φ Hprv IHHprv
    | ff p Γ φ H
    | ff p Γ φ ψ Hprv1 IHHprv1 Hprv2 IHHprv2
    | ff p Γ φ ψ Hprv IHHprv
    | ff p Γ φ ψ Hprv IHHprv
    | ff p Γ φ ψ Hprv IHHprv
    | ff p Γ φ ψ Hprv IHHprv
    | ff p Γ φ ψ χ Hprv1 IHHprv1 Hprv2 IHHprv2
        Hprv3 IHHprv3
    | ff Γ φ ψ
    ] in Hbdd, n, Heqpeirce_flag |-*; subst.
     { 
      (* →-intro *)
      destruct (IHHprv n) as [c H]...
      - solve_bounded.
      - destruct (epf_param (fun! ⟨code_α , code_Γ⟩ => fun code_φ => θ c ⟨code_α, ⟨code_φ , code_Γ⟩⟩)) as [γ Hγ].
        destruct (epf (fun! ⟨code_α , code_Γ⟩ => ret (γ ⟨code_α , code_Γ⟩))) as [e He].
        exists e.
        intros α code_α Henv code_Γ Hctx. 
        exists (γ ⟨code_α, code_Γ⟩).
        split.
        + apply He. rewrite embedP. apply ret_hasvalue.
        + simpl. intros m Hφ.
          destruct (H α code_α Henv ⟨m, code_Γ⟩) as (v & Hvalv & Hrealv).  
          {
            exists m. split. apply Hφ. exists code_Γ. split. apply Hctx. reflexivity.
          }
          exists v. 
          split.
          * apply Hγ. rewrite embedP. apply Hvalv.        
          * apply Hrealv.
      }
     { 
        (* →-elim *)
        destruct (find_bounded φ) as [m Hmφ].
        destruct (IHHprv1 (Nat.max n m)) as [c Hc]...
        { solve_bounded. }
        destruct (IHHprv2 (Nat.max n m)) as [e He]...
        { solve_bounded. }
        destruct (epf (fun! ⟨code_α, code_Γ⟩ => bind (θ c ⟨code_α, code_Γ⟩) (fun v => bind (θ e ⟨code_α, code_Γ⟩) (fun u => θ v u)))) as [d Hd].
        exists d.
        intros α code_α Henv code_Γ Hctx.
        assert (Henvmax : code_α ⊩env[Nat.max n m] α).
        { apply realizes_env_ge with (Part := Part) (θ := θ) (n := n); try assumption; lia. }
      
        destruct (Hc α code_α Henvmax code_Γ Hctx) as (v & Hvalv & Hrealv). 
        destruct (He α code_α Henvmax code_Γ Hctx) as (u & Hvalu & Hrealu).
        simpl in Hrealv. 
        destruct (Hrealv u Hrealu) as (w & Hvalvw & Hrealw).
        exists w.
        split.
        + apply Hd. rewrite embedP. apply bind_hasvalue.
          exists v. split. apply Hvalv. 
          apply bind_hasvalue. 
          exists u. split.
          apply Hvalu. apply Hvalvw.
        + apply Hrealw.
      }
     {  
        (* ∀-intro *)
        destruct (IHHprv (S n)) as [c H]...
        - solve_bounded.
        - destruct (epf_param (fun! ⟨code_α, code_Γ⟩ => fun x => bind (θ c ⟨⟨x, code_α⟩, code_Γ⟩) (fun v => (ret v)))) as [γ Hγ]. 
        (* realizes φ in the extended environment (x .: α) *)
          destruct (epf (fun! ⟨code_α, code_Γ⟩ => ret (γ ⟨code_α, code_Γ⟩))) as [e He].
          exists e.
          intros α code_α Henv code_Γ Hctx.
          exists (γ ⟨code_α, code_Γ⟩).
          split.
          + apply He. rewrite embedP. apply ret_hasvalue.
          + simpl. intros x. 
            destruct (H (x .: α) ⟨x, code_α⟩ (realizes_env_S _ Henv) code_Γ) as (v & Hvalv & Hrealv).
            {
              apply realizes_subst_ctx. 
              apply Hctx.  
            }
            exists v.
            split.
            apply Hγ. rewrite embedP. apply bind_hasvalue. 
            exists v.
            split. apply Hvalv. apply ret_hasvalue.
            apply Hrealv.   
      }
      {
        (* ∀-elim *)
        repeat decompose_bounded.
        destruct (find_bounded (∀ φ)) as [nφ ?].
        destruct (find_bounded_t t) as [nt ?].
        set (m := Nat.max n (Nat.max nφ nt)).

        assert (Hm : bounded_L m (∀ φ :: Γ)) by repeat prove_bounded.

        assert (Ht : bounded_t m t) by repeat solve_bounded.

        destruct ( @realize_terms _ θ epf t m Ht) as (r & Hr).
        destruct (IHHprv m Hm) as [c IH]...
        destruct (epf (fun! ⟨code_α, code_Γ⟩ => 
                          bind (θ c ⟨code_α, code_Γ⟩) 
                            (fun v => bind (θ r code_α) (fun u => θ v u)))) 
        as [e He].
        exists e.

        intros α code_α ? code_Γ Hctx.
        assert (code_α ⊩env[m] α) as Henv.
        { apply realizes_env_ge with (Part := Part) (θ := θ) (n := n); try assumption; lia. }

        destruct (Hr α code_α Henv) as (u & Hvalu & Hequ).
        destruct (IH α code_α Henv code_Γ Hctx) as (v & Hvalv & Hrealv).
        destruct (Hrealv u) as (w & Hvalw & Hrealw).
        exists w.
        split.
        + apply He.
          rewrite embedP.
          apply bind_hasvalue.
          exists v.
          split; try assumption.
          apply bind_hasvalue.
          exists u; split; try assumption.
        + apply realizes_subst.
          erewrite realizes_ext_iff; try apply Hrealw.
          destruct x; try assumption; try reflexivity.
      }
      { 
        (* ∃-intro *)
        destruct (find_bounded_t t) as [m Hmt].
        destruct (IHHprv (Nat.max (S n) m)) as [c H]...
        - solve_bounded.
        - destruct ( @realize_terms _ θ epf t (Nat.max (S n) m) ) as (r & Hr).
        { solve_bounded. } 
        destruct (epf (fun! ⟨code_α, code_Γ⟩ => 
                        bind (θ c ⟨code_α, code_Γ⟩) 
                          (fun v => bind (θ r code_α) (fun u => ret ⟨u, v⟩))))
        as [e He].
        exists e.
        intros α code_α Henv code_Γ Hctx.

        assert (Henvmax : code_α ⊩env[Nat.max (S n) m] α).
        { apply realizes_env_ge with (Part := Part) (θ := θ) (n := n); try lia; try assumption. }

        destruct (Hr α code_α Henvmax) as (u & Hvalu & Hequ).
        destruct (H α code_α Henvmax code_Γ Hctx) as (v & Hvalv & Hrealv).
        exists ⟨u, v⟩.
        split.
        apply He. rewrite embedP. apply bind_hasvalue.
        exists v.
        split.
        apply Hvalv. apply bind_hasvalue. 
        exists u.
        split; try assumption.
        apply ret_hasvalue.
        simpl.
        exists u. exists v.
        split; try reflexivity.
        apply realizes_subst in Hrealv.
        erewrite realizes_ext_iff; try apply Hrealv.
        destruct x; try symmetry; try assumption; try reflexivity.
      }
      { 
        (* ∃-elim *)
        repeat decompose_bounded.
        destruct (find_bounded (∃ φ)) as [neφ ?].
        destruct (find_bounded φ) as [nφ ?].
        set (m := S (Nat.max n (Nat.max nφ neφ))).

        assert (Hm : bounded_L m (∃ φ :: Γ)) by repeat prove_bounded.

        destruct (IHHprv1 m Hm) as [c Hc]...

        destruct (IHHprv2 m) as [e He]...
        { repeat prove_bounded. 
          assert (bounded (Nat.max n (Nat.max nφ neφ)) ψ) by prove_bounded.
          eapply subst_bounded_max; try eassumption. 
          intros; econstructor; lia. }

        destruct (epf (fun! ⟨code_α, code_Γ⟩ => 
                        bind (θ c ⟨code_α, code_Γ⟩) 
                          (fun! ⟨x, y⟩ => 
                            bind (θ e ⟨⟨x, code_α⟩, ⟨y , code_Γ⟩⟩) 
                              (fun u => ret u)))) as [d Hd].
        
        exists d.
        intros α code_α Henv code_Γ Hctx.
        
        edestruct (Hc α code_α) as (v & Hvalv & Hrealv); try apply Henv; try apply Hctx.
        { apply realizes_env_ge with (Part := Part) (θ := θ) (n := n); try assumption; try apply Henv; lia. }
        
        destruct Hrealv as (x & y & Hrealy & Hxy).

        unshelve edestruct He as (u & Hvalu & Hrealu).
        - exact (x .: α).
        - exact ⟨x, code_α⟩.
        - exact ⟨y, code_Γ⟩.
        - apply realizes_env_ge with (Part := Part) (θ := θ) (n := S n); try lia; try assumption.
          apply realizes_env_S; assumption.
        - simpl. exists y. 
          split; try assumption.  
          exists code_Γ. split; [ | reflexivity ].
          rewrite realizes_subst_ctx.
          erewrite realizes_ext_iff_ctx; [ apply Hctx | ].
          reflexivity.
        
        - exists u. split.
          apply Hd. rewrite embedP.
          apply bind_hasvalue.
          exists v. split; [ assumption | ]. 
          subst. rewrite embedP. apply bind_hasvalue.
          exists u. split; [ assumption | apply ret_hasvalue ].

          rewrite realizes_subst in Hrealu.
          eapply realizes_ext_iff; [| apply Hrealu ].
          reflexivity.
      }
      {
        (* exfalso *)
        destruct (IHHprv n) as [c Hc]...
        { solve_bounded. constructor. }
        exists c.
        intros α code_α Henv code_Γ Hctx.
        destruct (Hc α code_α Henv code_Γ Hctx) as (v & H & Hfalse).
        destruct Hfalse.
      }
      {
        (* Axiom *)
        induction Γ as [| ψ Δ IHΔ].
        - inversion H.
        - destruct H.
          + destruct (epf (fun! ⟨code_α, code_Γ⟩ => 
                            ret (fst (unembed code_Γ)))) as [c Hc].
            exists c.
            intros α code_α Henv code_Γ Hctx.
            destruct Hctx as (c1 & Hc1 & c2 & Hctx & Heq).
            subst. 
            exists c1.
            split; [| assumption].
            apply Hc. rewrite embedP. 
            rewrite embedP. 
            apply ret_hasvalue.  
          + destruct IHΔ as [c Hc]; [solve_bounded | assumption |].
            destruct (epf (fun! ⟨code_α, code_Γ⟩ => 
                            bind (θ c ⟨code_α, snd (unembed code_Γ)⟩)
                              (fun u => ret u))) as [e He].
            exists e.
            intros α code_α Henv code_Γ Hctx.
            destruct Hctx as (c1 & Hc1 & c2 & Hctx & Heq).
            destruct (Hc α code_α Henv c2 Hctx) as (u & Hvalu & Hrealu).
            exists u. 
            split; [| assumption].
            apply He. Locate "fun!". rewrite embedP. 
            subst. rewrite embedP. simpl.
            apply bind_hasvalue.
            exists u.
            split; [assumption | apply ret_hasvalue].
      }
      {
        (* /\-intro *)
        destruct (IHHprv1 n) as [c Hc]...
        { solve_bounded. }
        destruct (IHHprv2 n) as [e He]...
        { solve_bounded. }

        destruct (epf (fun! ⟨code_α, code_Γ⟩ => 
                    bind (θ c ⟨code_α, code_Γ⟩) 
                      (fun v => bind (θ e ⟨code_α, code_Γ⟩) 
                        (fun u => ret ⟨v, u⟩)))) as [d Hd].
        exists d.
        intros α code_α Henv code_Γ Hctx.
        destruct (Hc α code_α Henv code_Γ Hctx) as (v & Hvalv & Hrealv). destruct (He α code_α Henv code_Γ Hctx) as (u & Hvalu & Hrealu).
        exists (⟨v, u⟩).
        split.
        + apply Hd. rewrite embedP. 
          apply bind_hasvalue. 
          exists v. split.
          apply Hvalv.
          apply bind_hasvalue.
          exists u. split.
          apply Hvalu.
          apply ret_hasvalue.
        + simpl. exists v. exists u.
          split. apply Hrealv. 
          split. apply Hrealu.
          reflexivity.
      }
      {
        (* /\-elim left *)
        destruct (find_bounded ψ) as [m Hmψ].
        destruct (IHHprv (Nat.max n m)) as [c Hc]...
        { solve_bounded. }
        destruct (epf (fun! ⟨code_α, code_Γ⟩ => 
                    bind (θ c ⟨code_α, code_Γ⟩) 
                      (fun! ⟨x, y⟩ => ret x))) as [e He].
        exists e.
        intros α code_α Henv code_Γ Hctx.
        assert (Henvmax : code_α ⊩env[Nat.max n m] α).
        { apply realizes_env_ge with (Part := Part) (θ := θ) (n := n); [ assumption | assumption | lia ]. }
        destruct (Hc α code_α Henvmax code_Γ Hctx) as (v & Hvalv & Hrealv).
        destruct Hrealv as (c1 & c2 & Hc1 & Hc2 & Heq).
        exists c1.
        split.
        + apply He. rewrite embedP. 
          apply bind_hasvalue.
          exists v. split.
          apply Hvalv. 
          rewrite Heq.
          rewrite embedP.
          apply ret_hasvalue.
        + apply Hc1.
      }
      {
        (* /\-elim right *)
        destruct (find_bounded φ) as [m Hmφ].
        destruct (IHHprv (Nat.max n m)) as [c Hc]...
        { solve_bounded. }
        destruct (epf (fun! ⟨code_α, code_Γ⟩ => 
                    bind (θ c ⟨code_α, code_Γ⟩) 
                      (fun! ⟨x, y⟩ => ret y))) as [e He].
        exists e.
        intros α code_α Henv code_Γ Hctx.
        assert (Henvmax : code_α ⊩env[Nat.max n m] α).
        { apply realizes_env_ge with (Part := Part) (θ := θ) (n := n); [ assumption |assumption | lia ]. }
        destruct (Hc α code_α Henvmax code_Γ Hctx) as (v & Hvalv & Hrealv).
        destruct Hrealv as (c1 & c2 & Hc1 & Hc2 & Heq).
        exists c2.
        split.
        + apply He. rewrite embedP. 
          apply bind_hasvalue.
          exists v. split.
          apply Hvalv. 
          rewrite Heq.
          rewrite embedP.
          apply ret_hasvalue.
        + apply Hc2.
      }
      {
        (* \/-intro left *)
        destruct (IHHprv n) as [c Hc]...
        { solve_bounded. }
        destruct (epf (fun! ⟨code_α, code_Γ⟩ => 
                        bind (θ c ⟨code_α, code_Γ⟩) 
                          (fun v => ret ⟨0, v⟩))) as [e He].
        exists e.
        intros α code_α Henv code_Γ Hctx.
        destruct (Hc α code_α Henv code_Γ Hctx) as (v & Hvalv & Hrealv).
        exists ⟨0, v⟩.
        split.
        + apply He. rewrite embedP. 
          apply bind_hasvalue. 
          exists v. split. 
          apply Hvalv. apply ret_hasvalue.
        + simpl. left. exists v.
          split. reflexivity. apply Hrealv.
      }
      {
        (* \/-intro right *)
        destruct (IHHprv n) as [c Hc]...
        { solve_bounded. }
        destruct (epf (fun! ⟨code_α, code_Γ⟩ => 
                        bind (θ c ⟨code_α, code_Γ⟩) 
                          (fun v => ret ⟨1, v⟩))) as [e He].
        exists e.
        intros α code_α Henv code_Γ Hctx.
        destruct (Hc α code_α Henv code_Γ Hctx) as (v & Hvalv & Hrealv).
        exists ⟨1, v⟩.
        split.
        + apply He. rewrite embedP.
          apply bind_hasvalue. 
          exists v. split. 
          apply Hvalv. apply ret_hasvalue.
        + simpl. right. exists v.
          split. reflexivity. apply Hrealv.
      }
      {
        (* \/-elimination *)
        destruct (find_bounded φ) as [m Hmφ].
        destruct (find_bounded ψ) as [k Hkψ].
        destruct (IHHprv1 (Nat.max (Nat.max m k) n)) as [c Hc]...
        { solve_bounded. }
        destruct (IHHprv2 (Nat.max (Nat.max m k) n)) as [e He]...
        { solve_bounded. }
        destruct (IHHprv3 (Nat.max (Nat.max m k) n)) as [f Hf]...
        { solve_bounded. }
        destruct (epf (fun! ⟨code_α, code_Γ⟩ => 
                    bind (θ c ⟨code_α, code_Γ⟩) (fun! ⟨v1, v2⟩ => 
                      match Nat.eqb 0 v1 with 
                      | true => θ e ⟨code_α, ⟨v2, code_Γ⟩⟩
                      | false => match Nat.eqb 1 v1 with 
                                | true => θ f ⟨code_α, ⟨v2, code_Γ⟩⟩
                                | false => undef
                                end
                      end))) as [g Hg].
        exists g.
        intros α code_α Henv code_Γ Hctx.
        assert (Henvmax : code_α ⊩env[Nat.max (Nat.max m k) n] α).
        { apply realizes_env_ge with (Part := Part) (θ := θ) (n := n); [ assumption |assumption | lia ]. }
        destruct (Hc α code_α Henvmax code_Γ Hctx) as (v & Hvalv & Hrealv).
        simpl in Hrealv. 
        destruct Hrealv as [(v2 & Heq & Hrealv2) | (v2 & Heq & Hrealv2)].
        - destruct (He α code_α Henvmax ⟨v2, code_Γ⟩) as (u & Hvalu & Hrealu).
          {
            exists v2. split. apply Hrealv2.
            exists code_Γ. split. 2: reflexivity. apply Hctx.
          }
          exists u. split.
          apply Hg. rewrite embedP.
          apply bind_hasvalue.
          exists v. split; [ apply Hvalv | ].
          rewrite Heq. rewrite embedP.  
          simpl. apply Hvalu.
          apply Hrealu.
        - destruct (Hf α code_α Henvmax ⟨v2, code_Γ⟩) as (u & Hvalu & Hrealu).
          {
            exists v2. split. apply Hrealv2.
            exists code_Γ. split. 2: reflexivity. apply Hctx.
          }
          exists u. split.
          apply Hg. rewrite embedP.
          apply bind_hasvalue.
          exists v. split; [ apply Hvalv | ].
          rewrite Heq. rewrite embedP.  
          simpl. apply Hvalu.
          apply Hrealu.
      }
      {
        (* Pierce *)
        congruence.
      }
Qed.

Corollary realizes_sound_closed {f : falsity_flag} (φ : form) : 
  bounded 0 φ -> 
  [] ⊢I φ -> 
    exists code_φ : nat, code_φ ⊩ φ.
Proof.
  intros Hφ Hprv.
  assert (Hbnd : bounded_L 0 (φ :: [])) by solve_bounded. 
  destruct (realizes_sound_ND Hbnd Hprv) as (c & Hc).
  pose (zero_realizes_triv_env) as Henv.
  assert (0 ⊩ctx List.nil) as Hctx.
  { apply I. }
  destruct (Hc (fun _ => 0) 0 Henv 0 Hctx) as (code_φ & Hval & Hreal).
  exists code_φ. 
  assumption.
Qed.

End Soundness.

(** ** Consistency *)

Section Consistency.

Definition consistent (φ : form) :=
  ~ ([] ⊢I φ → ⊥).

Lemma realized_closed_form_is_consistent (φ : form) :
  bounded 0 φ -> (exists c, c ⊩ φ) -> consistent φ.
Proof.
  intros ? [c Hrealc] Hprv.
  assert (Hbnd : bounded 0 (φ → ⊥)). constructor; [assumption | constructor]. 
  destruct (realizes_sound_closed Hbnd Hprv) as (nc & Hnc).
  simpl in Hnc. setoid_rewrite ex_P_and_False in Hnc.
  apply Hnc with c; assumption.
Qed.


End Consistency.

End NumberRealizability.
