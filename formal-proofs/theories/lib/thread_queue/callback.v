From iris.heap_lang Require Import notation lang.
From SegmentQueue.util Require Import
  everything local_updates big_opL cmra count_matching find_index.

From iris.base_logic Require Import lib.invariants.
From iris.program_logic Require Import atomic.
From iris.bi.lib Require Import fractional.
From iris.heap_lang Require Import proofmode.
From iris.algebra Require Import cmra excl csum auth csum numbers.

Section proof.

Inductive callback_state :=
  | CallbackWaiting
  | CallbackInvoked (v: val)
  | CallbackCancelled.

Notation permit := (optionUR (csumR fracR (agreeR unitO))).

Notation algebra := (authUR (prodUR
                                  (* None: Waiting
                                     Some: Invoked
                                  *)
                              (prodUR
                                (prodUR 
                                  (optionUR (agreeR valO))
                                  (optionUR (agreeR (optionO valO))))
                                permit)
                              permit)).

Class callbackG Σ := CallbackG {
  callback_inG :> inG Σ algebra;
}.
Definition callbackΣ : gFunctors := #[GFunctor algebra].
Instance subG_callbackΣ {Σ} : subG callbackΣ Σ -> callbackG Σ.
Proof. solve_inG. Qed.

Context `{heapG Σ} `{callbackG Σ}.

(* true -> whole permit
   false -> not present *)
Definition permit_auth_ra (present: bool): permit :=
  Some (if present then Cinl 1%Qp else Cinr (to_agree ())).

(* true -> half the permit
   false -> not present *)
Definition permit_state_ra (present: bool): permit :=
  Some (if present then Cinl (1 / 2)%Qp else Cinr (to_agree ())).

Definition callback_auth_ra (p: leibnizO callback_state) (k: valO): algebra :=
  ● match p with
  | CallbackWaiting => (Some (to_agree k), None, permit_auth_ra true, permit_auth_ra true)
  | CallbackInvoked v => (Some (to_agree k), Some (to_agree (Some v)), permit_auth_ra false, permit_auth_ra true)
  | CallbackCancelled => (Some (to_agree k), Some (to_agree None), permit_auth_ra true, permit_auth_ra false)
  end.
    
Definition callback_invokation_permit (γ: gname) (q: Qp): iProp Σ :=
  own γ (◯ (None, None, Some (Cinl q), None)).

Definition callback_cancellation_permit (γ: gname) (q: Qp): iProp Σ :=
  own γ (◯ (None, None, None, Some (Cinl q))).

Definition callback_is_invoked (γ: gname) (v: val): iProp Σ :=
  own γ (◯ (None, Some (to_agree (Some v)), permit_state_ra false, None)).
  
Definition callback_is_cancelled (γ: gname): iProp Σ :=
  own γ (◯ (None, Some (to_agree None), None, permit_state_ra false)).
  
Definition is_callback (γ: gname) (k: val): iProp Σ :=
  own γ (◯ (Some (to_agree k), None, None, None)).
  
Global Instance callback_invokation_permit_Timeless:
  Timeless (callback_invokation_permit γ q).
Proof. apply _. Qed.

Global Instance callback_cancellation_permit_Timeless:
  Timeless (callback_cancellation_permit γ q).
Proof. apply _. Qed.

Global Instance callback_invokation_permit_Fractional γ:
  Fractional (callback_invokation_permit γ).
Proof.
  iIntros (x y). rewrite /callback_invokation_permit.
  by rewrite -own_op -auth_frag_op -!pair_op -Some_op -Cinl_op -frac_op'.
Qed.

Global Instance callback_cancellation_permit_Fractional γ:
  Fractional (callback_cancellation_permit γ).
Proof.
  iIntros (x y). rewrite /callback_cancellation_permit.
  by rewrite -own_op -auth_frag_op -!pair_op -Some_op -Cinl_op -frac_op'.
Qed.

Theorem callback_invokation_permit_valid γ q:
  callback_invokation_permit γ q -∗ ⌜(q ≤ 1)%Qc⌝.
Proof.
  iIntros "HFuture". iDestruct (own_valid with "HFuture") as %HValid.
  iPureIntro. move: HValid. rewrite auth_frag_valid; case; case=> /=. 
  rewrite Some_valid. by compute.
Qed.

Theorem callback_cancellation_permit_valid γ q:
  callback_cancellation_permit γ q -∗ ⌜(q ≤ 1)%Qc⌝.
Proof.
  iIntros "HFuture". iDestruct (own_valid with "HFuture") as %HValid.
  iPureIntro. move: HValid. rewrite auth_frag_valid. case=> _/=. 
  rewrite Some_valid. by compute.
Qed.

Global Instance callback_is_invoked_Persistent:
  Persistent (callback_is_invoked γ v).
Proof. apply _. Qed.

Global Instance callback_is_cancelled_Persistent:
  Persistent (callback_is_cancelled γ).
Proof. apply _. Qed.

Theorem callback_invokation_permit_implies_not_invoked γ v q:
  callback_invokation_permit γ q -∗ callback_is_invoked γ v -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %[[_ HValid]%pair_valid _]%pair_valid.
  exfalso. move: HValid=> /=. by compute.
Qed.

Theorem callback_cancellation_permit_implies_not_cancelled γ q:
  callback_cancellation_permit γ q -∗ callback_is_cancelled γ -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %[_ HValid]%pair_valid.
  exfalso. move: HValid=> /=. by compute.
Qed.

Theorem callback_is_invoked_not_cancelled γ v:
  callback_is_invoked γ v -∗ callback_is_cancelled γ -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2")
    as %[[[_ HValid]%pair_valid _]%pair_valid _]%pair_valid.
  exfalso. move: HValid=> /=. rewrite -Some_op Some_valid=> HValid.
  by apply agree_op_invL' in HValid.
Qed.

Definition is_waker (P: val -> iProp Σ) (k : val): iProp Σ := ∀ v, P v -∗ WP (k v) {{r, ⌜ r = #() ⌝}}.

Definition callback_invariant (P: val -> iProp Σ) (γ: gname) (k: val)
           (state: callback_state): iProp Σ :=
  own γ (callback_auth_ra state k) ∗ ⌜ k ≠ #() ⌝ ∗
  match state with
    | CallbackWaiting => is_waker P k
    | CallbackInvoked v => True
    | CallbackCancelled =>  True
  end.
    
Instance callback_state_Inhabited: Inhabited callback_state.
Proof. econstructor. econstructor. Qed.

Lemma callback_is_invoked_from_auth_ra γ v k:
  own γ (callback_auth_ra (CallbackInvoked v) k) ==∗
  own γ (callback_auth_ra (CallbackInvoked v) k) ∗ callback_is_invoked γ v.
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ $]"; last done.
  apply auth_update_core_id; first by apply _.
  repeat (apply prod_included; split). all: simpl. all: try done.
  apply None_least.
  apply None_least.
Qed.

Lemma callback_is_cancelled_from_auth_ra γ k:
  own γ (callback_auth_ra CallbackCancelled k) ==∗
  own γ (callback_auth_ra CallbackCancelled k) ∗ callback_is_cancelled γ.
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ $]"; last done.
  apply auth_update_core_id; first by apply _.
  repeat (apply prod_included; split). all: simpl. all: try done.
  apply None_least.
  apply None_least.
Qed.

Theorem is_callback_from_auth_ra γ state k: 
  own γ (callback_auth_ra state k) ==∗
  own γ (callback_auth_ra state k) ∗ is_callback γ k.
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ $]"; last done.
  apply auth_update_core_id; first by apply _.
  repeat (apply prod_included; split).
  all: destruct state; simpl; try done; try apply None_least.
Qed.

Theorem callback_invokation_permit_exclusive γ q:
  callback_invokation_permit γ 1%Qp -∗ callback_invokation_permit γ q -∗ False.
Proof.
  iIntros "H1 H2". iCombine "H1" "H2" as "H".
  iDestruct (own_valid with "H") as %HValid. exfalso. move: HValid.
  case; case=> _/=.
  move: (frac_valid' (1 + q)). case=> HOk _ HOk' _. apply HOk in HOk'.
  by eapply Qp_not_plus_q_ge_1.
Qed.

Theorem callback_cancellation_permit_exclusive γ q:
  callback_cancellation_permit γ 1%Qp -∗ callback_cancellation_permit γ q -∗ False.
Proof.
  iIntros "H1 H2". iCombine "H1" "H2" as "H".
  iDestruct (own_valid with "H") as %HValid. exfalso. move: HValid.
  case=> _/=.
  move: (frac_valid' (1 + q)). case=> HOk _ HOk'. apply HOk in HOk'.
  by eapply Qp_not_plus_q_ge_1.
Qed.

Theorem is_callback_agree γ k k': 
  is_callback γ k -∗ is_callback γ k' -∗ ⌜ k = k' ⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %HValid.
  iPureIntro. move: HValid.
  case; case; case=> /= HValid _ _ _.
  move: HValid.
  rewrite Some_valid.
  apply agree_op_invL'.
Qed.

Theorem invokeCallback_spec P γ k (v: val):
  callback_invokation_permit γ 1%Qp -∗
  callback_invariant P γ k CallbackWaiting -∗
  P v ==∗
    WP (k v) {{r, ⌜ r = #() ⌝ }} ∗
    callback_invariant P γ k (CallbackInvoked v) ∗
    callback_is_invoked γ v.
Proof.
  iIntros "HInvoke (H● & % & Hk) HP".
  iSplitL "Hk HP". 
  - iModIntro.  
    iApply ("Hk" with "HP").
  - iAssert (|==> own γ (callback_auth_ra (CallbackInvoked v) k) ∗ callback_is_invoked γ v)%I with "[H● HInvoke]" as ">[H● HCallbackInvoked]".
    { 
      iApply own_op.
      iApply (own_update_2 with "H● HInvoke").
      rewrite /callback_auth_ra. 
      apply auth_update with
          (a' := (Some (to_agree k), Some (to_agree (Some v)),
                  permit_auth_ra false, permit_auth_ra true)).
      repeat apply prod_local_update'.
      - by done.
      - by apply alloc_option_local_update.
      - rewrite /permit_auth_ra.
        etransitivity.
        by apply delete_option_local_update, Cinl_exclusive, frac_full_exclusive.
        by apply alloc_option_local_update.
      - done.
    }
    iModIntro.
    iFrame. by iSplit.
Qed.

Theorem cancelCallback_spec P γ k (v: val):
  callback_cancellation_permit γ 1%Qp -∗
  callback_invariant P γ k CallbackWaiting ==∗
    is_waker P k ∗
    callback_invariant P γ k CallbackCancelled ∗
    callback_is_cancelled γ.
Proof.
  iIntros "HCancel (H● & % & Hk)".
  iSplitL "Hk"; first done.
  iAssert (|==> own γ (callback_auth_ra CallbackCancelled k) ∗ callback_is_cancelled γ)%I with "[H● HCancel]" as ">[H● HCallbackCancelled]".
  { 
    iApply own_op.
    iApply (own_update_2 with "H● HCancel").
    rewrite /callback_auth_ra. 
    apply auth_update with
        (a' := (Some (to_agree k), Some (to_agree None),
                permit_auth_ra true, permit_auth_ra false)).
    repeat apply prod_local_update'.
    - by done.
    - by apply alloc_option_local_update.
    - done.
    - rewrite /permit_auth_ra.
      etransitivity.
      by apply delete_option_local_update, Cinl_exclusive, frac_full_exclusive.
      by apply alloc_option_local_update.
  }
  iModIntro.
  iFrame. by iSplit.
Qed.

Lemma None_op_right_id (A: cmraT) (a: option A): a ⋅ None = a.
Proof. by destruct a. Qed.

Theorem newCallback_spec P k:
  ⌜ k ≠ #() ⌝ -∗  
  is_waker P k ==∗
    ∃ γ, callback_invariant P γ k CallbackWaiting ∗
          callback_invokation_permit γ 1%Qp ∗ 
          callback_cancellation_permit γ 1%Qp.
Proof.
  iIntros "Hunit Hwaker".
  iMod (own_alloc (callback_auth_ra CallbackWaiting k ⋅
                   (◯ (None, None, Some (Cinl 1%Qp), None) ⋅
                    ◯ (None, None, None, Some (Cinl 1%Qp)))))
    as (γ) "[H● [H◯ H◯']]".
  {
    apply auth_both_valid. split; last done.
    repeat (apply prod_included'; split). all: try by simpl.
    simpl.
    rewrite None_op_right_id.
    apply None_least.
  }
  iModIntro.
  iExists _. by iFrame.
Qed.

End proof.

Typeclasses Opaque callback_invokation_permit callback_cancellation_permit 
            callback_is_invoked callback_is_cancelled.
