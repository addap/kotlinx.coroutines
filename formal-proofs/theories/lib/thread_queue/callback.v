From iris.heap_lang Require Import notation lang.
From SegmentQueue.util Require Import
  everything local_updates big_opL cmra count_matching find_index.

From iris.base_logic Require Import lib.invariants.
From iris.program_logic Require Import atomic.
From iris.bi.lib Require Import fractional.
From iris.heap_lang Require Import proofmode.
From iris.algebra Require Import cmra excl csum auth numbers.

Definition newCallback : val := (λ: "k", ref "k").

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

Context `{heapGS Σ} `{callbackG Σ}.

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
  
Global Instance callback_invokation_permit_Timeless γ q:
  Timeless (callback_invokation_permit γ q).
Proof. apply _. Qed.

Global Instance callback_cancellation_permit_Timeless γ q:
  Timeless (callback_cancellation_permit γ q).
Proof. apply _. Qed.

Global Instance callback_invokation_permit_Fractional γ:
  Fractional (callback_invokation_permit γ).
Proof.
  iIntros (x y). rewrite /callback_invokation_permit.
  by rewrite -own_op -auth_frag_op -!pair_op -Some_op -Cinl_op -frac_op.
Qed.

Global Instance callback_cancellation_permit_Fractional γ:
  Fractional (callback_cancellation_permit γ).
Proof.
  iIntros (x y). rewrite /callback_cancellation_permit.
  by rewrite -own_op -auth_frag_op -!pair_op -Some_op -Cinl_op -frac_op.
Qed.

(* a.d. PORT swapped Qc for Qp, should be okay *)
Theorem callback_invokation_permit_valid γ q:
  callback_invokation_permit γ q -∗ ⌜(q ≤ 1)%Qp⌝.
Proof.
  iIntros "HFuture". iDestruct (own_valid with "HFuture") as %HValid.
  iPureIntro. move: HValid. rewrite auth_frag_valid; case; case=> /=. 
  rewrite Some_valid. by compute.
Qed.

Theorem callback_cancellation_permit_valid γ q:
  callback_cancellation_permit γ q -∗ ⌜(q ≤ 1)%Qp⌝.
Proof.
  iIntros "HFuture". iDestruct (own_valid with "HFuture") as %HValid.
  iPureIntro. move: HValid. rewrite auth_frag_valid. case=> _/=. 
  rewrite Some_valid. by compute.
Qed.

Global Instance callback_is_invoked_Persistent γ v:
  Persistent (callback_is_invoked γ v).
Proof. apply _. Qed.

Global Instance callback_is_cancelled_Persistent γ:
  Persistent (callback_is_cancelled γ).
Proof. apply _. Qed.

(* a.d. PORT something goes wrong with applying pair_valid lemmas here. *)
Theorem callback_invokation_permit_implies_not_invoked γ v q:
  callback_invokation_permit γ q -∗ callback_is_invoked γ v -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %H'.
  rewrite -auth_frag_op in H'.
  specialize (auth_frag_valid_1 _ H') as H1.
  move: H1.
  rewrite pair_valid. cbn.
  rewrite pair_valid. cbn.
  move=> [[_ HValid] _].
  exfalso. move: HValid=> /=. by compute.
  (* iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %[[_ HValid]%pair_valid _]%pair_valid.
  exfalso. move: HValid=> /=. by compute. *)
Qed.

Theorem callback_cancellation_permit_implies_not_cancelled γ q:
  callback_cancellation_permit γ q -∗ callback_is_cancelled γ -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %H'.
  rewrite -auth_frag_op in H'.
  specialize (auth_frag_valid_1 _ H') as H1.
  move: H1.
  rewrite pair_valid. cbn.
  move=> [_ HValid].
  exfalso. move: HValid=> /=. by compute.
  (* iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %[_ HValid]%pair_valid.
  exfalso. move: HValid=> /=. by compute. *)
Qed.

Theorem callback_is_invoked_not_cancelled γ v:
  callback_is_invoked γ v -∗ callback_is_cancelled γ -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %H'.
  rewrite -auth_frag_op in H'.
  specialize (auth_frag_valid_1 _ H') as H1.
  move: H1.
  rewrite pair_valid. cbn.
  rewrite pair_valid. cbn.
  rewrite pair_valid. cbn.
  move=> [[[_ HValid] _] _].
  exfalso. move: HValid=> /=. rewrite -Some_op Some_valid=> HValid.
  by apply to_agree_op_inv_L in HValid.
  (* iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2")
    as %[[[_ HValid]%pair_valid _]%pair_valid _]%pair_valid.
  exfalso. move: HValid=> /=. rewrite -Some_op Some_valid=> HValid.
  by apply to_agree_op_inv_L in HValid. *)
Qed.

Theorem callback_is_invoked_not_waiting γ v k:
  callback_is_invoked γ v -∗ own γ (callback_auth_ra CallbackWaiting k) -∗ False.
Proof.
  (* a.d. learn how ssreflect proofs work or just do it in the traditional way. *)
  iIntros "H1 H2". 
  rewrite /callback_is_invoked /callback_auth_ra.
  iDestruct (own_valid_2 with "H2 H1") as "H".
  iDestruct "H" as %HValid.
  exfalso. move: HValid=> /=. rewrite auth_both_valid_discrete.
  case. move=> HValid _. move: HValid. 
  do 3 rewrite pair_included. do 3 case.
  move=> _ HContra _ _.
  move: HContra.
  rewrite option_included.
  case; first done.
  case. move=> ?.
  case. move=> ?.
  case. move=> _.
  case. done.
Qed.

Definition is_waker (P: val -> iProp Σ) (k : val): iProp Σ := ∀ v, P v -∗ WP (k v) {{r, ⌜ r = #() ⌝}}.
(* TODO rename to callback_resources *)
Definition callback_invariant (P: val -> iProp Σ) (γ: gname) (l: loc)
           (state: callback_state): iProp Σ :=
  ∃ (k: val), l ↦ k ∗
  own γ (callback_auth_ra state k) ∗ 
  match state with
    | CallbackWaiting => is_waker P k
    | CallbackInvoked v => True
    | CallbackCancelled =>  True
  end.
    
Instance callback_state_Inhabited: Inhabited callback_state.
Proof. econstructor. econstructor. Qed.

Lemma callback_is_invoked_from_auth_ra E' γ v k:
  own γ (callback_auth_ra (CallbackInvoked v) k) ={E'}=∗
  own γ (callback_auth_ra (CallbackInvoked v) k) ∗ callback_is_invoked γ v.
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ $]"; last done.
  apply auth_update_dfrac_alloc; first by apply _.
  repeat (apply prod_included; split). all: simpl. all: try done.
  apply None_least.
  apply None_least.
Qed.

Lemma callback_is_cancelled_from_auth_ra E' γ k:
  own γ (callback_auth_ra CallbackCancelled k) ={E'}=∗
  own γ (callback_auth_ra CallbackCancelled k) ∗ callback_is_cancelled γ.
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ $]"; last done.
  apply auth_update_dfrac_alloc; first by apply _.
  repeat (apply prod_included; split). all: simpl. all: try done.
  apply None_least.
  apply None_least.
Qed.

Theorem is_callback_from_auth_ra E' γ state k: 
  own γ (callback_auth_ra state k) ={E'}=∗
  own γ (callback_auth_ra state k) ∗ is_callback γ k.
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ $]"; last done.
  apply auth_update_dfrac_alloc; first by apply _.
  repeat (apply prod_included; split).
  all: destruct state; simpl; try done; try apply None_least.
Qed.

From stdpp Require Import numbers.

Theorem callback_invokation_permit_exclusive γ q:
  callback_invokation_permit γ 1%Qp -∗ callback_invokation_permit γ q -∗ False.
Proof.
  iIntros "H1 H2". 
  iDestruct (own_valid_2 with "H1 H2") as %HValid. exfalso.
  rewrite -auth_frag_op in HValid.
  specialize (auth_frag_valid_1 _ HValid) as H1.
  move: H1.
  case; case=> _/=.
  move: (frac_valid (1 + q)). case=> HOk _ HOk' _. apply HOk in HOk'.
  by eapply Qp_not_add_le_l.
Qed.

Theorem callback_cancellation_permit_exclusive γ q:
  callback_cancellation_permit γ 1%Qp -∗ callback_cancellation_permit γ q -∗ False.
Proof.
  iIntros "H1 H2". 
  iDestruct (own_valid_2 with "H1 H2") as %HValid. exfalso. 
  rewrite -auth_frag_op in HValid.
  specialize (auth_frag_valid_1 _ HValid) as H1.
  move: H1.
  case=> _/=.
  move: (frac_valid (1 + q)). case=> HOk _ HOk'. apply HOk in HOk'.
  by eapply Qp_not_add_le_l.
Qed.

Theorem is_callback_agree γ k k': 
  is_callback γ k -∗ is_callback γ k' -∗ ⌜ k = k' ⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %H1.
  iPureIntro.
  rewrite -auth_frag_op in H1.
  specialize (auth_frag_valid_1 _ H1) as HValid.
  move: HValid.
  case; case; case=> /= HValid _ _ _.
  move: HValid.
  rewrite Some_valid.
  apply to_agree_op_inv_L.
Qed.

Theorem invokeCallback_spec E' P γ l (v: val):
  callback_invokation_permit γ 1%Qp -∗
  callback_invariant P γ l CallbackWaiting -∗
  P v ={E'}=∗
    ∃ (k: val), WP (k v) {{r, ⌜ r = #() ⌝ }} ∗
    callback_invariant P γ l (CallbackInvoked v) ∗
    callback_is_invoked γ v ∗
    is_callback γ k.
Proof.
  iIntros "HInvoke HInv HP".
  iDestruct "HInv" as (k) "(Hptr & H● & Hk)".
  iMod (is_callback_from_auth_ra with "H●") as "[H● HIsCallback']".
  iExists _.
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
    iFrame.
    iExists k. by iFrame.
Qed.

Theorem cancelCallback_spec E' P γ l k:
  is_callback γ k -∗
  callback_cancellation_permit γ 1%Qp -∗
  callback_invariant P γ l CallbackWaiting ={E'}=∗
    is_waker P k ∗
    callback_invariant P γ l CallbackCancelled ∗
    callback_is_cancelled γ.
Proof.
  iIntros "HIsCallback HCancel HInv".
  iDestruct "HInv" as (k') "(Hptr & H● & Hk)".
  iMod (is_callback_from_auth_ra with "H●") as "[H● HIsCallback']".
  iDestruct (is_callback_agree with "HIsCallback HIsCallback'") as %<-.
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
  iFrame. 
  iExists k. by iFrame.
Qed.

Lemma None_op_right_id (A: cmra) (a: option A): a ⋅ None = a.
Proof. by destruct a. Qed.

Theorem newCallback_spec P k:
  {{{ is_waker P k }}}
    newCallback k
  {{{ l γ, RET #l; 
        is_callback γ k ∗
        callback_invariant P γ l CallbackWaiting ∗
        callback_invokation_permit γ 1%Qp ∗ 
        callback_cancellation_permit γ 1%Qp }}}.
Proof.
  iIntros (HΦ) "Hwaker HΦ".
  iMod (own_alloc (callback_auth_ra CallbackWaiting k ⋅
                   (◯ (None, None, Some (Cinl 1%Qp), None) ⋅
                    ◯ (None, None, None, Some (Cinl 1%Qp)))))
    as (γ) "[H● [H◯ H◯']]".
  {
    apply auth_both_valid_discrete. split; last done.
    repeat (apply prod_included'; split). all: try by simpl.
    simpl.
    rewrite None_op_right_id.
    apply None_least.
  }
  rewrite -fupd_wp.
  iMod (is_callback_from_auth_ra with "H●") as "[H● HIsCallback]".
  iModIntro.
  wp_lam. 
  wp_alloc ℓ as "Hℓ". 
  iApply "HΦ".
  instantiate (1:=γ).
  iFrame. 
  iExists _. by iFrame.
Qed.

End proof.

Typeclasses Opaque callback_invokation_permit callback_cancellation_permit 
            callback_is_invoked callback_is_cancelled.
