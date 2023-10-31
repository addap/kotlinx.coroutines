From iris.heap_lang Require Import notation lang.
From SegmentQueue.util Require Import cmra.

From iris.base_logic Require Import lib.invariants.
From iris.program_logic Require Import atomic.
From iris.bi.lib Require Import fractional.
From iris.heap_lang Require Import proofmode.
From iris.algebra Require Import cmra excl csum auth csum numbers.

Section proof.

Inductive callback_state :=
  | CallbackWaiting
  | CallbackInvoked (v: val).

Notation permit := (optionUR (csumR fracR (agreeR unitO))).

Notation algebra := (authUR (prodUR
                                  (* None: Waiting
                                     Some: Invoked
                                  *)
                                  (optionUR (agreeR valO))
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

Definition callback_auth_ra (p: leibnizO callback_state): algebra :=
  ● match p with
  | CallbackWaiting => (None, permit_auth_ra true)
  | CallbackInvoked v => (Some (to_agree v), permit_auth_ra false)
  end.

Definition callback_invokation_permit (γ: gname) (q: Qp): iProp Σ :=
  own γ (◯ (None, Some (Cinl q))).

Definition callback_is_invoked (γ: gname) (v: val): iProp Σ :=
  own γ (◯ (Some (to_agree v), permit_state_ra false)).

Global Instance callback_invokation_permit_Timeless:
  Timeless (callback_invokation_permit γ q).
Proof. apply _. Qed.

Global Instance callback_invokation_permit_Fractional γ:
  Fractional (callback_invokation_permit γ).
Proof.
  iIntros (x y). rewrite /callback_invokation_permit.
  by rewrite -own_op -auth_frag_op -!pair_op -Some_op -Cinl_op -frac_op'.
Qed.

Theorem callback_invokation_permit_valid γ q:
  callback_invokation_permit γ q -∗ ⌜(q ≤ 1)%Qc⌝.
Proof.
  iIntros "HFuture". iDestruct (own_valid with "HFuture") as %HValid.
  iPureIntro. move: HValid. rewrite auth_frag_valid. case=> _/=. 
  rewrite Some_valid. by compute.
Qed.

Global Instance callback_is_invoked_Persistent:
  Persistent (callback_is_invoked γ v).
Proof. apply _. Qed.

Theorem callback_invokation_permit_implies_not_invoked γ v q:
  callback_invokation_permit γ q -∗ callback_is_invoked γ v -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %[_ HValid]%pair_valid.
  exfalso. move: HValid=> /=. by compute.
Qed.

Definition is_callback (P: val -> iProp Σ) (γk: gname) (k: val): iProp Σ :=
  (⌜k ≠ #()⌝ ∗ (callback_invokation_permit γk 1%Qp -∗ ∀ v, P v -∗ WP (k v) {{_, True}})).

(* Global Instance is_callback_persistent R γ k:
  Persistent (is_callback R γ k).
Proof. apply _. Qed. *)

Instance callback_state_Inhabited: Inhabited callback_state.
Proof. econstructor. econstructor. Qed.

Lemma callback_is_invoked_from_auth_ra γ v:
  own γ (callback_auth_ra (CallbackInvoked v)) ==∗
  own γ (callback_auth_ra (CallbackInvoked v)) ∗ callback_is_invoked γ v.
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ $]"; last done.
  apply auth_update_core_id; first by apply _.
  repeat (apply prod_included; split). all: simpl. all: try done.
Qed.

Theorem callback_invokation_permit_exclusive γ q:
  callback_invokation_permit γ 1%Qp -∗ callback_invokation_permit γ q -∗ False.
Proof.
  iIntros "H1 H2". iCombine "H1" "H2" as "H".
  iDestruct (own_valid with "H") as %HValid. exfalso. move: HValid.
  case=> _/=.
  move: (frac_valid' (1 + q)). case=> HOk _ HOk'. apply HOk in HOk'.
  by eapply Qp_not_plus_q_ge_1.
Qed.


(* Theorem invokeCallback_spec P γ k (v: val):
  is_callback P γ k -∗
  {{{ ▷ P v ∗
      callback_invokation_permit γ 1%Qp }}}
    k v @ ⊤ ∖ ↑N
  {{{ RET #(); callback_is_invoked γ v }}}.
Proof.
  iIntros "#HFuture". 
  iInv "HFuture" as (p) "[>H● Hℓ]" "HInvClose". *)

Theorem invokeCallback_spec P γ k (v: val):
  {{{ is_callback P γ k ∗
      ▷ P v ∗
      callback_invokation_permit γ 1%Qp }}}
    k v
  {{{ r, RET #r; callback_is_invoked γ v }}}.
Proof.
Admitted.
  (* iIntros (Φ) "((% & HIHCallback) & HP & HInvoke) HΦ".
  rewrite /is_callback.
  iApply "HCallback".



  iIntros "#HFuture" (Φ) "AU". 
  iInv "HFuture" as (p) "[>H● Hℓ]" "HInvClose".
  iMod "AU" as "[[HR HPermit] [_ HClose]]".
  destruct p.
  - wp_cmpxchg_suc.
    iMod (own_update_2 with "H● HPermit") as "[H● HCallbackInvoked]".
    {
      apply auth_update with
          (a' := (Some (to_agree (Some v)),
                  permit_auth_ra false, permit_auth_ra true)).
      repeat apply prod_local_update'.
      - by apply alloc_option_local_update.
      - rewrite /permit_auth_ra.
        etransitivity.
        by apply delete_option_local_update, Cinl_exclusive, frac_full_exclusive.
        by apply alloc_option_local_update.
      - done.
    }
    iDestruct "HCallbackInvoked" as "#HCallbackInvoked".
    iMod ("HClose" $! true with "HCallbackInvoked") as "HΦ".
    iModIntro.
    iMod ("HInvClose" with "[-HΦ]") as "_".
    { iExists (CallbackInvoked v). iFrame.
      iDestruct "HR" as "[$|HContra]".
      destruct controlling_cancellation.
      - iDestruct (callback_is_invoked_not_cancelled
                     with "HCallbackInvoked HContra") as ">[]".
      - iDestruct "HContra" as %[].
    }
    iModIntro. by wp_pures.
  - iDestruct (own_valid_2 with "H● HPermit")
      as %[[[_ HValid]%pair_included _]%pair_included _]%auth_both_valid.
    exfalso. move: HValid. rewrite /permit_auth_ra.
    rewrite Some_included. case=> HContra.
    * inversion HContra.
    * apply csum_included in HContra.
      destruct HContra as
          [HContra|[(? & ? & ? & HContra & ?)|(? & ? & HContra & ?)]];
        simplify_eq.
  - wp_cmpxchg_fail.
    iMod (future_is_cancelled_from_auth_ra with "H●") as "[H● HFutureCancelled]".
    destruct controlling_cancellation.
    2: iDestruct "HR" as "[HR|%]"; last done.
    all: iMod ("HClose" $! false with "[$]") as "HΦ"; iModIntro.
    all: iMod ("HInvClose" with "[H● Hℓ]") as "_";
      first by iExists FutureCancelled; iFrame.
    all: iModIntro; by wp_pures.
Qed. *)

End proof.

Typeclasses Opaque callback_invokation_permit 
            callback_is_invoked is_callback.
