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
  (⌜k ≠ #()⌝ ∗ (callback_invokation_permit γk 1%Qp -∗ ∀ v, P v -∗ WP (k v) {{v, ⌜ v = #() ⌝}})).

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
  
Theorem invokeCallback_spec' P γ k (v: val):
  is_callback P γ k -∗
  P v -∗
  callback_invokation_permit γ 1%Qp -∗
    WP (k v) {{v, ⌜ v = #() ⌝ }}.
Proof.
  iIntros "(% & HCallback) HP HInvoke".
  rewrite /is_callback.
  iApply ("HCallback" with "[HInvoke] [HP]").
  iAssumption. iAssumption.
Qed.

Theorem invokeCallback_spec P γ k (v: val):
  {{{ is_callback P γ k ∗
      P v ∗
      callback_invokation_permit γ 1%Qp }}}
    k v
  {{{ RET #(); True }}}.
Proof.
  (* a.d. TODO how do these TEXAN triples work and why do I get a later that I cannot get rid of. *)
Admitted.
  (* iIntros (Φ) "((% & HCallback) & HP & HInvoke) HΦ".
  iSpecialize ("HCallback" with "HInvoke HP").
  iApply (wp_strong_mono with "HCallback"); try done.
  iIntros (? ->) "!>". *)

End proof.

Typeclasses Opaque callback_invokation_permit 
            callback_is_invoked is_callback.
