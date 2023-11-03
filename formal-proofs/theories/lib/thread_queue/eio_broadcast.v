From SegmentQueue.util Require Import
  everything local_updates big_opL cmra count_matching find_index.

Require Import SegmentQueue.lib.util.getAndSet.
From iris.heap_lang Require Import notation.
From SegmentQueue.lib.concurrent_linked_list.infinite_array
     Require Import array_spec iterator.iterator_impl.
From SegmentQueue.lib.thread_queue Require Import callback.

(* We say EIORESUMEDV b/c RESUMED already existed before and I want a clean separation. Rename in the end. *)
Notation EMPTYV := NONEV.
Notation EIORESUMEDV := (SOMEV #()).
Notation CANCELLEDV := (InjLV #1).

Section impl.

Variable array_interface: infiniteArrayInterface.

(* 
  Suspend like Eio does it, receive a k as input and put it in the cell.
  In that case, the cell can only be resumed. Other cases are impossible.
 *)
Definition suspend: val :=
  λ: "enqIterator" "k",
  let: "cellPtr" := Snd (iteratorStep array_interface "enqIterator") in
  let: "cell" := derefCellPointer array_interface "cellPtr" in
  if: CAS "cell" EMPTYV (InjL "k")
  then SOME "cellPtr"
  else let: "cellState" := !"cell" in
       if: "cellState" = EIORESUMEDV
       then "k" #() ;; NONEV
       else "undefined".

(* 
  Resume similar to Eio would do it but only singular. resume_all comes later.
*)
Definition resume: val :=
  λ: "deqIterator",
  match: iteratorStepOrIncreaseCounter
           array_interface #false "deqIterator" with
      NONE => #false
      (* a.d. if not cancelled, we get the same kind of cellPtr as in suspend. *)
    | SOME "cellPtr" =>
      (* a.d. same as in Eio. *)
      cellPointerCleanPrev array_interface "cellPtr" ;;
      (rec: "modify_cell" <> :=
        let: "cell" := derefCellPointer array_interface "cellPtr" in
        let: "cellState" := !"cell" in
        if: "cellState" = EMPTYV then
          if: CAS "cell" EMPTYV EIORESUMEDV
          then #true
          (* a.d. if CAS failed, then the cell is not EMPTYV so we will hit another branch. *)
          else "modify_cell" #()
        else if: "cellState" = CANCELLEDV then #false
        else match: "cellState" with
        (* resumed is impossible *)
               InjR <> => "undefined"
        (* finally, we have a waker in the cell, so we try to call it *)
             | InjL "waker" => 
               if: CAS "cell" (InjL "waker") EIORESUMEDV
               then "waker" #()
               else #false
             end) #()
  end.

(* 

*)
Definition try_cancel: val :=
  λ: "cellPtr",
    let: "cell" := derefCellPointer array_interface "cellPtr" in
    let: "cellState" := !"cell" in
    if: "cellState" = CANCELLEDV then "invalid_arg"
    else if: "cellState" = EMPTYV then "undefined"
    else match: "cellState" with
         (* already resumed *)
           InjR <> => #false
         | InjL "waker" => 
           if: CAS "cell" (InjL "waker") CANCELLEDV
           then cancelCell array_interface "cellPtr" ;; #true
           else #false (* we got resumed first *)
         end.
    
Definition newThreadQueue: val :=
  λ: <>, let: "arr" := newInfiniteArray array_interface #2 in
        (newIterator ("arr" +ₗ #0) #0,
         newIterator ("arr" +ₗ #1) #0).

End impl.

From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode.
From iris.algebra Require Import auth numbers list gset excl csum.

Section proof.

(** State **)

Inductive cellTerminalState :=
| cellResumed
| cellImmediatelyCancelled.

Inductive cellState :=
| cellPassedValue (resolution: option unit)
| cellInhabited (callbackName: gname) (callbackLoc: val)
                (resolution: option cellTerminalState).

(** Resource algebras **)

(* a.d. waker and its ghost name (maybe unecessary since we don't create it like the future) *)
Notation cellInhabitantThreadR := (agreeR (prodO gnameO valO)).

Notation inhabitedCellStateR :=
  (* a.d. None: cell is just inhabited.
          Some: callback was called or cell is cancelled. *)
  (optionR
     (* a.d. TODO should be the same as agreeR boolO *)
     (csumR
        (* Callback was called. *)
        (agreeR valO)
        (* Cell was (immediately) cancelled. *)
        (agreeR unitO))).

(* a.d.
  filled -> resume came first and placed a value.
  inhabited -> suspend came first and placed a waker/already cancelled. *)
Notation cellStateR :=
  (csumR
     (* Cell was filled with a value (always unit). *)
     (prodR
        (agreeR valO)
        (* a.d. None: cell is filled. Some: value was taken. *)
        (optionUR (agreeR unitO)))
     (* Cell was inhabited. *)
     (prodR
        (* Description of the stored callback. *)
        cellInhabitantThreadR
        inhabitedCellStateR)).

Notation queueContentsUR :=
  (prodUR (listUR (optionUR cellStateR))
          (* a.d. size of the queue. TODO but why option? *)
          (optionUR (exclR natO))).

Notation enqueueUR := natUR.
Notation dequeueUR := (prodUR natUR max_natUR).
Notation algebra := (authUR (prodUR (prodUR enqueueUR dequeueUR)
                                    queueContentsUR)).

Class threadQueueG Σ := ThreadQueueG { thread_queue_inG :> inG Σ algebra }.
Definition threadQueueΣ : gFunctors := #[GFunctor algebra].
Instance subG_threadQueueΣ {Σ} : subG threadQueueΣ Σ -> threadQueueG Σ.
Proof. solve_inG. Qed.

Context `{heapG Σ} `{iteratorG Σ} `{threadQueueG Σ} `{callbackG Σ}.
Variable (N : namespace).
Let NTq := N .@ "tq".
Let NArr := N .@ "array".
Let NDeq := N .@ "deq".
Let NEnq := N .@ "enq".
Notation iProp := (iProp Σ).

(* a.d. TODO can we make R persistent here? *)
Record thread_queue_parameters :=
  ThreadQueueParameters
    {
      enqueue_resource: iProp;
      dequeue_resource: iProp;
    }.

Variable parameters: thread_queue_parameters.
Let E := enqueue_resource parameters.
Let R := dequeue_resource parameters.
(* the value is always unit. *)
(* Definition V : base_lit -> iProp := λ x, (⌜ x = LitUnit ⌝)%I. *)

Global Instance base_lit_inhabited: Inhabited base_lit.
Proof. repeat econstructor. Qed.

Definition cellTerminalState_ra (r : cellTerminalState) :=
  match r with
  | cellResumed => Cinl (to_agree #())
  | cellImmediatelyCancelled => Cinr (to_agree ())
  end.

Definition cellState_ra (state: cellState): cellStateR :=
  match state with
  | cellPassedValue d => Cinl (to_agree #(), option_map to_agree d)
  | cellInhabited γk k r => Cinr (to_agree (γk, k),
                                option_map cellTerminalState_ra r)
  end.

(* a.d. one fragment of the algebra, it describes the state of one cell. *)
Definition rendezvous_state γtq i (r: option cellStateR) :=
  own γtq (◯ (ε, ({[ i := r ]}, ε))).

Global Instance rendezvous_state_persistent γtq i (r: cellStateR):
  CoreId r -> Persistent (rendezvous_state γtq i (Some r)).
Proof. apply _. Qed.

(* a.d. knowledge that there is a callback k that inhabits cell i. *)
Definition inhabited_rendezvous_state γtq i (r: inhabitedCellStateR): iProp :=
  ∃ γk k, rendezvous_state γtq i (Some (Cinr (to_agree (γk, k), r))).

Global Instance inhabited_rendezvous_state_persistent γtq i r:
  CoreId r -> Persistent (inhabited_rendezvous_state γtq i r).
Proof. apply _. Qed.

(* a.d. knowledge that there is a value v which fills cell i. *)
Definition filled_rendezvous_state γtq i r: iProp :=
  rendezvous_state γtq i (Some (Cinl (to_agree #(), r))).

Global Instance filled_rendezvous_state_persistent γtq i r:
  CoreId r -> Persistent (filled_rendezvous_state γtq i r).
Proof. apply _. Qed.

(* a.d. n is the size of the thread queue. *)
Definition thread_queue_state γ (n: nat) :=
  own γ (◯ (ε, (ε, Excl' n))).

Global Instance thread_queue_state_timeless:
  Timeless (thread_queue_state γ n).
Proof. apply _. Qed.

(* a.d. knowledge that the dequeue front has a certain size. *)
Definition deq_front_at_least γtq (n: nat) :=
  own γtq (◯ (ε, (ε, MaxNat n), ε)).

(* a.d. knowledge that cell i is inhabited by callback k. *)
Definition rendezvous_thread_locs_state (γtq γk: gname) (k: val) (i: nat): iProp :=
  rendezvous_state γtq i (Some (Cinr (to_agree (γk, k), None))).

Global Instance rendezvous_thread_locs_state_persistent γtq γk k i:
  Persistent (rendezvous_thread_locs_state γtq γk k i).
Proof. apply _. Qed.

(* a.d. knowledge that cell i is filled with value v. *)
Definition rendezvous_filled_value (γtq: gname) (v: val) (i: nat): iProp :=
  rendezvous_state γtq i (Some (Cinl (to_agree v, None))).

Definition V' (v: val): iProp := ⌜v = #()⌝ ∗ R.

(* Definition is_callback (P: val -> iProp) (k: val): iProp :=
  (⌜k ≠ #()⌝ ∗ ∀ v, P v -∗ WP (k v) {{_, True}}). *)

(* a.d. knowledge that cell i is inhabited by callback k.
   Because we removed future we just save the pure knowledge that k is not unit (bc it's a callback). *)
Definition rendezvous_thread_handle (γtq γk: gname) (k: val) (i: nat): iProp :=
  (⌜k ≠ #()⌝ ∗ ⌜k ≠ #1⌝ ∗ ⌜ val_is_unboxed (InjLV k)⌝ ∗ rendezvous_thread_locs_state γtq γk k i)%I.

(* a.d. I expect it is important that this is persistent. But the waker is certainly not persistent.
   Maybe we need to put it in an invariant like this:
        inv (P v -> WP (k v) {⊤}) ∨ wakerToken)
   Then we keep the wakerToken somewhere and to run the waker you need to give up the token.  
*)
Global Instance rendezvous_thread_handle_persistent γtq γk k i:
  Persistent (rendezvous_thread_handle γtq γk k i).
Proof. apply _. Qed.

(* a.d. the cell_is_owned predicate for the infinite array. 
  a fresh cell can go into two directions, depending on if suspend() or resume() reaches it first.

  suspend(): cell goes to inhabited, as in a future inhabits the cell
  resume(v): cell goes to filled, as in the cell is filled with the value v.
*)
Definition rendezvous_initialized γtq i: iProp :=
  inhabited_rendezvous_state γtq i ε ∨ filled_rendezvous_state γtq i ε.

Definition suspension_permit γ := own γ (◯ (1%nat, ε, ε)).

Definition awakening_permit γ := own γ (◯ (ε, (1%nat, ε), ε)).

Variable array_interface: infiniteArrayInterface.
Variable array_spec: infiniteArraySpec _ array_interface.

Let cell_location γtq :=
  infinite_array_mapsto _ _ array_spec NArr (rendezvous_initialized γtq).

Let cancellation_handle := cell_cancellation_handle _ _ array_spec NArr.
Let cell_cancelled := cell_is_cancelled _ _ array_spec NArr.

(* a.d. 

To describe the resources the cell owns at various states, we first need to introduce a helpful ownership
pattern. We say that T is owned as a resource for resumer if one of the following is true:
– The Future completion permit for f and T is owned;
– Half the Future completion permit, the i’th permit from the dequeue iterator, and T is owned;
– The Future completion permit for f and the i’th permit from the dequeue iterator is owned. 

a.d. TODO we probably need something similar for our formulation with a waker instead of a future.
  But since the callback cannot be cancelled we don't have to do it so complicated.
  It would just be the invariant described above, some callback_invokation_permit together with the WP. *)



Definition resources_for_resumer T γf γd i: iProp :=
  ((callback_invokation_permit γf 1%Qp ∨
    callback_invokation_permit γf (1/2)%Qp ∗ iterator_issued γd i) ∗ T ∨
   callback_invokation_permit γf 1%Qp ∗ iterator_issued γd i).

(* a.d. I think this is the big cell state transition system (or at least just all the cell states, lemmas would describe which transitions are allowed.

γtg : ghost cell for thread queue
γa  : ghost cell for infinite array
γe  : ghost cell for enqueue iterator
γd  : ghost cell for dequeue iterator
i   : index of the cell
k   : state of the cell
insideDeqFront : if i < deqFront, if so we know that dequeue registration happened.

*)
Definition cell_resources
           γtq γa γe γd i (k: option cellState) (insideDeqFront: bool):
  iProp :=
  match k with
  (* a.d. 
  EMPTY. By definition of a relevant cell, E was passed to it during the enqueue registration, and no state
transitions happened yet to extract that resource, so the cell owns a E. Additionally, it is possible that the cell
is already inside the dequeue front, in which case the cell also owns an R.
  *)
  | None => E ∗ if insideDeqFront then R else True%I
(* a.d.
resume(v) arrived first. If the call to resume(v) was the first to modify the cell, we have the following:
– The cell owns the cancellation permit for the infinite array cell, meaning that the cell is never going to
be cancelled;
– The cell owns the i’th permit from the dequeue iterator. *)
  | Some (cellPassedValue d) =>
    iterator_issued γd i ∗
    cancellation_handle γa i ∗
    ∃ ℓ, cell_location γtq γa i ℓ ∗
(* a.d. There are some additional resources that the cell owns, depending on its state: *)
         match d with
(* a.d.
– SUCCESS-ASYNC. The cell contains some value v and owns an R.
Transition from EMPTY to this state happens in the asynchronous resumption mode when the resumer
writes its value to the cell, relinquishing the i’th permit from the dequeue iterator in exchange for E.
The cell was inside the deque front, so it owned an R.
*)
         | None => ℓ ↦ EIORESUMEDV ∗ R
(* a.d. 
– SUCCESS. The cell still contains the value (since it's always unit) and owns the i’th permit from the enqueue iterator.
Transition from SUCCESS-ASYNC happens when suspend() provides its i’th permit from the enqueue iterator in exchange for R.
 *)
         | Some () => ℓ ↦ EIORESUMEDV ∗ iterator_issued γe i
         end
  | Some (cellInhabited γk k r) =>
(* a.d. 
suspend() arrived first. If the call to suspend() was the first to modify the cell, writing a callback to it, the
following is true:
– The cell owns the i’th permit from the enqueue iterator.
– There exists an R-passing callback which is in one of the following states *)
    iterator_issued γe i ∗ 
    (* a.d. TODO this might be unnecessary. *)
    rendezvous_thread_handle γtq γk k i ∗
    ∃ ℓ, cell_location γtq γa i ℓ ∗
         match r with
         (* CALLBACK WAITING
            The callback has neither been invoked nor cancelled, so it is just waiting.
            In this case it still owns E and and R if dequeue registration already happened. *)
         | None => ℓ ↦ InjLV k ∗ cancellation_handle γa i ∗
                  E ∗ (if insideDeqFront then R else True) ∗
                  (* this describes the logical state of the callack. A waiting callback contains the WP 
                      asserting that the closure is safe to execute. *)
                  callback_invariant V' γk k CallbackWaiting ∗
                  (* a.d. TODO I think this can just be callback_invokation_permit γk 1 *)
                  (callback_invokation_permit γk 1%Qp ∨
                   callback_invokation_permit γk (1/2)%Qp ∗
                   iterator_issued γd i)
         (* RESUMED *)
         | Some (cellResumed) =>
           (* a.d. TODO why have the disjunction? I think I should only have EIORESUMEDV *)
           ℓ ↦ EIORESUMEDV ∗
           iterator_issued γd i ∗
           cancellation_handle γa i ∗
           callback_invariant V' γk k (CallbackInvoked #())
         (* CALLBACK SIMPLY CANCELLED *)
         | Some cellImmediatelyCancelled =>
           (* a.d. TODO why have the disjunction? I think I should only have CANCELLEDV *)
           ℓ ↦ CANCELLEDV ∗
           (* future_is_cancelled γf ∗ *)
           callback_invariant V' γk k CallbackCancelled ∗
           (* resources_for_resumer (if insideDeqFront then R else True) γk γd i *)
           (* a.d. since I have a simpler state transition system it could work that I just have the resource here. *)
           (resources_for_resumer (if insideDeqFront then R else True) γk γd i)
         end
  end.

Definition is_immediately_cancelled (r: option cellState): bool :=
  match r with
  | Some (cellInhabited γt th (Some cellImmediatelyCancelled)) => true
  | _ => false
  end.

Definition cell_list_contents_auth_ra l (deqFront: nat): algebra :=
  ● (length l, (deqFront, MaxNat deqFront),
     (map (option_map cellState_ra) l,
(* Finally, the size of a CQS is defined to be the number of nonskippable relevant cells outside the deque front. This is
the value in terms of which the programmer-facing specifications are defined. *)
      Excl' (length (drop deqFront l)))).

Lemma rendezvous_state_included γ l deqFront i s:
  own γ (cell_list_contents_auth_ra l deqFront) -∗
  rendezvous_state γ i s -∗
  ⌜∃ c, l !! i = Some c ∧ s ≼ option_map cellState_ra c⌝.
Proof.
  iIntros "H● H◯".
  iDestruct (own_valid_2 with "H● H◯")
    as %[[_ [(v&HEl&HInc)%list_singletonM_included _]%prod_included
         ]%prod_included _]%auth_both_valid.
  simpl in *. iPureIntro.
  rewrite map_lookup in HEl.
  destruct (l !! i) as [el|]; simpl in *; simplify_eq.
  eexists. by split.
Qed.

Lemma rendezvous_state_included' γ l deqFront i s:
  own γ (cell_list_contents_auth_ra l deqFront) -∗
  rendezvous_state γ i (Some s) -∗
  ⌜∃ c, l !! i = Some (Some c) ∧ s ≼ cellState_ra c⌝.
Proof.
  iIntros "H● H◯".
  iDestruct (rendezvous_state_included with "H● H◯") as %(c & HEl & HInc).
  iPureIntro.
  destruct c as [el|]; last by apply included_None in HInc.
  simpl in *. eexists. split; first done. move: HInc.
  rewrite Some_included.
  case; last done. intros ->.
  destruct el as [r|γth f r]; simpl.
  + by apply Cinl_included.
  + by apply Cinr_included.
Qed.

Lemma thread_queue_state_valid γtq n l deqFront:
  own γtq (cell_list_contents_auth_ra l deqFront) -∗
  thread_queue_state γtq n -∗
  ⌜n = length (drop deqFront l)⌝.
Proof.
  iIntros "H● HState".
  iDestruct (own_valid_2 with "H● HState")
    as %[[_ [_ HEq%Excl_included]%prod_included]%prod_included
                                                _]%auth_both_valid.
  by simplify_eq.
Qed.

Theorem cell_list_contents_ra_locs γ l deqFront i γt th:
  own γ (cell_list_contents_auth_ra l deqFront) -∗
  rendezvous_thread_locs_state γ γt th i -∗
  ⌜exists c, l !! i = Some (Some (cellInhabited γt th c))⌝.
Proof.
  iIntros "H● H◯".
  iDestruct (rendezvous_state_included' with "H● H◯") as %([|] & HEl & HInc).
  all: iPureIntro; simpl in *.
  - exfalso. move: HInc. rewrite csum_included. case; first done.
    case.
    * by intros (? & ? & HContra & _).
    * by intros (? & ? & ? & HContra & _).
  - move: HInc. rewrite Cinr_included prod_included=> /=. case.
    rewrite to_agree_included. case=>/=. intros <- <- _.
    by eexists.
Qed.

(* a.d. so this is why we have the option around cell state.
   this defines some general knowledge that the cell i exists but nothing else. *)
Definition cell_enqueued γtq (i: nat): iProp :=
  rendezvous_state γtq i ε.

(* Which is proven by this lemma. Given a cell_enqueued we know there is some cell at index i. *)
Theorem cell_enqueued_lookup γtq l i d:
  own γtq (cell_list_contents_auth_ra l d) -∗
  cell_enqueued γtq i -∗
  ⌜exists v, l !! i = Some v⌝.
Proof.
  iIntros "H● HExistsEl".
  iDestruct (rendezvous_state_included with "H● HExistsEl") as %(c & HEl & _).
  iPureIntro. eauto.
Qed.

(* Two logical values are maintained: the dequeue front, and the cell state list. The deque front is the first cell about
which it is not yet known that its state is going to be observed by resume(v) or already was. A cell is inside the deque
front if its index is less than the deque front. Cell state list stores the authoritative knowledge of the state of each
relevant cell in the infinite array; a cell is considered relevant if it is known that its state is going to be observed by a
call to suspend() or already was.

The last cell inside the deque front must be a relevant cell, which effectively means that we forbid calling resume(v)
unless it is known that the corresponding suspend() is also eventually going to be called.

The deque front is nondecreasing, which is in line with its definition: once it is known that a cell is about to be
witnessed by a call to resume(v), this can not become false. Likewise, the length of the cell state list can not decrease
with time.

a.d. l is the "cell state list" *)
(* For each relevant cell, there exists a single instance of a logical resource called the suspension permit. For each cell
before the deque front, there exists a single instance of a logical resource called the awakening permit.
  
  concretely, the cell_list_contents_auth_ra has a `length l`, which is the sum of all suspension permits
              analogously, deqFront is the sum of all awakening permits.
*)
Definition thread_queue_invariant γa γtq γe γd l deqFront: iProp :=
  own γtq (cell_list_contents_auth_ra l deqFront) ∗
      ([∗ list] i ↦ e ∈ l, cell_resources γtq γa γe γd i e
                                          (bool_decide (i < deqFront))) ∗
      ⌜deqFront ≤ length l⌝.

(* Physically, a CQS consists of an infinite array and two iterators, one, the enqueue iterator, bounded by the suspension
permits, and another, the dequeue iterator, bounded by awakening permits.
 *)
Definition is_thread_queue γa γtq γe γd e d :=
(* here we instantiate the cell_is_owned predicate, either it is "inhabited" or "filled". *)
  let co := rendezvous_initialized γtq in
  (inv NTq (∃ l deqFront, thread_queue_invariant γa γtq γe γd l deqFront) ∗
   is_infinite_array _ _ array_spec NArr γa co ∗
   is_iterator _ array_spec NArr NEnq co γa (suspension_permit γtq) γe e ∗
   is_iterator _ array_spec NArr NDeq co γa (awakening_permit γtq) γd d)%I.

Theorem newThreadQueue_spec:
  {{{ inv_heap_inv }}}
    newThreadQueue array_interface #()
  {{{ γa γtq γe γd e d, RET (e, d); is_thread_queue γa γtq γe γd e d
      ∗ thread_queue_state γtq 0 }}}.
Proof.
  iIntros (Φ) "HHeap HΦ". wp_lam. wp_bind (newInfiniteArray _ _).
  rewrite -fupd_wp.
  iMod (own_alloc (cell_list_contents_auth_ra [] 0
                   ⋅ ◯ (ε, (ε, Excl' 0)))) as (γtq) "[H● H◯]".
  { apply auth_both_valid. split=> /=.
    - apply pair_included. split; first by apply ucmra_unit_least.
      apply pair_included. split; first by apply ucmra_unit_least.
      done.
    - apply pair_valid. split; first done.
      apply pair_valid. split; last done. apply list_lookup_valid.
      by case. }
  replace 2%Z with (Z.of_nat 2); last lia.
  iApply (newInfiniteArray_spec with "[HHeap]").
  { iSplitR. by iPureIntro; lia. done. }
  iIntros "!> !>" (γa aℓ) "[HArr (HE & HD & _)]". wp_pures.
  wp_bind (newIterator _ _).
  replace 0%Z with (Z.of_nat 0); last lia.
  iApply (newIterator_spec with "[HD]"); first by simpl; iFrame.
  iIntros "!>" (γd d) "HDeq".
  wp_bind (newIterator _ _). wp_pures. rewrite -wp_fupd.
  iApply (newIterator_spec with "[HE]"); first by simpl; iFrame.
  iIntros "!>" (γe e) "HEnq".
  iMod (inv_alloc NTq _
        (∃ l deqFront, thread_queue_invariant γa γtq γe γd l deqFront)
       with "[H●]") as "#HInv".
  { iExists [], 0. iFrame. simpl. iPureIntro. split; done.
    }
  iSpecialize ("HΦ" $! γa γtq γe γd e d).
  iModIntro. wp_pures. iApply "HΦ". by iFrame.
Qed.

Theorem thread_queue_append γtq γa γe γd n l deqFront:
  ▷ E -∗ thread_queue_state γtq n -∗
  ▷ thread_queue_invariant γa γtq γe γd l deqFront ==∗
  ▷ (suspension_permit γtq ∗ cell_enqueued γtq (length l) ∗
  thread_queue_state γtq (S n) ∗
  thread_queue_invariant γa γtq γe γd (l ++ [None]) deqFront).
Proof.
  iIntros "HE H◯ (>H● & HRRs & >HLen)".
  iDestruct (thread_queue_state_valid with "H● H◯") as %->.
  iDestruct "HLen" as %HLen.
  iMod (own_update_2 with "H● H◯") as "[H● [[$ $] $]]".
  2: {
    rewrite /thread_queue_invariant app_length big_sepL_app=>/=.
    iFrame "HE H● HRRs". 
    iSplitR; first by rewrite bool_decide_false; last lia.
    iPureIntro.
    lia.
  }
  {
    apply auth_update, prod_local_update'; last apply prod_local_update'=> /=.
    * rewrite app_length=>/=.
      apply prod_local_update_1=>/=.
      by apply nat_local_update.
    * rewrite map_app=> /=.
      replace (length l) with (length (map (option_map cellState_ra) l))
        by rewrite map_length //.
      rewrite ucmra_unit_right_id.
      apply list_append_local_update=> ?.
      apply list_lookup_validN. by case.
    * etransitivity.
      by apply delete_option_local_update, _.
      rewrite drop_app_le; last lia.
      rewrite app_length=>/=.
      move=>/=.
      rewrite Nat.add_1_r.
      by apply alloc_option_local_update.
  }
Qed.

(* a.d. Enqueue registration It is possible to provide an E, increasing the size and obtaining in exchange a suspension
permit — a permission to call suspend(). *)
Theorem thread_queue_append' E' γtq γa γe γd n e d:
  ↑NTq ⊆ E' ->
  is_thread_queue γa γtq γe γd e d -∗
  ▷ E -∗ ▷ thread_queue_state γtq n ={E'}=∗
  thread_queue_state γtq (S n) ∗ suspension_permit γtq.
Proof.
  iIntros (HMask) "[HInv _] HE >HState".
  iInv "HInv" as (l deqFront) "HOpen" "HClose".
  iMod (thread_queue_append with "HE HState HOpen") as "(>$ & _ & >$ & HRest)".
  iMod ("HClose" with "[HRest]") as "_"; last done. by iExists _, _.
Qed.

Global Instance deq_front_at_least_persistent γtq n:
  Persistent (deq_front_at_least γtq n).
Proof. apply _. Qed.

Theorem deq_front_at_least_valid γtq n l deqFront :
  own γtq (cell_list_contents_auth_ra l deqFront) -∗
  deq_front_at_least γtq n -∗
  ⌜n <= deqFront⌝.
Proof.
  iIntros "H● H◯".
  iDestruct (own_valid_2 with "H● H◯") as %[HValid _]%auth_both_valid.
  apply prod_included in HValid. destruct HValid as [HValid _].
  apply prod_included in HValid. destruct HValid as [_ HValid].
  apply prod_included in HValid. destruct HValid as [_ HValid].
  apply max_nat_included in HValid. simpl in *.
  iPureIntro; simpl in *; lia.
Qed.

Theorem cell_list_contents__deq_front_at_least i γtq l deqFront:
  (i <= deqFront)%nat ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra l deqFront) ∗
  deq_front_at_least γtq i.
Proof.
  iIntros (HLe) "H●".
  iMod (own_update with "H●") as "[$ $]"; last done.
  apply auth_update_core_id.
  by apply _.
  repeat (apply prod_included; split); simpl.
  all: try apply ucmra_unit_least.
  apply max_nat_included. simpl. lia.
Qed.

Lemma None_op_right_id (A: cmraT) (a: option A): a ⋅ None = a.
Proof. by destruct a. Qed.

Lemma cell_list_contents_cell_update_alloc s
      γtq l deqFront i initialState newState:
  l !! i = Some initialState ->
  (Some (option_map cellState_ra initialState), None) ~l~>
  (Some (option_map cellState_ra newState),
   Some s) ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra (<[i := newState]> l) deqFront) ∗
  rendezvous_state γtq i s.
Proof.
  iIntros (HEl HUp) "H●".
  iMod (own_update with "H●") as "($ & $)"; last done.
  apply auth_update_alloc. rewrite insert_length.
  apply prod_local_update_2, prod_local_update=> /=.
  - rewrite -!fmap_is_map list_fmap_insert.
    apply list_lookup_local_update=> i'. rewrite lookup_nil.
    destruct (lt_eq_lt_dec i' i) as [[HLt| ->]|HGt].
    + rewrite list_lookup_singletonM_lt; last lia.
      rewrite list_lookup_insert_ne; last lia.
      rewrite map_lookup.
      assert (is_Some (l !! i')) as [? ->].
      { apply lookup_lt_is_Some. apply lookup_lt_Some in HEl. lia. }
      apply option_local_update'''. by rewrite ucmra_unit_left_id.
      intros n. by rewrite ucmra_unit_left_id.
    + rewrite list_lookup_singletonM list_lookup_insert.
      2: { eapply lookup_lt_Some. by rewrite map_lookup HEl. }
      by rewrite map_lookup HEl=> /=.
    + rewrite list_lookup_singletonM_gt; last lia.
      rewrite list_lookup_insert_ne; last lia.
      done.
  - by rewrite !drop_length insert_length.
Qed.

(* a.d. how we update our knowledge when inhabiting a cell with a callback. *)
Lemma inhabit_cell_ra γtq l deqFront i γf f:
  l !! i = Some None ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra
             (<[i := Some (cellInhabited γf f None)]> l) deqFront) ∗
  rendezvous_thread_locs_state γtq γf f i.
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "($ & $)"; try done.
  apply option_local_update'''.
  by rewrite None_op_right_id.
  intros n. by rewrite None_op_right_id.
Qed.

Lemma rendezvous_state_op γtq i a b:
  rendezvous_state γtq i a ∗ rendezvous_state γtq i b ⊣⊢
  rendezvous_state γtq i (a ⋅ b).
Proof.
  rewrite /rendezvous_state -own_op -auth_frag_op -pair_op.
  rewrite ucmra_unit_left_id -pair_op list_singletonM_op //.
Qed.

(* a.d. how we update our knowledge when filling a cell with a value. *)
Lemma fill_cell_ra γtq l deqFront i:
  l !! i = Some None ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra
             (<[i := Some (cellPassedValue None)]> l) deqFront) ∗
  rendezvous_state γtq i (Some (Cinl (to_agree #(), ε))).
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "($ & H◯)"=>//=.
  apply option_local_update'''. by rewrite None_op_right_id.
  intros n. by rewrite None_op_right_id.
Qed.

(* a.d. how we update our knowledge when taking the value out of a filled cell. *)
Lemma take_cell_value_ra γtq l deqFront i:
  l !! i = Some (Some (cellPassedValue None)) ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra
             (<[i := Some (cellPassedValue (Some ()))]> l) deqFront) ∗
  rendezvous_state γtq i (Some (Cinl (to_agree #(), Some (to_agree ())))).
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "[$ $]"=> //=.
  apply option_local_update'''=> [|n];
    by rewrite -Some_op -Cinl_op -!pair_op None_op_right_id agree_idemp.
Qed.

(* a.d. TODO what is this and how is it different from the cell_list_contents_cell_update_alloc.
  For this one we have to give up a rendezvous_state and get back a new one.
  But I'm unsure about how the local update is used and why the other lemma has an extra None/Some
*)
Lemma cell_list_contents_cell_update newState initialState s s'
      γtq l deqFront i:
  l !! i = Some initialState ->
  i < deqFront ->
  (option_map cellState_ra initialState, s) ~l~>
  (option_map cellState_ra newState, s') ->
  own γtq (cell_list_contents_auth_ra l deqFront) -∗
  rendezvous_state γtq i s ==∗
  own γtq (cell_list_contents_auth_ra (<[i := newState]> l) deqFront) ∗
  rendezvous_state γtq i s'.
Proof.
  iIntros (HEl HDeqFront HUp) "H● H◯".
  iMod (own_update_2 with "H● H◯") as "($ & $)"; last done.
  apply auth_update. rewrite insert_length.
  apply prod_local_update_2, prod_local_update=> /=.
  - rewrite -!fmap_is_map list_fmap_insert.
    apply list_lookup_local_update=> i'.
    destruct (lt_eq_lt_dec i' i) as [[HLt| ->]|HGt].
    + rewrite !list_lookup_singletonM_lt; try lia.
      rewrite list_lookup_insert_ne; last lia.
      by rewrite map_lookup.
    + rewrite !list_lookup_singletonM list_lookup_insert.
      2: { eapply lookup_lt_Some. by rewrite map_lookup HEl. }
      rewrite map_lookup HEl=> /=.
      apply option_local_update, HUp.
    + rewrite !list_lookup_singletonM_gt; try lia.
      rewrite list_lookup_insert_ne; last lia.
      done.
  - by rewrite drop_insert_gt; last lia.
Qed.

(* a.d. how we update our knowledge when immediately cancelling a cell. *)
Lemma immediately_cancel_cell_ra γtq γk k l deqFront i:
  l !! i = Some (Some (cellInhabited γk k None)) ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra
             (<[i := Some (cellInhabited γk k (Some cellImmediatelyCancelled))]> l) deqFront) ∗
  rendezvous_state γtq i (Some (Cinr (to_agree (γk, k), Some (Cinr (to_agree ()))))).
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "($ & $)"=> //=.
  apply option_local_update'''=> [|n];
    by rewrite -Some_op -Cinr_op -!pair_op None_op_right_id !agree_idemp.
Qed.

Lemma resumed_cell_core_id_ra γtq γf f l deqFront i:
  l !! i = Some (Some (cellInhabited γf f (Some (cellResumed)))) ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra l deqFront) ∗
  rendezvous_state γtq i (Some (Cinr (to_agree (γf, f),
                                      Some (Cinl (to_agree #()))))).
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "(H● & $)"=> //=.
  2: by rewrite list_insert_id.
  apply option_local_update'''=> [|n];
    by rewrite -Some_op -Cinr_op -!pair_op -Some_op -Cinl_op !agree_idemp.
Qed.

Lemma resume_cell_ra γtq γf f l deqFront i:
  l !! i = Some (Some (cellInhabited γf f None)) ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra
             (<[i := Some (cellInhabited γf f (Some (cellResumed)))]> l) deqFront) ∗
  rendezvous_state γtq i (Some (Cinr (to_agree (γf, f), Some (Cinl (to_agree #()))))).
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "($ & $)"=> //=.
  apply option_local_update'''=> [|n];
    by rewrite -Some_op -Cinr_op -!pair_op None_op_right_id !agree_idemp.
Qed.

Lemma awakening_permit_combine γtq n:
  n > 0 ->
  ([∗] replicate n (awakening_permit γtq))%I ≡ own γtq (◯ (ε, (n, ε), ε)).
Proof.
  move=> Hn.
  rewrite big_opL_replicate_irrelevant_element -big_opL_own;
    last by inversion Hn.
  move: (big_opL_op_prodR 0)=> /= HBigOpL.
  rewrite -big_opL_auth_frag !HBigOpL !big_opL_op_ucmra_unit.
  rewrite -big_opL_op_nat' Nat.mul_1_r replicate_length.
  done.
Qed.

Lemma suspension_permit_combine γtq n:
  n > 0 ->
  ([∗] replicate n (suspension_permit γtq))%I ≡ own γtq (◯ (n, ε, ε)).
Proof.
  move=> Hn.
  rewrite big_opL_replicate_irrelevant_element -big_opL_own;
    last by inversion Hn.
  move: (big_opL_op_prodR 0)=> /= HBigOpL.
  rewrite -big_opL_auth_frag !HBigOpL !big_opL_op_ucmra_unit.
  rewrite -big_opL_op_nat' Nat.mul_1_r replicate_length.
  done.
Qed.

(* a.d. why i and S i? 
This seems to say: register i dequeue operations. But not sure why we get S i awakening permits in the end.
*)
Lemma deque_register_ra_update γ l deqFront i n:
  (i + deqFront < length l)%nat ->
  own γ (cell_list_contents_auth_ra l deqFront) -∗
  thread_queue_state γ n ==∗
  own γ (cell_list_contents_auth_ra l (deqFront + S i))
  ∗ [∗] replicate (S i) (awakening_permit γ)
  ∗ thread_queue_state γ
      (n - length (take (S i) (drop deqFront l)))
  ∗ deq_front_at_least γ (deqFront + S i).
Proof.
  rewrite awakening_permit_combine; last lia.
  iIntros (?) "H● H◯".
  iMod (own_update_2 with "H● H◯") as "($ & $ & $ & $)"; last done.
  apply auth_update, prod_local_update=>/=.
  apply prod_local_update_2, prod_local_update=>/=.
  - rewrite ucmra_unit_right_id. by apply nat_local_update.
  - apply max_nat_local_update; simpl; lia.
  - apply prod_local_update_2. rewrite ucmra_unit_right_id=>/=.
    apply local_update_total_valid=> _ _. rewrite Excl_included=> ->.
    etransitivity. by apply delete_option_local_update, _.
    rewrite take_length_le; rewrite !drop_length.
    2: by lia.
    replace (length l - (deqFront + S i)) with (length l - deqFront - S i) by lia.
      by apply alloc_option_local_update.
Qed.

Lemma find_drop_lt {A} (l: list A) j i:
  find_index (λ _, True) (drop j l) = Some i → j < length l.
Proof.
  intros HFindSome.
  apply find_index_Some in HFindSome as [(v & HEl & _) _].
  rewrite lookup_drop in HEl.
  apply (le_lt_trans _ (j+i)). lia. 
  apply lookup_lt_is_Some. by exists v.
Qed.

Lemma advance_deqFront deqFront l γtq γa γe γd:
  deqFront < length l ->
  ▷ R -∗
  ▷ ([∗ list] k ↦ y ∈ l, cell_resources γtq γa γe γd k y
                                        (bool_decide (k < deqFront))) -∗
  ▷ ([∗ list] k ↦ y ∈ l, cell_resources γtq γa γe γd k y
                                        (bool_decide (k < deqFront + 1))).
Proof.
  iIntros (Hlen) "HR HRRs".
  pose proof (lookup_lt_is_Some_2 _ _ Hlen) as (v & HEl).
  erewrite <-(take_drop_middle l _ v); last done.
  rewrite !big_sepL_app=>/=.
  iDestruct "HRRs" as "(HInit & H & HTail)".
  apply lookup_lt_Some in HEl. rewrite take_length_le; last lia.
  iSplitL "HInit"; last iSplitR "HTail".
  * 
    { iApply (big_sepL_mono with "HInit"). iIntros (k x HEl') "H".
      assert (k < deqFront)%nat.
      { apply lookup_lt_Some in HEl'.
        by rewrite take_length_le in HEl'; last lia. }
      iEval (rewrite bool_decide_true; last lia).
      rewrite bool_decide_true; last lia. done. }
  * rewrite bool_decide_false; last lia.
    rewrite bool_decide_true; last lia.
    rewrite Nat.add_0_r.
    rewrite /cell_resources.
    destruct v as [[|? ? [[|]|]]|]=>//.
    + iDestruct "H" as "($ & $ & H)". iDestruct "H" as (?) "H".
      iExists _. 
      iDestruct "H" as "($ & $ & $ & H)".
      iDestruct "H" as "[[H _]|H]"; [iLeft|iRight]; iFrame; done.
    + iDestruct "H" as "($ & $ & H)".
      iDestruct "H" as (?) "H".
      iExists _. iDestruct "H" as "($ & $ & $ & $ & _ & $)".
      by done.
    + iDestruct "H" as "($ & _)". 
      by done.
  * iApply (big_sepL_mono with "HTail"). iIntros (? ? ?) "H".
    rewrite !bool_decide_false; first done; lia.
Qed.

(* Lemma advance_deqFront_pure deqFront l:
  deqFront < length l ->
   ∧ (S deqFront > 0
      ∧ (∃ r : option cellState,
           l !! deqFront = Some r ∧ is_skippable r) → False).
Proof.
  intros HFindSome.
  apply find_index_Some in HFindSome.
  destruct HFindSome as [(v & HEl & HNonSkippable) HRestSkippable].
  rewrite lookup_drop in HEl.
  assert (deqFront + i < length l); first by apply lookup_lt_Some in HEl.
  split; first lia. case. intros _ (v' & HEl' & HNonSkippable').
  replace (_ - _) with (deqFront + i) in HEl' by lia.
  simplify_eq. rewrite /is_nonskippable in HNonSkippable.
  destruct (is_skippable v); contradiction.
Qed. *)


Lemma thread_queue_register_for_dequeue γtq γa γe γd l deqFront n:
  deqFront < length l ->
  ▷ R -∗ ▷ thread_queue_invariant γa γtq γe γd l deqFront -∗
  ▷ thread_queue_state γtq n ==∗
  ▷ (awakening_permit γtq
  ∗ deq_front_at_least γtq (deqFront + 1)
  ∗ thread_queue_invariant γa γtq γe γd l (deqFront + 1)
  ∗ thread_queue_state γtq (n - 1)).
Proof.
  iIntros (HLen) "HR (>H● & HRRs & _) >H◯".
  (* move: (present_cells_in_take_Si_if_next_present_is_Si _ _ _ HFindSome)
    => HPresentCells.
  assert (find_index is_nonskippable (drop deqFront l) = Some i) as HFindSome';
    first done. *)
  (* apply find_index_Some in HFindSome. *)
  (* destruct HFindSome as [(v & HEl & HNonSkippable) HRestSkippable]. *)
  (* rewrite lookup_drop in HEl.
  assert (deqFront + i < length l); first by apply lookup_lt_Some in HEl. *)
  iMod (deque_register_ra_update with "H● H◯")
    as "($ & HAwaks & H◯ & $)"; first lia.
  simpl. iDestruct "HAwaks" as "[$ _]".
  rewrite take_length_le; last by rewrite drop_length; lia.
  iFrame "H◯".
  iDestruct (advance_deqFront _ _ _ _ _ _ HLen with "HR HRRs") as "$".
  iPureIntro. by lia.
Qed.

(* a.d. Dequeue registration If it is known that the size is nonzero, it is possible to decrease the size and provide an R,
obtaining in exchange an awakening permit — a permission to call resume(v). *)
Theorem thread_queue_register_for_dequeue' E' γtq γa γe γd n e d:
  ↑NTq ⊆ E' ->
  n > 0 ->
  is_thread_queue γa γtq γe γd e d -∗
  ▷ R -∗ ▷ thread_queue_state γtq n ={E'}=∗
  thread_queue_state γtq (n - 1) ∗ awakening_permit γtq.
Proof.
  iIntros (HMask Hn) "[HInv _] HR >HState".
  iInv "HInv" as (l deqFront) "HOpen" "HClose".
  iAssert (▷⌜deqFront < length l⌝)%I with "[-]" as "#>HLen".
  { iDestruct "HOpen" as "[>H● _]".
    iDestruct (thread_queue_state_valid with "H● HState") as %->.
    rewrite drop_length in Hn.
    iPureIntro. lia. }
  iDestruct "HLen" as %HLen.
  iMod (thread_queue_register_for_dequeue with "HR HOpen HState")
       as "(>HAwak & _ & HOpen & >HState)"=> //.
  iFrame. iMod ("HClose" with "[HOpen]"); last done.
  by iExists _, _.
Qed.

Lemma awakening_permit_implies_bound γtq l deqFront n:
  own γtq (cell_list_contents_auth_ra l deqFront) -∗
  ([∗] replicate n (awakening_permit γtq)) -∗
  ⌜n <= deqFront⌝.
Proof.
  iIntros "H● HAwaks".
  destruct n; first by iPureIntro; lia.
  rewrite awakening_permit_combine; last lia.
  iDestruct (own_valid_2 with "H● HAwaks")
    as %[[[_ [HValid%nat_included _]%prod_included]%prod_included
             ]%prod_included _]%auth_both_valid.
  simpl in *. iPureIntro; lia.
Qed.

Lemma suspension_permit_implies_bound γtq l deqFront n:
  own γtq (cell_list_contents_auth_ra l deqFront) -∗
  ([∗] replicate n (suspension_permit γtq)) -∗
  ⌜n <= length l⌝.
Proof.
  iIntros "H● HSuspends".
  destruct n; first by iPureIntro; lia.
  rewrite suspension_permit_combine; last lia.
  iDestruct (own_valid_2 with "H● HSuspends")
    as %[[[HValid%nat_included _]%prod_included
             _]%prod_included _]%auth_both_valid.
  simpl in *. iPureIntro; lia.
Qed.

Global Instance is_thread_queue_persistent γa γ γe γd e d:
  Persistent (is_thread_queue γa γ γe γd e d).
Proof. apply _. Qed.

(* a.d. TODO rename *)
Lemma cell_cancelled_means_skippable γtq γa γe γd i b c:
  cell_cancelled γa i -∗
  cell_resources γtq γa γe γd i (Some c) b -∗
  ⌜is_immediately_cancelled (Some c)⌝.
Proof.
  iIntros "#HCancelled HRR".
  iAssert (cancellation_handle γa i -∗ False)%I with "[]" as "HContra".
  { iIntros "HCancHandle".
    iDestruct (cell_cancellation_handle_not_cancelled with
                   "HCancelled HCancHandle") as %[]. }
  destruct c as [c'|? ? c']=> /=.
  { iDestruct "HRR" as "(_ & HCancHandle & _)".
    iDestruct ("HContra" with "HCancHandle") as %[]. }
  iDestruct "HRR" as "(_ & _ & HRR)". iDestruct "HRR" as (ℓ) "[_ HRR]".
  destruct c' as [[|]|].
  - iDestruct "HRR" as "(_ & _ & HCancHandle & _)".
    iDestruct ("HContra" with "HCancHandle") as %[].
  - iPureIntro. done.
  - iDestruct "HRR" as "(_ & HCancHandle & _)".
    iDestruct ("HContra" with "HCancHandle") as %[].
Qed.

Lemma cell_cancelled_means_present E' γtq γa γe γd l deqFront ℓ i:
  ↑NArr ⊆ E' ->
  cell_cancelled γa i -∗
  cell_location γtq γa i ℓ -∗
  ▷ thread_queue_invariant γa γtq γe γd l deqFront ={E'}=∗
  ▷ thread_queue_invariant γa γtq γe γd l deqFront ∗
  ▷ ∃ c, ⌜l !! i = Some (Some c) ∧ is_immediately_cancelled (Some c)⌝.
Proof.
  iIntros (HSets) "#HCanc #H↦ (>H● & HRRs & >%)".
  iMod (acquire_cell _ _ _ _ _ _ with "H↦")
    as "[[#>HCellInit|[>Hℓ HCancHandle]] HCloseCell]"; first done.
  - iMod ("HCloseCell" with "[HCellInit]") as "_"; first by iLeft. iModIntro.
    iDestruct "HCellInit" as "[HCellInit|HCellInit]".
    + rewrite /inhabited_rendezvous_state. 
      iDestruct "HCellInit" as (? ?) "HCellInit".
      iDestruct (rendezvous_state_included' with "H● HCellInit") as
        %(c & HEl & _).
      iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
        first done.
      iDestruct (cell_cancelled_means_skippable with "HCanc HRR")
                   as "#HH".
      iSpecialize ("HRRsRestore" with "HRR").
      iFrame. iSplit; first by iPureIntro.
      iNext. iDestruct "HH" as %HH. iPureIntro. by eexists.
    + rewrite /filled_rendezvous_state. 
      iDestruct (rendezvous_state_included' with "H● HCellInit") as
        %(c & HEl & _).
      iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
        first done.
      iDestruct (cell_cancelled_means_skippable with "HCanc HRR")
                   as "#HH".
      iSpecialize ("HRRsRestore" with "HRR").
      iFrame. iSplit; first by iPureIntro.
      iNext. iDestruct "HH" as %HH. iPureIntro. by eexists.
  - iDestruct (cell_cancellation_handle_not_cancelled with "HCanc HCancHandle")
      as ">[]".
Qed.

(* ENTRY POINTS TO THE CELL ****************************************************)

Lemma deq_front_at_least_from_iterator_issued E' γa γtq γe γd e d i:
  ↑N ⊆ E' ->
  is_thread_queue γa γtq γe γd e d -∗
  iterator_issued γd i ={E'}=∗
  deq_front_at_least γtq (S i) ∗
  iterator_issued γd i.
Proof.
  iIntros (HMask) "(HInv & _ & _ & HD) HIsRes".
  iMod (access_iterator_resources with "HD [#]") as "HH"; first by solve_ndisj.
  by iDestruct (iterator_issued_is_at_least with "HIsRes") as "$".
  rewrite awakening_permit_combine; last lia.
  iDestruct "HH" as "[>HH HHRestore]".
  iInv NTq as (l deqFront) "(>H● & HRRs & HRest)" "HClose".
  rewrite -awakening_permit_combine; last lia.
  iDestruct (awakening_permit_implies_bound with "H● HH") as "#%".
  iMod (cell_list_contents__deq_front_at_least with "H●") as "[H● $]"; first lia.
  iFrame "HIsRes".
  iMod ("HClose" with "[-HH HHRestore]") as "_".
  { iExists _, _. iFrame. }
  by iMod ("HHRestore" with "HH").
Qed.

Lemma callback_is_not_unit γk k state:
  callback_invariant V' γk k state -∗ ⌜k ≠ #()⌝ ∗ callback_invariant V' γk k state.
Proof.
  iIntros "(H1 & (% & Rest) & H2)". by iFrame.
Qed.

Lemma inhabit_cell_spec γa γtq γe γd γk i ptr k e d:
  {{{ callback_invariant V' γk k CallbackWaiting ∗
      cell_location γtq γa i ptr ∗
      is_thread_queue γa γtq γe γd e d ∗
      callback_invokation_permit γk 1%Qp ∗
      iterator_issued γe i }}}
    CAS #ptr (InjLV #()) (InjLV k)
  {{{ (r: bool), RET #r;
      if r
      then rendezvous_thread_handle γtq γk k i
      else filled_rendezvous_state γtq i ε
           ∗ iterator_issued γe i
           ∗ callback_invariant V' γk k CallbackWaiting
           ∗ callback_invokation_permit γk 1%Qp }}}.
Proof.
  iIntros (Φ) "(HF & #H↦ & #(HInv & HInfArr & HE & _) & HInvoke & HEnq)
               HΦ".
  iAssert (⌜ k ≠ #() ⌝ ∗ ⌜ k ≠ #1 ⌝ ∗ ⌜ val_is_unboxed (InjLV k) ⌝ ∗ callback_invariant V' γk k CallbackWaiting)%I with "[HF]" as "(% & % & % & HF)".
  { iDestruct "HF" as "($ & (% & % & %) & H)". iFrame.
    repeat iSplit; done. }
  wp_bind (CmpXchg _ _ _).
  iMod (access_iterator_resources with "HE [#]") as "HH"; first done.
  by iApply (iterator_issued_is_at_least with "HEnq").
  iDestruct "HH" as "[HH HHRestore]".
  iInv "HInv" as (l' deqFront) "(>H● & HRRs & >HLen)" "HTqClose".
  iDestruct (suspension_permit_implies_bound with "H● HH") as "#>HH'".
  iDestruct "HH'" as %HLength. iSpecialize ("HHRestore" with "HH").
  destruct (lookup_lt_is_Some_2 l' i) as [c HEl]; first lia.
  destruct c as [[resolution|? ? resolution]|].
  - (* A value was already passed.
       a.d. so we abort and return a filled_rendezvous_state. *)
    iMod (own_update with "H●") as "[H● HCellFilled]".
    2: iDestruct ("HΦ" $! false with "[HCellFilled HEnq HF HInvoke]")
      as "HΦ". 
    2: by iFrame; iExists _.
    { (* with auth_update_core_id we can extract a persistent fraction out of the auth
         (namely that the cell is filled). We just need to prove that it holds using the HEl assumption. *)
      apply auth_update_core_id. by apply _.
      apply prod_included; split=>/=; first by apply ucmra_unit_least.
      apply prod_included; split=>/=; last by apply ucmra_unit_least.
      apply list_singletonM_included. eexists. rewrite map_lookup HEl /=.
      split; first done. apply Some_included. right. apply Cinl_included.
      apply prod_included. split=>/=; first done. apply ucmra_unit_least.
    }
    iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    simpl.
    iDestruct "HRR" as "(H1 & H2 & HRR)".
    iDestruct "HRR" as (ℓ) "[H↦' HRR]".
    iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
    (* a.d. destruct if value was already taken. should not happen. *)
    destruct resolution as [[]|].
    + iDestruct "HRR" as "(Hℓ & HRR)"; wp_cmpxchg_fail.
      iDestruct ("HRRsRestore" with "[H1 H2 HRR Hℓ]") as "HRRs";
        first by (eauto 10 with iFrame).
      iMod ("HTqClose" with "[-HΦ HHRestore]") as "_";
        first by iExists _, _; iFrame.
      by iModIntro; iMod "HHRestore"; iModIntro; wp_pures.
    + iDestruct "HRR" as "(Hℓ & HRR)"; wp_cmpxchg_fail.
      iDestruct ("HRRsRestore" with "[H1 H2 HRR Hℓ]") as "HRRs";
        first by (eauto 10 with iFrame).
      iMod ("HTqClose" with "[-HΦ HHRestore]") as "_";
        first by iExists _, _; iFrame.
      by iModIntro; iMod "HHRestore"; iModIntro; wp_pures.
  - (* Cell already inhabited? Impossible. *)
    iDestruct (big_sepL_lookup with "HRRs") as "HRR"; first done.
    iDestruct "HRR" as "[>HEnq' _]".
    iDestruct (iterator_issued_exclusive with "HEnq HEnq'") as %[].
  - iMod (acquire_cell _ _ _ _ _ _ with "H↦")
      as "[[#>HCellInit|[>Hℓ HCancHandle]] HCloseCell]";
      first by solve_ndisj.
    { (* We know the rendezvous is not yet initialized. *)
      iAssert (∃ s, rendezvous_state γtq i (Some s))%I with "[]"
        as (?) "HContra".
      { iDestruct "HCellInit" as "[H|H]".
        iDestruct "H" as (? ?) "H"; iExists _; iFrame "H".
        iExists _; iFrame "H". }
      iDestruct (rendezvous_state_included with "H● HContra")
        as %(c & HEl' & HInc).
      simplify_eq. simpl in HInc. by apply included_None in HInc.
    }
    wp_cmpxchg_suc.
    iMod (inhabit_cell_ra with "H●") as "(H● & #HLoc)"; first done.
    iMod ("HCloseCell" with "[]") as "_"; last iModIntro.
    { iLeft. iNext. iLeft. iExists _, _. iApply "HLoc". }
    iSpecialize ("HΦ" $! true with "[HLoc]").
      rewrite /rendezvous_thread_handle. 
      iSplit; first done. 
      iSplit; first done. 
      iSplit; first done. 
      
      iApply "HLoc".
    iMod ("HTqClose" with "[-HΦ HHRestore]").
    2: by iModIntro; iMod "HHRestore"; iModIntro; wp_pures.
    iExists _, _. iFrame "H●". rewrite insert_length. iFrame "HLen".
    iDestruct (big_sepL_insert_acc with "HRRs") as "[HPre HRRsRestore]";
      first done.
    iApply "HRRsRestore". simpl. iFrame "HEnq HLoc HF".
    iSplit; first done.
    iExists _. iFrame "H↦ Hℓ HCancHandle". iDestruct "HPre" as "[$ $]".
    by iLeft.
Qed.


Lemma pass_value_to_empty_cell_spec
      γtq γa γe γd i ptr e d :
  {{{ is_thread_queue γa γtq γe γd e d ∗
      deq_front_at_least γtq (S i) ∗
      cell_location γtq γa i ptr ∗
      iterator_issued γd i
      }}}
    CAS #ptr (InjLV #()) EIORESUMEDV
  {{{ (r: bool), RET #r;
      if r
      then E
      else inhabited_rendezvous_state γtq i ε ∗ iterator_issued γd i
  }}}.
Proof.
  iIntros (Φ) "(#HTq & #HDeqFront & #H↦ & HIsRes) HΦ".
  wp_bind (CmpXchg _ _ _).
  iDestruct "HTq" as "(HInv & HInfArr & _ & _)".
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen)" "HTqClose".
  iDestruct "HLen" as %HLen.
  iDestruct (deq_front_at_least_valid with "H● HDeqFront") as %HDeqFront.
  assert (i < length l) as HLt; first lia.
  apply lookup_lt_is_Some in HLt. destruct HLt as [c HEl].
  iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRsRestore]"; first done.
  destruct c as [[r|γk k r]|].
  - (* The cell could not have been already filled. *)
    iDestruct "HRR" as "[HIsRes' _]".
    iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as ">[]".
  - (* CAS fails, as the suspender already arrived. *)
    iAssert (▷ ∃ v, ⌜v ≠ InjLV #()⌝
                    ∗ ptr ↦ v
                    ∗ (ptr ↦ v -∗ cell_resources γtq γa γe γd i
                           (Some (cellInhabited γk k r))
                           (bool_decide (i < deqFront))))%I
            with "[HRR]" as (inh) "(>% & Hℓ & HRRRestore)".
    {
      simpl. iDestruct "HRR" as "($ & [>% $] & HRR)".
      iDestruct "HRR" as (ptr') "[H↦' HRR]".
      iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
      destruct r as [[|]|].
      + (* cell resumed with v' *)
        iDestruct "HRR" as "[Hℓ $]".
        iExists _; iFrame "Hℓ". iSplitR.
        iPureIntro. done.
        iNext. iIntros "Hℓ". 
        iSplit; first done. iExists _; by iFrame.
      + (* cell cancelled *)
        iDestruct "HRR" as "[Hℓ $]".
        iExists _; iFrame "Hℓ". iSplitR.
        iPureIntro. done.
        iNext. iIntros "Hℓ". 
        iSplit; first done. iExists _; by iFrame.
      + (* cell inhabited by k. *)
        iDestruct "HRR" as "[Hℓ $]".
        iExists _; iFrame "Hℓ". iSplitR.
        iPureIntro. case. intros ->. contradiction.
        iNext. iIntros "Hℓ". 
        iSplit; first done. iExists _; by iFrame.
    }
    wp_cmpxchg_fail.
    iDestruct ("HRRRestore" with "Hℓ") as "HRR".
    iDestruct ("HRRsRestore" with "HRR") as "HRRs".
    iMod (own_update with "H●") as "[H● H◯]".
    2: iSpecialize ("HΦ" $! false with "[H◯ HIsRes]");
      first by iFrame; iExists _, _.
    {
      apply auth_update_core_id. by apply _.
      apply prod_included=>/=. split; first by apply ucmra_unit_least.
      apply prod_included=>/=. split; last by apply ucmra_unit_least.
      apply list_singletonM_included. eexists.
      rewrite map_lookup HEl=>/=. split; first done.
      rewrite Some_included. right. apply Cinr_included.
      apply prod_included=>/=. split; last by apply ucmra_unit_least.
      done.
    }
    iMod ("HTqClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
    rewrite list_insert_id; last done.
    iExists _, _. iFrame. iPureIntro; lia.
  - iMod (acquire_cell _ _ _ _ _ _ with "H↦")
      as "[[#>HCellInit|[>Hℓ HCancHandle]] HCloseCell]";
      first by solve_ndisj.
    { (* We know the rendezvous is not yet initialized. *)
      iAssert (∃ s, rendezvous_state γtq i (Some s))%I with "[]"
        as (?) "HContra".
      { iDestruct "HCellInit" as "[H|H]".
        iDestruct "H" as (? ?) "H"; iExists _; iFrame "H".
        iExists _; iFrame "H". }
      iDestruct (rendezvous_state_included with "H● HContra")
        as %(c & HEl' & HInc).
      simplify_eq. simpl in HInc. by apply included_None in HInc.
    }
    wp_cmpxchg_suc.
    iDestruct "HRR" as "[HE HR]". rewrite bool_decide_true; last lia.
    iMod (fill_cell_ra with "H●") as "(H● & #HInitialized)"; first done.
    iMod ("HCloseCell" with "[]") as "_"; last iModIntro.
    { iLeft. iRight. done. }
    iSpecialize ("HΦ" $! true).
    iSpecialize ("HΦ" with "HE").
    (* a.d. FIXME this actually seems like a bug, you don't take the value here so the internal state gets messed up. *)
    (* iMod (take_cell_value_ra with "H●") as "[H● #H◯]".
    { erewrite list_lookup_insert=> //. lia. } *)
    (* rewrite list_insert_insert. *)
    iMod ("HTqClose" with "[-HΦ]"); last by iModIntro; wp_pures.
    iExists _, _. iFrame "H●". rewrite insert_length.
    iSplitL.
    2: iPureIntro; by lia.
    iApply "HRRsRestore". simpl. iFrame. 
    iExists _. iFrame "H↦".
    iNext.
    by iFrame.
Qed.

Lemma deq_front_at_least_from_auth_ra γtq l deqFront:
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra l deqFront) ∗
  deq_front_at_least γtq deqFront.
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ $]"; last done.
  apply auth_update_core_id. by apply _.
  apply prod_included=> /=. split; last by apply ucmra_unit_least.
  apply prod_included=> /=. split; first by apply ucmra_unit_least.
  apply prod_included=> /=. split; first by apply ucmra_unit_least.
  done.
Qed.

Lemma read_cell_value_by_resumer_spec γtq γa γe γd i ptr e d:
  {{{ deq_front_at_least γtq (S i) ∗
      is_thread_queue γa γtq γe γd e d ∗
      cell_location γtq γa i ptr ∗
      iterator_issued γd i }}}
    !#ptr
  {{{ (v: val), RET v;
      (⌜v = NONEV⌝ ∧ iterator_issued γd i ∨
       ⌜v = CANCELLEDV⌝ ∧ R ∨
       ∃ γk k, ⌜v = InjLV k⌝ ∧ rendezvous_thread_handle γtq γk k i)
  }}}.
Proof.
  iIntros (Φ) "(#HDeqFront & #(HInv & HInfArr & _ & HD) & #H↦ & HIsRes) HΦ".
  iMod (access_iterator_resources with "HD [#]") as "HH"; first done.
  { iApply (own_mono with "HIsRes"). apply auth_included; split=>//=.
    apply prod_included; split; first by apply ucmra_unit_least.
    apply max_nat_included. simpl. done. }
  iDestruct "HH" as "[HH HHRestore]".
  iMod (acquire_cell _ _ _ _ _ _ with "H↦")
    as "[[#>HCellInit|[>Hℓ HCancHandle]] HCloseCell]"; first by solve_ndisj.
  2: { (* Cell was not yet inhabited, so NONEV is written in it. *)
    wp_load. iMod ("HCloseCell" with "[Hℓ HCancHandle]") as "_".
    by iRight; iFrame. iModIntro. iMod ("HHRestore" with "HH").
    iApply "HΦ". by iLeft; iFrame.
  }
  iSpecialize ("HCloseCell" with "[HCellInit]"); first by iLeft.
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen)" "HTqClose".
  iDestruct (awakening_permit_implies_bound with "H● HH") as "#>HValid".
  iDestruct "HValid" as %HValid.
  iSpecialize ("HHRestore" with "[HH]"); first done.
  iDestruct "HCellInit" as "[HCellInhabited|HCellFilled]".
  2: { (* Cell could not have been filled already, we hold the permit. *)
    iDestruct (rendezvous_state_included' with "H● HCellFilled")
      as %(c & HEl & HInc).
    destruct c as [c'|].
    2: { exfalso. simpl in *. move: HInc. rewrite csum_included.
        case; first done. case; by intros (? & ? & ? & ? & ?). }
    iDestruct (big_sepL_lookup with "HRRs") as "HRR"; first done.
    iDestruct "HRR" as "[>HContra _]".
    iDestruct (iterator_issued_exclusive with "HContra HIsRes") as %[].
  }
  (* Cell was inhabited. *)
  iDestruct "HCellInhabited" as (? ?) "HCellInhabited".
  iDestruct (rendezvous_state_included' with "H● HCellInhabited")
    as %(c & HEl & HInc).
  destruct c as [c'|? ? c'].
  1: { exfalso. simpl in *. move: HInc. rewrite csum_included.
        case; first done. case; by intros (? & ? & ? & ? & ?). }
  move: HInc; rewrite Cinr_included pair_included to_agree_included.
  case. case=> /= HEq1 HEq2 _. simplify_eq.
  iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
    first done.
  iDestruct (deq_front_at_least_valid with "H● HDeqFront") as %HDeqFront.
  rewrite bool_decide_true; last lia.
  iDestruct "HRR" as "(HIsSus & #HTh & HRR)". iDestruct "HRR" as (ℓ) "[H↦' HRR]".
  iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
  destruct c' as [[|]|].
  - (* Cell could not have been resumed already. *)
    iDestruct "HRR" as "(_ & >HContra & _)".
    iDestruct (iterator_issued_exclusive with "HContra HIsRes") as %[].
  - iDestruct "HRR" as "(Hℓ & HCallback & [HCompletion|[_ HC]])".
    iDestruct "HCompletion" as "[[HCompletionPermit|[_ HC]] HR]".
    all: try by iDestruct (iterator_issued_exclusive with "HIsRes HC") as ">[]".
    wp_load.
    iSpecialize ("HΦ" $! CANCELLEDV with "[HR]").
    { iRight. iLeft. by iFrame. }
    iMod ("HTqClose" with "[-HCloseCell HHRestore HΦ]").
    2: iModIntro; iMod "HCloseCell"; iModIntro; iMod "HHRestore"; iApply "HΦ".
    iExists _, _. iFrame "H● HLen". iApply "HRRsRestore".
    iFrame "HIsSus HTh". iExists _.
    (* a.d. TODO here I need resources for resumer. *)
    by iFrame.
  - iDestruct "HRR" as "(Hℓ & HCancHandle & HE & HR & HCallback &
      [HInvoke|[_ HC]])".
    2: by iDestruct (iterator_issued_exclusive with "HIsRes HC") as ">[]".
    iEval (rewrite -Qp_half_half callback_invokation_permit_Fractional)
      in "HInvoke".
    iDestruct "HInvoke" as "[HInvoke1 HInvoke2]".
    wp_load.
    iSpecialize ("HΦ" $! (InjLV _) with "[HInvoke2]").
    { repeat iRight. iExists _, _. iFrame. iSplit=>//. }
    iMod ("HTqClose" with "[-HCloseCell HHRestore HΦ]").
    2: iModIntro; iMod "HCloseCell"; iModIntro; by iMod "HHRestore".
    iExists _, _. iFrame "H● HLen". iApply "HRRsRestore".
    iFrame "HCancHandle HIsSus HTh". iExists _. iFrame "H↦". iFrame.
    iRight. iFrame.
Qed.

Lemma acquire_resumer_resource_from_immediately_cancelled E' γtq γa γe γd i e d ℓ:
  (↑NTq ∪ ↑NArr) ⊆ E' ->
  is_thread_queue γa γtq γe γd e d -∗
  deq_front_at_least γtq (S i) -∗
  cell_cancelled γa i -∗
  cell_location γtq γa i ℓ -∗
  iterator_issued γd i ={E'}=∗
  ▷ R.
Proof.
  iIntros (HMask) "[#HInv _] #HDeqFront #HCancelled #H↦ HIsRes".
  iInv "HInv" as (l deqFront) "HTq" "HClose".
  iMod (cell_cancelled_means_present with "HCancelled H↦ HTq") as
      "[HTq >HSkippable]"; first by solve_ndisj.
  iDestruct "HSkippable" as %(c & HEl & HCancelled).
  simpl in HCancelled.
  destruct c as [|? ? [[|]|]]=> //.
  iDestruct "HTq" as "(>H● & HRRs & HRest)".
  iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRs]"; first done.
  iDestruct (deq_front_at_least_valid with "H● HDeqFront") as %HDeqFront.
  rewrite bool_decide_true; last lia.
  simpl. iDestruct "HRR" as "(HIsSus & HTh & HRR)".
  iDestruct "HRR" as (ℓ') "(H↦' & Hℓ & HRR)".
  iDestruct "HRR" as "(HCallback & [[[HFuture|[_ >HC]] HR]|[_ >HC]])".
  all: try by iDestruct (iterator_issued_exclusive with "HC HIsRes") as %[].
  iFrame "HR".
  iMod ("HClose" with "[-]"); last done. iExists _, _. iFrame "H● HRest".
  iApply "HRRs". iFrame "HIsSus HTh". iExists _. by iFrame.
Qed.

(* TRANSITIONS ON CELLS IN THE NON-SUSPENDING CASE *****************************)

(* a.d. here the cell breaking token is used to rule out a case. We might have to add it 
   back just for this purpose even though we never break cells. *)
Lemma check_passed_value (suspender_side: bool) γtq γa γe γd i (ptr: loc):
  rendezvous_filled_value γtq #() i -∗
  cell_location γtq γa i ptr -∗
  (if suspender_side then iterator_issued γe i else False (* should be something exclusive *)) -∗
  <<< ∀ l deqFront, ▷ thread_queue_invariant γa γtq γe γd l deqFront >>>
    !#ptr @ ⊤
  <<< ∃ v, thread_queue_invariant γa γtq γe γd l deqFront ∗
           match l !! i with
           | Some (Some (cellPassedValue d)) =>
             match d with
               | None => ⌜v = EIORESUMEDV⌝ ∧
                        (if suspender_side then iterator_issued γe i
                         else False)
               | Some () =>
                 if suspender_side then ⌜v = EIORESUMEDV⌝ ∧ iterator_issued γe i
                 else ⌜v = EIORESUMEDV⌝ ∧ E
             end
           | _ => False
           end, RET v >>>.
Proof.
 iIntros "#HFilled #H↦ HCellBreaking" (Φ) "AU".
  iMod "AU" as (l deqFront) "[(>H● & HRRs & >HLen) [_ HClose]]".
  iDestruct (rendezvous_state_included' with "H● HFilled") as %(c & HEl & HInc).
  rewrite HEl. destruct c as [c'|].
  2: { exfalso. simpl in *. move: HInc. rewrite csum_included.
       case; first done. case; by intros (? & ? & ? & ? & ?). }
  move: HInc. rewrite Cinl_included pair_included to_agree_included. case=> HEq _.
  simplify_eq.
  iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
    first done.
  simpl. iDestruct "HRR" as "(HIsRes & HCancHandle & HRR)".
  iDestruct "HRR" as (ℓ) "[H↦' HRR]".
  iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
  destruct c' as [[]|]=> /=.
  - (* value was taken *)
    iDestruct "HRR" as "(Hptr & HRR)". wp_load.
    iMod ("HClose" with "[-]") as "HΦ"; last by iModIntro.
    * destruct suspender_side.
      + iDestruct "HRR" as "HC".
        iDestruct (iterator_issued_exclusive with "HCellBreaking HC") as %[].
      + iDestruct "HCellBreaking" as %[]. 
  - (* value was not already taken *)
    iDestruct "HRR" as "(Hptr & HRR)". wp_load.
    iMod ("HClose" with "[-]") as "HΦ"; last by iModIntro.
    iFrame "HCellBreaking". iSplitL; last by iPureIntro; eexists.
    iFrame "H● HLen". iApply "HRRsRestore". iFrame. iExists _. iFrame.
    by done.
Qed.

Lemma big_sepL_lookup_alter' {PROP: bi} {A:Type} i f (P: nat → A → PROP) (l: list A) (v: A):
  l !! i = Some v → 
  ([∗ list] i0↦k ∈ l, P i0 k)
    -∗ P i v
      ∗ (P i (f v) -∗ [∗ list] i0↦k ∈ alter f i l, P i0 k).
Proof.
  iIntros (HEl) "HRRs".
  iAssert ([∗ list] i0↦k ∈ l, P (0 + i0) k)%I with "[HRRs]" as "HRRs".
  { iApply big_sepL_mono; last by done.
    iIntros (? ? HEL) "HP". by rewrite Nat.add_0_l. }
  iPoseProof (big_sepL_lookup_alter with "HRRs") as "[HRR HRRsRestore]";
    first by done.
  iSplitL "HRR".
  - by rewrite Nat.add_0_l.
  - rewrite Nat.add_0_l.
    iIntros "HRR". 
    iSpecialize ("HRRsRestore" with "HRR").
    iApply big_sepL_mono; last by done.
    iIntros (? ? HEl') "HP". by rewrite Nat.add_0_l.
Qed. 

(* a.d. TODO it feels kinda weird to use the alter lemma here since they don't use it in other places.
   The question is then how do they update the logical state? 
   DONE they use big_sepL_insert_acc *)
Lemma read_cell_value_by_suspender_spec γtq γa γe γd i (ptr: loc):
  (* this should imply that the value is not yet taken *)
  rendezvous_filled_value γtq #() i -∗
  (* this is used to read from the infinite array *)
  cell_location γtq γa i ptr -∗
  (* used to swap out of the R in the cellState *)
  iterator_issued γe i -∗
  <<< ∀ l deqFront, ▷ thread_queue_invariant γa γtq γe γd l deqFront >>>
    !#ptr @ ⊤
  <<< ∃ l' (v: val), thread_queue_invariant γa γtq γe γd l' deqFront ∗
           ⌜ l' = <[i := Some (cellPassedValue (Some tt))]> l ⌝ ∗
           ⌜ l' !! i = Some (Some (cellPassedValue (Some tt))) ⌝ ∗
           ⌜v = EIORESUMEDV⌝ ∧ R, RET v >>>.
Proof.
  iIntros "#HFilled #H↦ HCellBreaking" (Φ) "AU".
  iMod "AU" as (l deqFront) "[(>H● & HRRs & >HLen) [_ HClose]]".
  iDestruct (rendezvous_state_included' with "H● HFilled") as %(c & HEl & HInc).
  destruct c as [c'|].
  2: { exfalso. simpl in *. move: HInc. rewrite csum_included.
       case; first done. case; by intros (? & ? & ? & ? & ?). }
  move: HInc. rewrite Cinl_included pair_included to_agree_included. case=> HEq _.
  simplify_eq.
  destruct c' as [[]|]=> /=.
  - (* value was taken *)
    iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    simpl. iDestruct "HRR" as "(HIsRes & HCancHandle & HRR)".
    iDestruct "HRR" as (ℓ) "[H↦' HRR]".
    iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
    iDestruct "HRR" as "(Hptr & HRR)".
    wp_load.
    iDestruct (iterator_issued_exclusive with "HCellBreaking HRR") as %[].
  - (* value was not already taken *) 
    iPoseProof ((@big_sepL_lookup_alter' _ _ i 
                  (λ _, Some (cellPassedValue (Some tt)))
                  (λ i v, cell_resources γtq γa γe γd i v (bool_decide (i < deqFront))) l (Some (cellPassedValue None))
                  ) with "HRRs") as "[HRR HRRsRestore]";
    first done.
    simpl. iDestruct "HRR" as "(HIsRes & HCancHandle & HRR)".
    iDestruct "HRR" as (ℓ) "[H↦' HRR]".
    iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
    iDestruct "HRR" as "(Hptr & HRR)". wp_load.
    iMod (take_cell_value_ra with "H●") as "[H● #H◯]"; first by done.
    iMod ("HClose" $! (<[i:=Some (cellPassedValue (Some ()))]> l) with "[-]") as "HΦ"; last by iModIntro.
    iSplitR "HRR".
    2: iSplit; last iSplit.
    + iFrame.
      iSplit.
      * rewrite list_insert_alter.
        iApply "HRRsRestore".
        iFrame. iExists _. iFrame. by done.
      * rewrite insert_length. by iAssumption. 
    + by iPureIntro. 
    + iPureIntro. rewrite list_lookup_insert. done.
      apply lookup_lt_is_Some. eexists. by apply HEl.
    + iSplit; first by iPureIntro.
      by iApply "HRR".
Qed.

Lemma read_cell_value_by_suspender_spec' γtq γa γe γd i (ptr: loc) l deqFront:
  {{{  
  (* this should imply that the value is not yet taken *)
  rendezvous_filled_value γtq #() i ∗
  (* this is used to read from the infinite array *)
  cell_location γtq γa i ptr ∗
  (* used to swap out of the R in the cellState *)
  iterator_issued γe i ∗
  thread_queue_invariant γa γtq γe γd l deqFront }}}
    !#ptr
  {{{ v, RET v; ∃ l', thread_queue_invariant γa γtq γe γd l' deqFront ∗
           ⌜ l' = <[i := Some (cellPassedValue (Some tt))]> l ⌝ ∗
           ⌜ l' !! i = Some (Some (cellPassedValue (Some tt))) ⌝ ∗
           ⌜v = EIORESUMEDV⌝ ∧ R }}}.
Proof.
  iIntros (Φ) "(#HFilled & #H↦ & HCellBreaking & HInv) HΦ". 
  rewrite /thread_queue_invariant.
  iDestruct "HInv" as "(H● & HRRs & HLen)".
  iDestruct (rendezvous_state_included' with "H● HFilled") as %(c & HEl & HInc).
  destruct c as [c'|].
  2: { exfalso. simpl in *. move: HInc. rewrite csum_included.
       case; first done. case; by intros (? & ? & ? & ? & ?). }
  move: HInc. rewrite Cinl_included pair_included to_agree_included. case=> HEq _.
  simplify_eq.
  destruct c' as [[]|]=> /=.
  - (* value was taken *)
    iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    simpl. iDestruct "HRR" as "(HIsRes & HCancHandle & HRR)".
    iDestruct "HRR" as (ℓ) "[H↦' HRR]".
    iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "<-".
    iDestruct "HRR" as "(Hptr & HRR)".
    wp_load.
    iDestruct (iterator_issued_exclusive with "HCellBreaking HRR") as %[].
  - (* value was not already taken *) 
    iPoseProof ((@big_sepL_lookup_alter' _ _ i 
                  (λ _, Some (cellPassedValue (Some tt)))
                  (λ i v, cell_resources γtq γa γe γd i v (bool_decide (i < deqFront))) l (Some (cellPassedValue None))
                  ) with "HRRs") as "[HRR HRRsRestore]";
    first done.
    simpl. iDestruct "HRR" as "(HIsRes & HCancHandle & HRR)".
    iDestruct "HRR" as (ℓ) "[H↦' HRR]".
    iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "<-".
    iDestruct "HRR" as "(Hptr & HRR)".
    iApply fupd_wp.
    iMod (take_cell_value_ra with "H●") as "[H● #H◯]"; first by done.
    iModIntro. wp_load.
    iApply "HΦ".
    iExists _. iFrame. 
    iSplit; last iSplit; last iSplit.
    + iSplit; last by rewrite insert_length.
      rewrite list_insert_alter.
      iApply "HRRsRestore".
      iFrame. iExists _. iFrame. iAssumption.
    + done.
    + rewrite list_lookup_insert. done. 
      apply lookup_lt_is_Some. eexists. by apply HEl.
    + done.
Qed.

(* Lemma take_cell_value_spec γtq γa γe γd i ptr e d v:
  {{{ is_thread_queue γa γtq γe γd e d ∗
      cell_location γtq γa i ptr ∗
      rendezvous_filled_value γtq v i ∗
      iterator_issued γe i }}}
    CAS #ptr (InjRV v) TAKENV
  {{{ (r: bool) v', RET #r; ⌜v = #v'⌝ ∧ if r then V v' ∗ R else CB ∗ E }}}.
Proof.
  iIntros (Φ) "(#HTq & #H↦ & #HFilled & HIsSus) HΦ".
  iDestruct "HTq" as "(HInv & HInfArr & _ & _)". wp_bind (CmpXchg _ _ _).
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)" "HTqClose".
  iDestruct "HLen" as %HLen.
  iDestruct (rendezvous_state_included' with "H● HFilled") as %(c & HEl & HInc).
  destruct c as [? c'|].
  2: { exfalso. simpl in *. move: HInc. rewrite csum_included.
       case; first done. case; by intros (? & ? & ? & ? & ?). }
  move: HInc. rewrite Cinl_included pair_included to_agree_included. case=> HEq _.
  simplify_eq.
  iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRsRestore]";
    first done.
  simpl. iDestruct "HRR" as "(HIsRes & HCancHandle & >% & HRR)".
  iDestruct "HRR" as (ℓ) "[H↦' HRR]".
  iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
  destruct c' as [[|]|]=> /=.
  - (* Rendezvous succeeded even before we arrived. *)
    iSpecialize ("HRRsRestore" $! _); rewrite list_insert_id //.
    iDestruct "HRR" as "[(Hℓ & HCellBreaking & HV & HR)|(_ & HContra & _)]".
    2: by iDestruct (iterator_issued_exclusive with "HIsSus HContra") as ">[]".
    wp_cmpxchg_suc. iSpecialize ("HΦ" $! true with "[HV HR]"). by iFrame.
    iMod ("HTqClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
    iExists _, _. iFrame "H● HDeqIdx". iSplitL; last by iPureIntro.
    iApply "HRRsRestore". iFrame "HIsRes HCancHandle". iSplitR; first done.
    iExists _. iFrame "H↦". iRight. iFrame.
  - (* Cell was broken before we arrived. *)
    iSpecialize ("HRRsRestore" $! _); rewrite list_insert_id //.
    iDestruct "HRR" as "(Hℓ & [[HE HCB]|HContra])".
    2: by iDestruct (iterator_issued_exclusive with "HIsSus HContra") as ">[]".
    wp_cmpxchg_fail. iSpecialize ("HΦ" $! false with "[HE HCB]"). by iFrame.
    iMod ("HTqClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
    iExists _, _. iFrame "H● HDeqIdx". iSplitL; last by iPureIntro.
    iApply "HRRsRestore". iFrame "HIsRes HCancHandle". iSplitR; first done.
    iExists _. iFrame "H↦". iFrame.
  - (* Cell is still intact, so we may take the value from it. *)
    iDestruct "HRR" as "(Hℓ & HE & HV & HR)".
    wp_cmpxchg_suc. iSpecialize ("HΦ" $! true with "[HV HR]"). by iFrame.
    iMod (take_cell_value_ra with "H●") as "[H● #H◯]"; first done.
    iMod ("HTqClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
    iDestruct "HDeqIdx" as %HDeqIdx.
    iExists _, _. iFrame "H●". rewrite insert_length. iSplitL.
    2: {
      iPureIntro; split; first lia.
      case. intros ? (r & HEl' & HSkippable). apply HDeqIdx. split; first done.
      destruct (decide (i = deqFront - 1)).
      - subst. rewrite list_insert_alter list_lookup_alter HEl in HEl'.
        simpl in *. simplify_eq. contradiction.
      - rewrite list_lookup_insert_ne in HEl'; last lia.
      eexists. done.
    }
    iApply "HRRsRestore". simpl. iFrame "HIsRes HCancHandle".
    iSplitR; first done. iExists _. iFrame "H↦". iRight. iFrame.
Qed. *)

(* DEALING WITH THE SUSPENDED FUTURE *******************************************)

(* MARKING STATES **************************************************************)

Lemma mark_cell_as_resumed γa γtq γe γd e d i ptr v:
  {{{ is_thread_queue γa γtq γe γd e d ∗
      inhabited_rendezvous_state γtq i (Some (Cinl (to_agree #v))) ∗
      cell_location γtq γa i ptr }}}
    #ptr <- EIORESUMEDV
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "([#HInv _] & #HResumed & #H↦) HΦ".
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen)".
  rewrite /inhabited_rendezvous_state.
  iDestruct "HResumed" as (? ?) "HResumed".
  iDestruct (rendezvous_state_included' with "H● HResumed")
            as %(c & HEl & HInc).
  destruct c as [?|γf f r].
  { exfalso. simpl in *. move: HInc. rewrite csum_included.
    case; first done. case; by intros (? & ? & ? & ? & ?). }
  simpl in *. move: HInc. rewrite Cinr_included pair_included. case.
  rewrite to_agree_included. case=> /= ? ? HInc'. simplify_eq.
  destruct r as [r'|]; last by apply included_None in HInc'. simpl in *.
  destruct r' as [|]; simpl in *.
  - iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    simpl. iDestruct "HRR" as "(HIsSus & HTh' & HRR)".
    iDestruct "HRR" as (?) "(H↦' & Hℓ & HRR)".
    iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
    iAssert (▷ ptr ↦ -)%I with "[Hℓ]" as (?) "Hℓ".
    { by iExists _. }
    wp_store.
    iDestruct ("HΦ" with "[$]") as "$". iModIntro. iExists _, _.
    iFrame. iApply "HRRsRestore". iFrame. iExists _. iFrame "H↦ Hℓ".
  - exfalso. move: HInc'. rewrite Some_included; case.
    by move=> HInc; inversion HInc.
    rewrite csum_included. case; first done. case; by intros (? & ? & ? & ? & ?).
Qed.

(* Lemma markCancelled_immediate_spec γa γtq γe γd e d i ptr:
  is_thread_queue γa γtq γe γd e d -∗
  inhabited_rendezvous_state γtq i (Some (Cinr (Cinl (to_agree ())))) -∗
  cell_location γtq γa i ptr -∗
  <<< True >>>
    getAndSet #ptr CANCELLEDV @ ⊤ ∖ ↑NTq
  <<< ∃ v, True, RET v >>>.
Proof.
  iIntros "[#HInv _] #HState #H↦" (Φ) "AU".
  awp_apply getAndSet_spec.
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)".
  iDestruct "HState" as (γf' f') "HState".
  iDestruct (rendezvous_state_included' with "H● HState") as %(c & HEl & HInc).
  assert (c = cellInhabited γf' f' (Some cellImmediatelyCancelled)) as ->.
  {
    destruct c as [|? ? r]=>//=.
    { exfalso. simpl in *. move: HInc. rewrite csum_included.
      case; first done. case; by intros (? & ? & ? & ? & ?). }
    simpl in *. move: HInc. rewrite Cinr_included pair_included. case.
    rewrite to_agree_included. case=> /= ? ? HInc'. simplify_eq.
    destruct r as [r'|]; last by apply included_None in HInc'. simpl in *.
    move: HInc'.
    destruct r' as [v'| |r'']; simpl in *.
    - rewrite Some_included. case. by intros HContra; inversion HContra.
      rewrite csum_included. case; first done.
      case; by intros (? & ? & ? & ? & ?).
    - done.
    - rewrite Some_included. rewrite Cinr_included. case.
      + intros HContra. inversion HContra. simplify_eq.
        inversion H5.
      + rewrite csum_included. case; first done.
        case; by intros (? & ? & ? & ? & ?).
  }
  iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRs]"; first done.
  simpl. iDestruct "HRR" as "(HIsSus & #[HFuture HLocs] & HRR)".
  iDestruct (future_is_loc with "HFuture") as ">HLoc".
  iDestruct "HLoc" as %[fℓ ->]. iDestruct "HRR" as (ℓ) "(H↦' & Hℓ & HRest)".
  iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
  iDestruct "Hℓ" as "[Hℓ|Hℓ]".
  1: iAssert (▷ ptr ↦ InjLV #fℓ ∧ ⌜val_is_unboxed (InjLV #fℓ)⌝)%I
    with "[Hℓ]" as "HAacc"; first by iFrame.
  2: iAssert (▷ ptr ↦ CANCELLEDV ∧ ⌜val_is_unboxed CANCELLEDV⌝)%I
    with "[Hℓ]" as "HAacc"; first by iFrame.
  all: iApply (aacc_aupd_commit with "AU"); first done; iIntros "_".
  all: iAaccIntro with "HAacc".
  - iIntros "[Hℓ _] !>". iSplitR; first done.
    iIntros "$ !>". iExists _, _. iFrame. iApply "HRRs".
    iFrame "HIsSus HFuture HLocs". iExists _. by iFrame.
  - iIntros "Hℓ !>". iExists _. iSplitR; first done. iIntros "$ !>".
    iExists _, _. iFrame. iApply "HRRs". iFrame "HIsSus HFuture HLocs".
    iExists _. by iFrame.
  - iIntros "[Hℓ _] !>". iSplitR; first done.
    iIntros "$ !>". iExists _, _. iFrame. iApply "HRRs".
    iFrame "HIsSus HFuture HLocs". iExists _. by iFrame.
  - iIntros "Hℓ !>". iExists _. iSplitR; first done. iIntros "$ !>".
    iExists _, _. iFrame. iApply "HRRs". iFrame "HIsSus HFuture HLocs".
    iExists _. by iFrame.
Qed. *)

(* Lemma markCancelled_spec γa γtq γe γd e d i ptr γf f:
  is_thread_queue γa γtq γe γd e d -∗
  inhabited_rendezvous_state γtq i (Some (Cinr (Cinr (0, Some (Cinr ε))))) -∗
  cell_location γtq γa i ptr -∗ cell_cancelling_token γtq i -∗
  rendezvous_thread_handle γtq γf f i -∗
  <<< True >>>
    getAndSet #ptr CANCELLEDV @ ⊤ ∖ ↑NTq
  <<< ∃ v, ⌜v = InjLV f⌝ ∧ ▷ E ∨
      (∃ v' : base_lit,
      ⌜v = InjRV #v'⌝
      ∧ inhabited_rendezvous_state γtq i
          (Some (Cinr (Cinr (0, Some (Cinr (Some (Cinl (to_agree #v'))))))))
      ∗ awakening_permit γtq
      ∗ ▷ V v'), RET v >>>.
Proof.
  iIntros "[#HInv _] #HState #H↦ HToken #HTh" (Φ) "AU".
  iDestruct "HToken" as (? ?) "HToken".
  awp_apply getAndSet_spec.
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)".
  iDestruct "HState" as (γf' f') "HState".
  iDestruct (rendezvous_state_included' with "H● HState") as %(c & HEl & HInc).
  assert (∃ d, c = cellInhabited γf' f' (Some (cellCancelled (Some (cancellationAllowed d))))) as [d' ->].
  {
    destruct c as [|? ? r]=>//=.
    { exfalso. simpl in *. move: HInc. rewrite csum_included.
      case; first done. case; by intros (? & ? & ? & ? & ?). }
    simpl in *. move: HInc. rewrite Cinr_included pair_included. case.
    rewrite to_agree_included. case=> /= ? ? HInc'. simplify_eq.
    destruct r as [r'|]; last by apply included_None in HInc'. simpl in *.
    move: HInc'.
    destruct r' as [v'| |r'']; simpl in *.
    - rewrite Some_included. case. by intros HContra; inversion HContra.
      rewrite csum_included. case; first done.
      case; by intros (? & ? & ? & ? & ?).
    - rewrite Some_included. rewrite Cinr_included. case.
      + intros HContra. inversion HContra. simplify_eq.
        inversion H5.
      + rewrite csum_included. case; first done.
        case; by intros (? & ? & ? & ? & ?).
    - destruct r'' as [r'''|].
      2: { simpl. rewrite Some_included. case.
        { move=> HCinr. apply Cinr_inj in HCinr. apply Cinr_inj in HCinr.
          move: HCinr. case. simpl. done. }
        rewrite Cinr_included Cinr_included prod_included /= nat_included.
        case=> _ HContra. by apply included_None in HContra. }
      destruct r'''.
      2: {
        simpl. rewrite Some_included. case.
        { move=> HCinr. apply Cinr_inj in HCinr. apply Cinr_inj in HCinr.
          move: HCinr. case. simpl. done. }
        rewrite Cinr_included Cinr_included prod_included /= nat_included.
        rewrite Some_included. case=> _. case.
        intros HContra; by inversion HContra.
        rewrite csum_included.
        case; first done. case; by intros (? & ? & ? & ? & ?).
      }
      simpl. by eexists.
  }
  iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRs]"; first done.
  simpl. iDestruct "HRR" as "(HIsSus & #HTh' & HRR)".
  iDestruct "HTh" as "[HFutureLoc HTh]".
  iDestruct (rendezvous_state_included' with "H● HTh")
    as %(c' & HEl' & HInc').
  simplify_eq. simpl in *. move: HInc'. rewrite Cinr_included pair_included.
  rewrite to_agree_included. case. case=> /= HH1 HH2 _. simplify_eq.
  iDestruct "HRR" as (ℓ) "(H↦' & HFutureCancelled & HNotImmediate & HRR)".
  iAssert (own γtq (cell_list_contents_auth_ra l deqFront) -∗
           cell_cancelling_token γtq i -∗
           cell_cancelling_token γtq i -∗ False)%I with "[]" as "HNotFinished".
  {
    iIntros "H● HToken HToken'".
    iDestruct "HToken" as (? ?) "HToken". iDestruct "HToken'" as (? ?) "HToken'".
    iCombine "HToken" "HToken'" as "HToken". rewrite list_singletonM_op.
    iDestruct (rendezvous_state_included' with "H● HToken")
      as %(c''' & HEl'' & HInc'').
    exfalso. simplify_eq. simpl in *.
    move: HInc''. rewrite -Cinr_op Cinr_included pair_included. case=> _/=.
    rewrite Some_included. case.
    - move=> HContra. do 2 apply Cinr_inj in HContra. case HContra.
      simpl. by case.
    - do 2 rewrite Cinr_included. rewrite pair_included. case=> /=.
      rewrite nat_included nat_op_plus. lia.
  }
  iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
  destruct d' as [[|]|].
  2: { (* Only we could have finished the cancellation. *)
    iDestruct "HRR" as "(_ & >HToken' & _)".
    iDestruct ("HNotFinished" with "H● HToken' [HToken]") as %[].
    by iExists _, _.
  }
  - (* a value was passed to the cell. *)
    iDestruct "HRR" as "([(Hℓ & >HUnboxed & HV & >HAwak)|(_ & >HToken')] &
                        HIsRes & HFuture)".
    2: { iDestruct ("HNotFinished" with "H● HToken' [HToken]") as %[].
         by iExists _, _. }
    iDestruct "HUnboxed" as %HUnboxed.
    iAssert (▷ ptr ↦ InjRV #v ∧ ⌜val_is_unboxed (InjRV #v)⌝)%I
            with "[Hℓ]" as "HAacc"; first by iFrame.
    iApply (aacc_aupd_commit with "AU"); first done. iIntros "_".
    iAaccIntro with "HAacc".
    { iIntros "[Hℓ _] !>". iSplitR; first done. iFrame "HToken". iIntros "$ !>".
      iExists _, _. iSpecialize ("HRRs" $! _). rewrite list_insert_id; last done.
      iFrame "H● HLen HDeqIdx". iApply "HRRs". iFrame "HIsSus HTh'".
      iExists _. iFrame "H↦". iFrame "HFutureCancelled HNotImmediate".
      iFrame "HIsRes HFuture". iLeft. by iFrame. }
    iIntros "Hℓ". iExists _. iMod (own_update with "H●") as "[H● H◯]".
    2: iSplitL "H◯ HV HAwak".
    2: { iModIntro. iRight; iExists _. iFrame "HV HAwak". iSplitR; first done.
      iExists _, _. iFrame. }
    {
      apply auth_update_core_id. apply _. apply prod_included. simpl.
      split; first by apply ucmra_unit_least. apply prod_included. simpl.
      split; last by apply ucmra_unit_least. apply list_singletonM_included.
      eexists. rewrite map_lookup HEl=> /=. split; first done.
      apply Some_included. right. apply Cinr_included. apply prod_included'.
      split=> /=; first done. apply Some_included. right.
      do 2 apply Cinr_included. apply prod_included=> /=. split; last done.
      apply nat_included. lia.
    }
    iIntros "!> $ !>".
    iSpecialize ("HRRs" $! _). rewrite list_insert_id; last done.
    iModIntro.
    iExists _, _. iFrame. iApply "HRRs". iFrame. iFrame "HTh'". iExists _.
    iFrame "H↦". iRight. iFrame "Hℓ". by iExists _, _.
  - (* we may cancel the cell without obstructions. *)
    iDestruct (future_is_loc with "HFutureLoc") as %[fℓ ->].
    iDestruct "HRR" as "(Hℓ & HE & HRR)".
    iAssert (▷ ptr ↦ InjLV #fℓ ∧ ⌜val_is_unboxed (InjLV #fℓ)⌝)%I
      with "[Hℓ]" as "HAacc"; first by iFrame.
    iApply (aacc_aupd_commit with "AU"); first done. iIntros "_".
    iAaccIntro with "HAacc".
    { iIntros "[Hℓ _] !>". iFrame "HToken". iIntros "$ !>". iExists _, _.
      iSpecialize ("HRRs" $! _). rewrite list_insert_id; last done.
      iFrame "H● HLen HDeqIdx". iApply "HRRs". iFrame "HIsSus HTh'".
      iExists _. iFrame "H↦". iFrame "HFutureCancelled HNotImmediate".
      iFrame "Hℓ HE HRR". }
    iIntros "Hℓ".
    iMod (finish_cancellation_ra with "H●") as "[H● #H◯]"; first done.
    iModIntro. iExists _. iSplitL "HE"; first by iLeft; iFrame.
    iIntros "$ !>".
    iExists _, _. iFrame "H●". rewrite insert_length.
    iDestruct "HLen" as %HLen; iDestruct "HDeqIdx" as %HDeqIdx.
    iSplitL.
    2: {
      iPureIntro. split; first lia.
      case. intros ? (r & HEl' & HSkippable). apply HDeqIdx. split; first done.
      destruct (decide (i = deqFront - 1)) as [->|HNeq].
      - rewrite list_lookup_insert in HEl'; last lia. simplify_eq.
        eexists. by split.
      - rewrite list_lookup_insert_ne in HEl'; last lia.
        eexists. done.
    }
    iApply "HRRs". iFrame "HIsSus HTh'". iExists _.
    iFrame "H↦ HFutureCancelled HNotImmediate Hℓ". iSplitL "HToken".
    by iExists _, _.
    rewrite /resources_for_resumer.
    iDestruct "HRR" as "[[H1 H2]|[H1 H2]]"; [iLeft|iRight]; iFrame.
Qed. *)

(* Lemma pass_value_to_cancelled_cell_spec γa γtq γe γd e d i ptr γf f v:
  {{{ is_thread_queue γa γtq γe γd e d ∗
      inhabited_rendezvous_state γtq i (Some (Cinr (Cinr ε))) ∗
      cell_location γtq γa i ptr ∗ iterator_issued γd i ∗
      deq_front_at_least γtq (S i) ∗
      rendezvous_thread_handle γtq γf f i ∗ V v ∗ ⌜lit_is_unboxed v⌝ }}}
    CAS #ptr (InjLV f) (InjRV #v)
  {{{ (r: bool), RET #r;
      if r then E else iterator_issued γd i ∗ V v
  }}}.
Proof.
  iIntros (Φ) "([#HInv _] & #HState & #H↦ & HIsRes & #HDeqFront & #HTh & HV) HΦ".
  iDestruct "HV" as "[HV HVUnboxed]". wp_bind (CmpXchg _ _ _).
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)" "HClose".
  iDestruct "HState" as (γf' f') "HState".
  iDestruct (rendezvous_state_included' with "H● HState") as %(c & HEl & HInc).
  assert (∃ d, c = cellInhabited γf' f' (Some (cellCancelled d))) as [d' ->].
  {
    destruct c as [|? ? r]=>//=.
    { exfalso. simpl in *. move: HInc. rewrite csum_included.
      case; first done. case; by intros (? & ? & ? & ? & ?). }
    simpl in *. move: HInc. rewrite Cinr_included pair_included. case.
    rewrite to_agree_included. case=> /= ? ? HInc'. simplify_eq.
    destruct r as [r'|]; last by apply included_None in HInc'. simpl in *.
    move: HInc'.
    destruct r' as [v'| |r'']; simpl in *.
    - rewrite Some_included. case. by intros HContra; inversion HContra.
      rewrite csum_included. case; first done.
      case; by intros (? & ? & ? & ? & ?).
    - rewrite Some_included. rewrite Cinr_included. case.
      + intros HContra. inversion HContra. simplify_eq.
        inversion H5.
      + rewrite csum_included. case; first done.
        case; by intros (? & ? & ? & ? & ?).
    - by eexists.
  }
  iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRs]"; first done.
  iDestruct (deq_front_at_least_valid with "H● HDeqFront") as %HDF.
  rewrite bool_decide_true; last lia.
  simpl. iDestruct "HRR" as "(HIsSus & #HTh' & HRR)".
  iDestruct "HTh" as "[HFutureLoc HTh]".
  iDestruct (rendezvous_state_included' with "H● HTh")
    as %(c' & HEl' & HInc').
  simplify_eq. simpl in *. move: HInc'. rewrite Cinr_included pair_included.
  rewrite to_agree_included. case. case=> /= HH1 HH2 _. simplify_eq.
  iDestruct "HRR" as (ℓ) "(H↦' & HFutureCancelled & HNotImmediate & HRR)".
  iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
  iDestruct (future_is_loc with "HFutureLoc") as %[fℓ ->].
  destruct d' as [[[[|]|]|]|].
  - (* We could not have already taken the value, we hold the permit. *)
    iDestruct "HRR" as "(_ & >HC & _)".
    iDestruct (iterator_issued_exclusive with "HC HIsRes") as %[].
  - (* Maybe the cell is already closed. *)
    iDestruct "HRR" as "(Hℓ & HCancTok & [[[HFuture|[_ >HC]] HAwak]|[_ >HC]])".
    all: try by iDestruct (iterator_issued_exclusive with "HC HIsRes") as %[].
    wp_cmpxchg_fail.
    iSpecialize ("HΦ" $! false with "[HIsRes HV]"); first by iFrame.
    iMod ("HClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
    iExists _, _. iFrame "H● HLen HDeqIdx". iSpecialize ("HRRs" $! _).
    rewrite list_insert_id; last done. iApply "HRRs".
    iFrame "HIsSus HTh'". iExists _. iFrame "H↦ HFutureCancelled HNotImmediate".
    iFrame "Hℓ HCancTok". iLeft. iFrame.
  - (* Cancellation was permitted but undecided until we arrived. *)
    iDestruct "HRR" as "(Hℓ & HE & [[[HFuture|[_ >HC]] HAwak]|[_ >HC]])".
    all: try by iDestruct (iterator_issued_exclusive with "HC HIsRes") as %[].
    iMod (put_value_in_cancelled_cell_ra with "H●") as "[H● H◯]"; first done.
    wp_cmpxchg_suc. iSpecialize ("HΦ" $! true with "HE").
    iMod ("HClose" with "[-HΦ]"); last by iModIntro; wp_pures.
    iExists _, _. iFrame "H●". rewrite insert_length.
    iDestruct "HLen" as %HLen; iDestruct "HDeqIdx" as %HDeqIdx.
    iSplitL.
    2: {
      iPureIntro. split; first lia.
      case. intros ? (r & HEl' & HSkippable). apply HDeqIdx. split; first done.
      destruct (decide (i = deqFront - 1)) as [->|HNeq].
      - rewrite list_lookup_insert in HEl'; last lia. simplify_eq.
        eexists. by split.
      - rewrite list_lookup_insert_ne in HEl'; last lia.
        eexists. done.
    }
    iApply "HRRs". iFrame "HIsSus HTh'". iExists _.
    iFrame "H↦ HFutureCancelled HNotImmediate HIsRes HFuture". iLeft.
    iFrame.
  - (* The cancellation was prevented. *)
    iDestruct "HRR" as "(_ & HCancHandle & [(Hℓ & HE & [HFuture|[_ >HC]])|
      [(Hℓ & [[[HFuture|[_ >HC]] HERefuse]|[_ >HC]] & HCancToken)|HRR]])";
      last iDestruct "HRR" as (?) "(_ & _ & >HC & _)".
    all: try by iDestruct (iterator_issued_exclusive with "HC HIsRes") as %[].
    + (* The cell is still not marked as refused. *)
      wp_cmpxchg_suc. iSpecialize ("HΦ" $! true with "HE").
      iMod ("HClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
      iExists _, _. iFrame "H● HLen HDeqIdx". iSpecialize ("HRRs" $! _).
      rewrite list_insert_id; last done. iApply "HRRs".
      iFrame "HIsSus HTh'". iExists _.
      iFrame "H↦ HFutureCancelled HNotImmediate HCancHandle".
      iRight. iRight. iExists _. by iFrame.
    + (* The cell is already marked as refused. *)
      wp_cmpxchg_fail.
      iSpecialize ("HΦ" $! false with "[HIsRes HV]"); first by iFrame.
      iMod ("HClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
      iExists _, _. iFrame "H● HLen HDeqIdx". iSpecialize ("HRRs" $! _).
      rewrite list_insert_id; last done. iApply "HRRs".
      iFrame "HIsSus HTh'". iExists _.
      iFrame "H↦ HFutureCancelled HNotImmediate HCancHandle".
      iRight. iLeft. iFrame. by iLeft.
  - (* The cancellation was not even registered yet. *)
    iDestruct "HRR" as "(HCancHandle & HR &
      [(Hℓ & HE & [HFuture|[_ >HC]])|[_ HRR]])";
      last iDestruct "HRR" as (?) "(_ & _ & >HC & _)".
    all: try by iDestruct (iterator_issued_exclusive with "HC HIsRes") as %[].
    wp_cmpxchg_suc. iSpecialize ("HΦ" $! true with "HE").
    iMod ("HClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
    iExists _, _. iFrame "H● HLen HDeqIdx". iSpecialize ("HRRs" $! _).
      rewrite list_insert_id; last done. iApply "HRRs".
    iFrame "HIsSus HTh'". iExists _. iFrame "H↦ HFutureCancelled HNotImmediate".
    iFrame "HCancHandle HR". iRight. iFrame. iExists _. by iFrame.
Qed. *)

(* WHOLE OPERATIONS ON THE THREAD QUEUE ****************************************)

Check 1.

(* Lemma tryResume_spec (mayBreakCells shouldAdjust waitForResolution: bool)
      (returnRefusedValue: val) (maxWait: nat) γa γtq γe γd e d v:
  NTq ## NFuture ->
  lit_is_unboxed v ->
  shouldAdjust = negb immediateCancellation ->
  {{{ ERefuse ∗ V v }}}
    returnRefusedValue #v
  {{{ RET #(); ▷ E }}} -∗
  {{{ is_thread_queue γa γtq γe γd e d ∗ awakening_permit γtq ∗
      V v ∗ if mayBreakCells then CB else True }}}
    tryResume array_interface #maxWait #shouldAdjust #mayBreakCells #waitForResolution
      d returnRefusedValue #v
  {{{ (n: nat), RET #n; ⌜n = 0⌝ ∧ E ∗ (if mayBreakCells then CB else True) ∨ 
                      ⌜n = 1⌝ ∧ V v ∗ (if mayBreakCells then CB else True) ∗
                        (if immediateCancellation then R
                         else awakening_permit γtq) ∨
                      ⌜n = 2 ∧ mayBreakCells⌝ ∧ R ∗ V v
  }}}.
Proof.
  iIntros (HMask HUnboxed ->) "#HRefusedValue".
  iIntros "!>" (Φ) "(#HTq & HAwak & HV & HCB) HΦ".
  wp_lam. wp_pures. wp_bind (iteratorStepOrIncreaseCounter _ _ _).
  iApply (iteratorStepOrIncreaseCounter_spec _ _ NArr NDeq with "[HAwak]").
  by solve_ndisj.
  { iDestruct "HTq" as "(HInv & $ & HEnq & $)". iFrame.
    destruct immediateCancellation eqn:X; first done.
    iApply (dequeue_iterator_update with "[$]"). iPureIntro=> HContra.
    by rewrite X in HContra. }
  iIntros "!>" (?) "[[-> HCancelled]|HSuccess]".
  { rewrite -wp_fupd. destruct immediateCancellation eqn:X=>/=.
    - iDestruct "HCancelled" as (i) "(HCancelled & H↦ & HIsRes)".
      iDestruct "H↦" as (ℓ) "H↦".
      iMod (deq_front_at_least_from_iterator_issued with "[$] HIsRes")
        as "[#HDeqFront HIsRes]"; first done.
      iMod (acquire_resumer_resource_from_immediately_cancelled
              with "[$] HDeqFront HCancelled H↦ HIsRes") as "HR";
        first by solve_ndisj.
      by rewrite X.
      wp_pures. iApply ("HΦ" $! 1). iRight; iLeft. by iFrame.
    - wp_pures. iApply ("HΦ" $! 1). iRight. iLeft. by iFrame.
  }
  iDestruct "HSuccess" as (ns s ->) "[HIsRes #H↦~]".
  iMod (deq_front_at_least_from_iterator_issued with "[$] HIsRes")
    as "[#HDeqFront HIsRes]"; first done.
  wp_pures.
  wp_bind (cellPointerCleanPrev _ _). iApply (cellPointerCleanPrev_spec).
  { iDestruct "HTq" as "(_ & $ & _)". iFrame "H↦~". }
  iIntros "_". iNext. wp_pures. iLöb as "IH".
  wp_bind (derefCellPointer _ _). iApply derefCellPointer_spec.
  { iDestruct "HTq" as "(_ & $ & _)". iFrame "H↦~". }
  iIntros "!>" (ℓ) "#H↦". wp_pures. wp_bind (!_)%E.
  iApply (read_cell_value_by_resumer_spec with "[$]").
  iIntros "!>" (?) "[[-> HIsSus]|[[-> HCancelled]|[[-> HRefused]|HInhabited]]]".
  - (* The cell is empty yet. *)
    wp_pures. wp_bind (Snd _).
    iApply (pass_value_to_empty_cell_spec mayBreakCells with "[$]")=> //.
    iIntros "!>" (passingResult) "HPassingResult".
    destruct passingResult; wp_pures.
    2: { iDestruct "HPassingResult" as "(_ & HIsRes & HV)".
         iApply ("IH" with "HV HCB HΦ HIsRes"). }
    destruct mayBreakCells.
    2: { wp_pures. iApply ("HΦ" $! 0). iLeft. by iFrame. }
    iDestruct "HPassingResult" as "[HCellBreakingToken #HFilled]".
    wp_pures. iClear "IH".
    (* waiting for a suspender to arrive. *)
    iInduction maxWait as [|maxWait'] "IHWait".
    + wp_pures.
      (* the suspender did not manage to arrive while we were waiting. *)
      wp_bind (Snd _). iApply (break_cell_spec with "[$]").
      iIntros "!>" (breakResult) "HBreakResult".
      destruct breakResult; wp_pures.
      * (* breaking succeeded. *)
        iApply ("HΦ" $! 2). iRight; iRight.
        by iDestruct "HBreakResult" as "[$ $]".
      * (* breaking failed as the suspender arrived. *)
        iApply ("HΦ" $! 0). iLeft. by iFrame.
    + wp_pures. wp_bind (!#ℓ)%E.
      awp_apply (check_passed_value false with "HFilled H↦ HCellBreakingToken")
                without "HCB HΦ".
      iDestruct "HTq" as "[HInv _]". iInv "HInv" as (l deqFront) "HOpen".
      iAaccIntro with "HOpen".
      { iIntros "HTq !>". iSplitL; last done. by iExists _, _. }
      iIntros (?) "[HTq HReadValue]". iSplitL "HTq"; first by iExists _, _.
      iIntros "!> [HCB HΦ]".
      destruct (l !! ns) as [[[? res|]|]|]; try iDestruct "HReadValue" as %[].
      destruct res as [[|]|].
      * (* rendezvous succeeded, we may safely leave. *)
        iDestruct "HReadValue" as "[-> HE]". wp_pures.
        iApply ("HΦ" $! 0). iLeft. by iFrame.
      * (* someone else broke the cell? impossible. *)
        by iDestruct "HReadValue" as "[[_ %] _]".
      * (* nothing happened in this cell yet after it was filled. *)
        iDestruct "HReadValue" as "[-> HCellBreakingToken]". wp_pures.
        replace (S maxWait' - 1)%Z with (Z.of_nat maxWait'); last lia.
        iApply ("IHWait" with "HCB HΦ HCellBreakingToken").
  - wp_pures. iApply ("HΦ" $! 1). iRight; iLeft. by iFrame.
  - wp_pures. wp_bind (returnRefusedValue _).
    iApply ("HRefusedValue" with "[$]"). iIntros "!> HE". wp_pures.
    iApply ("HΦ" $! 0). iLeft. by iFrame.
  - iDestruct "HInhabited" as (γf f ->) "[#HTh HFutureCompl]".
    iDestruct (future_is_loc with "[]") as "HLoc". by iDestruct "HTh" as "[$ _]".
    iDestruct "HLoc" as %[fℓ ->]. wp_pures.
    wp_bind (tryCompleteFuture _ _).
    awp_apply (try_resume_cell with "HDeqFront HTq HTh [HV]")
              without "HCB HΦ"=>//.
    iAaccIntro with "HFutureCompl"; first by iIntros "$ !>".
    iIntros (completionResult) "HCompletion !> [HCB HΦ]".
    wp_pures.
    destruct completionResult.
    { (* completion succeeded. *)
      iDestruct "HCompletion" as "(HE & _ & HState)". wp_pures.
      wp_bind (_ <- _)%E. iApply (mark_cell_as_resumed with "[$]").
      iIntros "!> _". wp_pures. iApply ("HΦ" $! 0). iLeft. by iFrame.
    }
    destruct immediateCancellation eqn:X.
    { (* cancellation is immediate. *)
      iDestruct "HCompletion" as "[HV HR]". wp_pures.
      iApply ("HΦ" $! 1). iRight. iLeft. by iFrame.
    }
    iDestruct "HCompletion" as "(HV & #HState & HIsRes)".
    destruct waitForResolution.
    { by wp_pures; iApply ("IH" with "HV HCB HΦ HIsRes"). }
    wp_pures. wp_bind (Snd _).
    iApply (pass_value_to_cancelled_cell_spec with "[HIsRes HV]").
    { iFrame "HTq HState H↦ HIsRes HDeqFront HV HTh". by iPureIntro. }
    iIntros "!>" (valuePassingResult) "HValuePassing".
    destruct valuePassingResult.
    { (* the value was successfully passed. *)
      wp_pures. iApply ("HΦ" $! 0). iLeft. by iFrame.
    }
    iDestruct "HValuePassing" as "[HIsRes HV]".
    wp_pures. iApply ("IH" with "HV HCB HΦ HIsRes").
Qed.

Lemma resume_spec (mayBreakCells shouldAdjust waitForResolution: bool)
      (returnRefusedValue: val) (maxWait: nat) γa γtq γe γd e d v:
  NTq ## NFuture ->
  lit_is_unboxed v ->
  shouldAdjust = negb immediateCancellation ->
  {{{ ERefuse ∗ V v }}}
    returnRefusedValue #v
  {{{ RET #(); ▷ E }}} -∗
  {{{ is_thread_queue γa γtq γe γd e d ∗ awakening_permit γtq ∗
      V v ∗ if mayBreakCells then CB else True }}}
    resume array_interface #maxWait #shouldAdjust #mayBreakCells #waitForResolution
      d returnRefusedValue #v
  {{{ (r: bool), RET #r; if r then E ∗ if mayBreakCells then CB else True
                      else ⌜immediateCancellation ∨ mayBreakCells⌝ ∧
                           R ∗ V v }}}.
Proof.
  iIntros (HMask HLitUnboxed HAdjust) "#HRefusedValue".
  iIntros "!>" (Φ) "[#HTq H] HΦ". wp_lam. wp_pures. iLöb as "IH".
  wp_bind (tryResume _ _ _ _ _ _ _ _).
  iApply (tryResume_spec with "HRefusedValue [H]")=> //. by iFrame.
  iIntros "!>" (n) "Hn". wp_pures.
  iDestruct "Hn" as "[[-> HE]|[[-> H]|[[-> #HMayBreak] H]]]"; wp_pures.
  by iApply "HΦ".
  - rewrite HAdjust. destruct immediateCancellation; wp_pures.
    + iApply "HΦ". iDestruct "H" as "($ & _ & $)". by iLeft.
    + iApply ("IH" with "[H] HΦ"). iDestruct "H" as "($ & $ & $)".
  - iApply "HΦ". iDestruct "HMayBreak" as %HMayBreak. iFrame. by iRight.
Qed. *)

Definition is_thread_queue_suspend_result γtq γa γk (v: val): iProp :=
  ∃ k i s, ⌜v = s⌝ ∧ rendezvous_thread_handle γtq γk k i
            ∗ is_infinite_array_cell_pointer _ _ array_spec NArr γa s i.

Global Instance is_thread_queue_suspend_result_persistent:
  Persistent (is_thread_queue_suspend_result γtq γa γf v).
Proof. apply _. Qed.

(* Definition thread_queue_future_cancellation_permit γf :=
  future_cancellation_permit γf (1/2)%Qp. *)

Theorem suspend_spec γa γtq γe γd e d k:
  (* the invariant about the state of CQS. *) 
  {{{ is_thread_queue γa γtq γe γd e d ∗ 
  (* a generic permit to call suspend *)
      suspension_permit γtq ∗ 
  (* the WP of the closure k so that we can create a callback. *)
      is_waker V' k ∗
  (* extra knowledge we need to know about the callback. 
     Since the callback is a closure and not a pointer this is technically wrong. 
     Therefore, when creating the callback we should allocate a new reference and use that as the callback.
     We never need to mutate it so we can save the invariant compared to original CQS.
     *)
      ⌜ k ≠ #() ⌝ ∗
      ⌜ k ≠ #1 ⌝ ∗
      ⌜ val_is_unboxed (InjLV k) ⌝ }}}
    suspend array_interface e k
  {{{ v, RET v; ⌜v = NONEV⌝ ∨
                ∃ γk v', ⌜v = SOMEV v'⌝ ∗
                         callback_cancellation_permit γk 1%Qp ∧
                         is_thread_queue_suspend_result γtq γa γk v' 
                         (* a.d. TODO we need to have an analogue of the cancellation permit. *)
                         (* thread_queue_future_cancellation_permit γf *) }}}.
Proof.
  iIntros (Φ) "(#HTq & HIsSus & Hk & Hunit & HOne & Hunboxed) HΦ".
  iApply fupd_wp.
  iMod (newCallback_spec with "Hunit HOne Hunboxed Hk") as (γk) "(HCallback & HInvoke & HCancel)".
  iModIntro.
  wp_lam. wp_pures.
  wp_bind (iteratorStep _ _). iApply (iteratorStep_spec with "[HIsSus]").
  2: { by iDestruct "HTq" as "(_ & $ & $ & _)". }
  by solve_ndisj.
  iIntros "!>" (n ns s) "HEnqResult". destruct (decide (ns = n)) as [->|HContra].
  2: { (* someone else cancelled our cell, but it's impossible. *)
    iDestruct "HEnqResult" as "(% & HIsSus & _ & #HCancelled)".
    iDestruct ("HCancelled" $! n with "[%]") as "[HNCancelled H↦]"; first lia.
    iDestruct "H↦" as (ℓ) "H↦". iDestruct "HTq" as "[HInv _]". rewrite -fupd_wp.
    iInv "HInv" as (? ?) "HOpen" "HClose".
    iMod (cell_cancelled_means_present with "HNCancelled H↦ HOpen") as "[HOpen >HPure]".
    by solve_ndisj.
    iDestruct "HPure" as %(c & HEl & HState).
    assert (∃ γf' f' d, l !! n = Some (Some (cellInhabited γf' f' d)))
      as (? & ? & ? & HEl'); simplify_eq.
    { simpl in *. destruct c. by destruct HState.
      by eauto. }
    iDestruct "HOpen" as "(_ & HRRs & _)".
    iDestruct (big_sepL_lookup with "HRRs") as "HRR"; first done.
    simpl. iDestruct "HRR" as "[>HC _]".
    by iDestruct (iterator_issued_exclusive with "HIsSus HC") as %[].
  }
  wp_pures. iDestruct "HEnqResult" as "(_ & HIsSus & #H↦~ & _)".
  wp_bind (derefCellPointer _ _). iApply (derefCellPointer_spec with "[]").
  { iDestruct "HTq" as "(_ & $ & _)". done. }
  iIntros "!>" (ℓ) "#H↦". wp_pures. wp_bind (Snd _).
  iApply (inhabit_cell_spec with "[$]").
  iIntros "!>" (inhabitResult) "HResult".
  destruct inhabitResult.
  { (* the cell was successfully inhabited. *)
    wp_pures. iApply "HΦ". iRight. iExists _, _. iSplitR; first done.
    iFrame.
    rewrite /rendezvous_thread_handle /is_thread_queue_suspend_result /rendezvous_thread_handle.
    iExists _, _, _.
    iSplit; first done.
    iFrame. by iAssumption.
  }
  (* the cell is already filled. 
     we know it can only be due to a value, so we call the callback ourselves *)
  wp_pures. wp_bind (!_)%E.
  iDestruct "HResult" as "(#HFilled & HIsSus & HCallback & HInvoke)".
  (* iDestruct "HTq" as "(HInv & HArray & HSuspendIter & HResumeIter)". *)
  iAssert (▷ callback_invariant V' γk k CallbackWaiting)%I with "HCallback" as "HCallback".
  iApply (read_cell_value_by_suspender_spec' _ _ _ _ _ _ l with "[HFilled H↦ HIsSus]").
  { iFrame. repeat iSplit. 
    iApply "HFilled". iApply "H↦". }
  awp_apply (read_cell_value_by_suspender_spec with "HFilled H↦ HIsSus")
    without "HΦ".
  iDestruct "HTq" as "(HInv & HRest)". iInv "HInv" as (l deqFront) "HOpen".
  iAaccIntro with "HOpen". iIntros "HOpen !>"; iSplitR "HCallback HInvoke HCancel"; first iExists _, _. 
    by done. 
    by iFrame.
  iIntros (? ?) "(HTq & -> & HEl & -> & HRR)". 
  iSplitL "HTq"; first by iExists _, _.
  iIntros "!> HΦ".
  (* rendezvous succeeded, we may safely leave. *)
  wp_pures.
  wp_bind (k #()).
  (* change the logical state of the callback. *)
  iApply fupd_wp.
  iMod (invokeCallback_spec with "HInvoke HCallback [HRR]") as "(Hk & HCallback & HCallbackInvoked)".
  { rewrite /V'. by iFrame. }
  iModIntro.
  iApply (wp_strong_mono with "Hk"); [by done|by done|].
  iIntros (? ->).
  iModIntro.
  wp_pures.
  iApply "HΦ".
  by iLeft. 
Qed.

Lemma read_cell_value_by_canceller_spec γtq γa γe γd γk i ptr e d k:
  {{{ is_thread_queue γa γtq γe γd e d ∗
      cell_location γtq γa i ptr ∗
      rendezvous_thread_locs_state γtq γk k i ∗
      callback_cancellation_permit γk 1%Qp }}}
    !#ptr
  {{{ (v: val), RET v;
      ⌜v = EIORESUMEDV⌝ ∨ 
      ⌜v = InjLV k⌝ ∗ callback_cancellation_permit γk 1%Qp
  }}}.
Proof.
Admitted.

(* Lemma take_cell_value_by_canceller_spec γtq γa *)

Theorem try_cancel_spec γa γtq γe γd e d γk r:
  (* the invariant about the state of CQS. *)
  {{{ is_thread_queue γa γtq γe γd e d ∗ 
  (* exclusive permit to cancel the callback. *)
      callback_cancellation_permit γk 1%Qp ∗
  (* knowledge that a callback is in the queue (TODO maybe unnecessary) *)
      is_thread_queue_suspend_result γtq γa γk r }}}
    try_cancel array_interface r
  {{{ (b: bool), RET #b; if b then 
                  (* is_waker gives us the WP for executing k *)
                  ∃ k, is_waker V' k ∗ 
                  (* we have a persistent piece of information that the callback is cancelled. *)
                        callback_is_cancelled γk ∗ 
                  (* is_callback allows us to conclude k = k' for k' which the function that called suspend/cancel still has. *)
                        is_callback γk k 
                  (* if cancellation fails we don't know anything (on the metalevel we know that another thread will eventually call k, but we don't have this linearity in the Iris proof yet). *)
                  else True }}}.
Proof.
  iIntros (Φ) "(#HTq & HCancel & HRes) HΦ".
  iDestruct "HRes" as (k i s) "(-> & (HUnit & HOne & Hunboxed & #HLoc) & #HArray)".
  iDestruct "HUnit" as %HUnit.
  iDestruct "HOne" as %HOne.
  iDestruct "Hunboxed" as %Hunboxed.
  wp_lam.
  wp_bind (derefCellPointer _ _). iApply (derefCellPointer_spec with "[]").
  { iDestruct "HTq" as "(_ & $ & _)". done. }
  iIntros "!>" (ℓ) "#H↦". wp_pures. 
  wp_bind (!_)%E. iApply (read_cell_value_by_canceller_spec with "[HCancel]").
  { iFrame. iSplit; last iSplit; by iAssumption. }
  iNext.
  iIntros (v) "[->|[-> HCancel]]".
  - (* already resumed so we just return false. *)
    wp_pures.
    by iApply "HΦ".
  - (* at the moment there is an uncancelled callback. We try to CAS it and then call it. *)
    wp_pures. 
    rewrite bool_decide_false; last by injection.
    wp_pures. 
    rewrite bool_decide_false; last by injection.
    wp_pures.
    iDestruct "HTq" as "(HInv & HInfArr & HRest)". wp_bind (CmpXchg _ _ _).
    iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen)" "HTqClose".
    iDestruct "HLen" as %HLen.
    iAssert (⌜∃ c : option cellTerminalState,
                  l !! i = Some (Some (cellInhabited γk k c))⌝)%I as %(c & HEl).
    { iApply (cell_list_contents_ra_locs with "H● HLoc"). }
    iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    destruct c as [[|]|].
    + (* now the callback is already resumed. *)
      iDestruct "HRR" as "(>HIsSus & >#HLoc' & HRR)".
      iDestruct "HRR" as (ℓ') "(#H↦' & Hℓ & HRR)".
      iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
      wp_cmpxchg_fail. 
      iDestruct ("HRRsRestore" $! (Some (cellInhabited γk k (Some cellResumed))) with "[HIsSus HLoc' H↦' HRR Hℓ]") as "HRRs".
      { iFrame. iSplit; first done. iExists ℓ. by iFrame. }
      iMod ("HTqClose" with "[-HΦ]") as "_".
      { iExists _, _. iFrame. iNext.
        rewrite list_insert_id; last by done.
        iSplit; last by done.
        done. }
      iModIntro. wp_pures.
      by iApply "HΦ".
    + (* callback is cancelled should lead to contradiction. *)
      iDestruct "HRR" as "(>HIsSus & >#HLoc' & HRR)".
      iDestruct "HRR" as (ℓ') "(_ & _ & >HCallback & _)".
      iApply fupd_wp.
      iMod (callback_is_cancelled_from_auth_ra with "[HCallback]") as "[HCallback HCallbackCancelled]".
      { by iDestruct "HCallback" as "[H _]". }
      by iDestruct (callback_cancellation_permit_implies_not_cancelled with "HCancel HCallbackCancelled") as %[].
    + (* callback is still not resumed *)
      iDestruct "HRR" as "(>HIsSus & >#HLoc' & HRR)".
      iDestruct "HRR" as (ℓ') "(#H↦' & Hℓ & HCancHandle & HRR)".
      iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
      simpl.
      wp_cmpxchg_suc.
      iDestruct "HRR" as "(HE & HR & HCallback & HRR)".
      (* update the callback invariant *)
      iDestruct "HCallback" as "(HCallbackState & HCallbackRest)".
      iMod (is_callback_from_auth_ra with "HCallbackState") as "[HCallbackState HIsCallback]".
      iAssert (callback_invariant V' γk k CallbackWaiting) with "[$]" as "HCallback".
      iMod (cancelCallback_spec with "HCancel HCallback") as "(Hk & HCallback & HCallbackCancelled)".
      iDestruct ("HRRsRestore" $! (Some (cellInhabited γk k (Some cellImmediatelyCancelled))) with "[HIsSus HLoc' H↦' HRR Hℓ HCallback HR]") as "HRRs".
      { iFrame. iSplit; first done. iExists ℓ. iFrame.
        iSplit; first by done. iLeft. iFrame. }
      iMod (immediately_cancel_cell_ra with "H●") as "[H● Hrendezvous]"; first by done.
      iMod ("HTqClose" with "[-HΦ HCancHandle HIsCallback Hk HCallbackCancelled]") as "_".
      { iExists _, _. iFrame. iNext.
        rewrite insert_length.
        done. }
      iModIntro.
      wp_pures.
      wp_bind (cancelCell _ _).
      iAssert (▷ cancellation_handle γa i)%I with "HCancHandle" as "HCancHandle".
      iAssert (▷ is_waker V' k)%I with "Hk" as "Hk".
      iAssert (▷ callback_is_cancelled γk)%I with "HCallbackCancelled" as "HCallbackCancelled".
      awp_apply (cancelCell_spec with "[] HArray") without "HΦ".
      by iAssumption.
      iAaccIntro with "HCancHandle". iIntros "$". by iFrame. iIntros "#HCancelled !> HΦ".
      wp_pures.
      iApply "HΦ".
      iExists _.
      iFrame.
Qed.

(* Theorem try_cancel_spec γa γtq γe γd e d γk r:
  is_thread_queue γa γtq γe γd e d -∗
  is_thread_queue_suspend_result γtq γa γk r -∗
  <<< (* ▷ thread_queue_future_cancellation_permit γf *) True >>>
    try_cancel r @ ⊤ ∖ ↑NTq
  <<< ∃ (r: bool),
      if r then 
        ∃ i k, 
        is_infinite_array_cell_pointer _ _ array_spec NArr γa e i
        ∗ rendezvous_thread_handle γtq γk k i ∗
        inhabited_rendezvous_state γtq i (Some (Cinr (Cinl (to_agree ()))))
             ∗ ▷ cancellation_handle γa i
      else
        True,
        (* thread_queue_future_cancellation_permit γf, *)
      RET #r >>>.
Proof.
  iIntros (HMask) "#HTq #HFuture". iIntros (Φ) "AU". wp_lam.
  iDestruct "HFuture" as (f') "[HFuture|HFuture]".
  - iDestruct "HFuture" as "(HFuture & -> & HFInv & HCompl)".
    iDestruct "HCompl" as (v) "#HCompl". wp_pures.
    awp_apply (tryCancelFuture_spec with "HFuture").
    iInv "HFInv" as ">HCancPermit".
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros ">HPermit". rewrite /thread_queue_future_cancellation_permit.
    iCombine "HCancPermit" "HPermit" as "HPermit".
    rewrite -future_cancellation_permit_Fractional Qp_half_half.
    iAaccIntro with "HPermit".
    {
      iIntros "HPermit".
      iEval (rewrite -Qp_half_half future_cancellation_permit_Fractional)
        in "HPermit".
      iDestruct "HPermit" as "[$ $]". by iIntros "!> $".
    }
    iIntros (r) "Hr". destruct r.
    by iDestruct (future_is_completed_not_cancelled with "HCompl Hr") as %[].
    iDestruct "Hr" as "[_ HCancPermit]".
    iEval (rewrite -Qp_half_half future_cancellation_permit_Fractional)
      in "HCancPermit".
    iExists false. iDestruct "HCancPermit" as "[$ $]".
    iSplitL; last by iIntros "!> $". by iExists _.
  - iDestruct "HFuture" as (i' s ->) "[HTh HLoc]". wp_pures.
    awp_apply (try_cancel_cell with "HTq HTh"); first done.
    iApply (aacc_aupd_commit with "AU"); first done. iIntros ">HPermit".
    iAaccIntro with "HPermit". by iIntros "$ !> $".
    iIntros (r) "Hr !>". iExists r. iSplitL; last by iIntros "$ !>".
    destruct r.
    + iDestruct "Hr" as "[$ Hr]". iExists _, _, _. iFrame "HLoc".
      iSplitR; first done. by iFrame.
    + iDestruct "Hr" as "[Hr $]". iDestruct "Hr" as (?) "[_ Hr]".
      by iExists _.
Qed. *)

End proof.

Typeclasses Opaque inhabited_rendezvous_state
 filled_rendezvous_state
 cell_breaking_token cancellation_registration_token
 cell_cancelling_token thread_queue_state deq_front_at_least
 rendezvous_thread_locs_state rendezvous_filled_value
 rendezvous_thread_handle rendezvous_initialized suspension_permit
 awakening_permit resources_for_resumer cell_resources cell_enqueued
 thread_queue_invariant is_thread_queue_suspend_result.
