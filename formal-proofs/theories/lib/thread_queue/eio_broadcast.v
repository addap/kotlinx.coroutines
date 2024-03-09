From SegmentQueue.util Require Import
  everything local_updates big_opL cmra count_matching find_index.

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
  let: "callback" := newCallback "k" in
  let: "cellPtr" := Snd (iteratorStep array_interface "enqIterator") in
  let: "cell" := derefCellPointer array_interface "cellPtr" in
  if: CAS "cell" EMPTYV (InjL "callback")
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
             | InjL "callback" => 
               if: CAS "cell" (InjL "callback") EIORESUMEDV
               then 
                let: "k" := !"callback" in
                "k" #() ;;
                #true
               else #false
             end) #()
  end.

(* 
  Resume_all, superficially not similar to Eio but does the same thing. 
  Eio, does a CAS (Fst deqIterator) deqCtr endCtr and then finds all the valid cell indices between deqCtr and enqCtr.
  We instead repeatedly call a normal resume function, which will increment deqIterator the same amount of times.
*)
Definition resume_all: val :=
  λ: "enqIterator" "deqIterator",
  (* we read the current value of enqIterator and deqIterator, take the difference and then call the normal resume function as many times.
    This way we emulate resume_all from eio.  *)
  let: "enqCtr" := ! (Fst "enqIterator") in
  let: "deqCtr" := ! (Fst "deqIterator") in
  let: "n" := "enqCtr" - "deqCtr" in
  (rec: "loop" "n" :=
    if: "n" = #0 then #()
    else resume "deqIterator";; "loop" ("n" - #1)) "n".

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
         | InjL "callback" => 
           if: CAS "cell" (InjL "callback") CANCELLEDV
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
From iris.staging.algebra Require Import list.
From iris.algebra.lib Require Import excl_auth.

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

Notation resume_algreba := (exclR unitO).
                              
Class threadQueueG Σ := ThreadQueueG { 
  thread_queue_inG :> inG Σ algebra;
  resume_inG :> inG Σ resume_algreba
}.
Definition threadQueueΣ : gFunctors := #[GFunctor algebra; GFunctor resume_algreba].
Instance subG_threadQueueΣ {Σ} : subG threadQueueΣ Σ -> threadQueueG Σ.
Proof. solve_inG. Qed.

Context `{heapGS Σ} `{iteratorG Σ} `{threadQueueG Σ} `{callbackG Σ}.
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
  | cellInhabited γk ℓk r => Cinr (to_agree (γk, ℓk),
                                option_map cellTerminalState_ra r)
  end.
    
Definition resume_all_ra : resume_algreba :=
  Excl ().

(* a.d. one fragment of the algebra, it describes the state of one cell. *)
Definition rendezvous_state γtq i (r: option cellStateR) :=
  own γtq (◯ (ε, ({[ i := r ]}, ε))).

Global Instance rendezvous_state_persistent γtq i (r: cellStateR):
  CoreId r -> Persistent (rendezvous_state γtq i (Some r)).
Proof. apply _. Qed.

(* a.d. knowledge that there is a callback k that inhabits cell i. *)
(* a.d. TODO maybe use location directly instead of value. *)
Definition inhabited_rendezvous_state γtq i (r: inhabitedCellStateR): iProp :=
  ∃ γk ℓk, rendezvous_state γtq i (Some (Cinr (to_agree (γk, ℓk), r))).

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

Global Instance thread_queue_state_timeless γ n:
  Timeless (thread_queue_state γ n).
Proof. apply _. Qed.

(* a.d. knowledge that the dequeue front has a certain size. *)
Definition deq_front_at_least γtq (n: nat) :=
  own γtq (◯ (ε, (ε, MaxNat n), ε)).

(* a.d. knowledge that cell i is inhabited by callback k. *)
Definition rendezvous_thread_locs_state (γtq γk: gname) (ℓk: val) (i: nat): iProp :=
  rendezvous_state γtq i (Some (Cinr (to_agree (γk, ℓk), None))).

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
   TODO remove 
   or rename put is_callback in here to make it in 
   line with original thread_handle *)
Definition rendezvous_thread_handle (γtq γk: gname) (k: val) (i: nat): iProp :=
  rendezvous_thread_locs_state γtq γk k i.

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

Definition resume_all_permit γ := own γ (resume_all_ra).

Global Instance awakening_permit_Timeless γ: Timeless (awakening_permit γ).
Proof. by apply _. Qed.

Global Instance suspension_permit_Timeless γ: Timeless (suspension_permit γ).
Proof. by apply _. Qed.

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
           γtq γa γe γd i (c: option cellState) (insideDeqFront: bool):
  iProp :=
  match c with
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
    ∃ (ℓ ℓk: loc), ⌜ k = #ℓk ⌝ ∗ 
      cell_location γtq γa i ℓ ∗
      (* a.d. TODO can we remove that? 
        No I think we need it in one case where we open the invariant and retain the knowledge that the cell is inhabited. *)
      rendezvous_thread_handle γtq γk k i ∗
         match r with
         (* CALLBACK WAITING
            The callback has neither been invoked nor cancelled, so it is just waiting.
            In this case it still owns E and and R if dequeue registration already happened. *)
         | None => ℓ ↦ InjLV k ∗ cancellation_handle γa i ∗
                  E ∗ (if insideDeqFront then R else True) ∗
                  (* this describes the logical state of the callack. A waiting callback contains the WP 
                      asserting that the closure is safe to execute. *)
                  (* a.d. TODO in the future I want to just have the callback_invariant here and store the invokation permit inside. 
                     Then when invoking we just save a callback_is_invoked in cell_resources, similar for cancelling. *)
                  callback_invariant V' γk ℓk CallbackWaiting ∗
                  callback_invokation_permit γk 1%Qp
         (* RESUMED *)
         | Some (cellResumed) =>
           (* a.d. TODO why have the disjunction? I think I should only have EIORESUMEDV *)
           ℓ ↦ EIORESUMEDV ∗
           iterator_issued γd i ∗
           cancellation_handle γa i ∗
           callback_invariant V' γk ℓk (CallbackInvoked #())
         (* CALLBACK SIMPLY CANCELLED *)
         | Some cellImmediatelyCancelled =>
           (* a.d. TODO why have the disjunction? I think I should only have CANCELLEDV *)
           ℓ ↦ CANCELLEDV ∗
           (* future_is_cancelled γf ∗ *)
           callback_invariant V' γk ℓk CallbackCancelled ∗
           (* a.d. TODO resume has to return an R if the cell is already cancelled so we have this disjunction so that it can 
              swap out the R for its iterator_issued γd i. *)
           (iterator_issued γd i ∨ if insideDeqFront then R else True)
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
         ]%prod_included _]%auth_both_valid_discrete.
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
                                                _]%auth_both_valid_discrete.
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
Definition is_thread_queue γa γtq γe γd γres e d :=
(* here we instantiate the cell_is_owned predicate, either it is "inhabited" or "filled". *)
  let co := rendezvous_initialized γtq in
  (inv NTq (∃ l deqFront, ((⌜ deqFront = 0 ⌝ ∨ resume_all_permit γres) ∗ thread_queue_invariant γa γtq γe γd l deqFront)) ∗
   is_infinite_array _ _ array_spec NArr γa co ∗
   is_iterator _ array_spec NArr NEnq co γa (suspension_permit γtq) γe e ∗
   is_iterator _ array_spec NArr NDeq co γa (awakening_permit γtq) γd d)%I.

Theorem newThreadQueue_spec:
  {{{ inv_heap_inv }}}
    newThreadQueue array_interface #()
  {{{ γa γtq γe γd γres e d, RET (e, d); is_thread_queue γa γtq γe γd γres e d
      ∗ thread_queue_state γtq 0 ∗ resume_all_permit γres }}}.
Proof.
  iIntros (Φ) "HHeap HΦ". wp_lam. wp_bind (newInfiniteArray _ _).
  rewrite -fupd_wp.
  iMod (own_alloc (cell_list_contents_auth_ra [] 0
                   ⋅ ◯ (ε, (ε, Excl' 0)))) as (γtq) "[H● H◯]".
  { apply auth_both_valid_discrete. split=> /=.
    - apply pair_included. split; first by apply ucmra_unit_least.
      apply pair_included. split; first by apply ucmra_unit_least.
      done.
    - apply pair_valid. split; first done.
      apply pair_valid. split; last done. apply list_lookup_valid.
      by case. }
  iMod (own_alloc (resume_all_ra)) as (γres) "Hres".
  { done. }
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
        (∃ l deqFront, (⌜ deqFront = 0 ⌝ ∨ resume_all_permit γres) ∗ thread_queue_invariant γa γtq γe γd l deqFront)
       with "[H●]") as "#HInv".
  { iExists [], 0. iFrame. simpl.
    iSplit; first by iLeft.  
    iPureIntro. split; done.
    }
  iSpecialize ("HΦ" $! γa γtq γe γd γres e d).
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
Theorem thread_queue_append' E' γtq γa γe γd γres n e d:
  ↑NTq ⊆ E' ->
  is_thread_queue γa γtq γe γd γres e d -∗
  ▷ E -∗ ▷ thread_queue_state γtq n ={E'}=∗
  thread_queue_state γtq (S n) ∗ suspension_permit γtq.
Proof.
  iIntros (HMask) "[HInv _] HE >HState".
  iInv "HInv" as (l deqFront) "[HResShot HOpen]" "HClose".
  iMod (thread_queue_append with "HE HState HOpen") as "(>$ & _ & >$ & HRest)".
  iMod ("HClose" with "[HResShot HRest]") as "_"; last done. iExists _, _.
  by iFrame.
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
  iDestruct (own_valid_2 with "H● H◯") as %[HValid _]%auth_both_valid_discrete.
  apply prod_included in HValid. destruct HValid as [HValid _].
  apply prod_included in HValid. destruct HValid as [_ HValid].
  apply prod_included in HValid. destruct HValid as [_ HValid].
  apply max_nat_included in HValid. simpl in *.
  iPureIntro; simpl in *; lia.
Qed.

Lemma deq_front_at_least_from_auth_ra γtq l deqFront:
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra l deqFront) ∗
  deq_front_at_least γtq deqFront.
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ $]"; last done.
  apply auth_update_dfrac_alloc. by apply _.
  apply prod_included=> /=. split; last by apply ucmra_unit_least.
  apply prod_included=> /=. split; first by apply ucmra_unit_least.
  apply prod_included=> /=. split; first by apply ucmra_unit_least.
  done.
Qed.


Theorem cell_list_contents__deq_front_at_least i γtq l deqFront:
  (i <= deqFront)%nat ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra l deqFront) ∗
  deq_front_at_least γtq i.
Proof.
  iIntros (HLe) "H●".
  iMod (own_update with "H●") as "[$ $]"; last done.
  apply auth_update_dfrac_alloc.
  by apply _.
  repeat (apply prod_included; split); simpl.
  all: try apply ucmra_unit_least.
  apply max_nat_included. simpl. lia.
Qed.

Lemma None_op_right_id (A: cmra) (a: option A): a ⋅ None = a.
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
DONE: No it says register S i dequeue operations. It just doesn't make any sense to register 0.
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

Lemma deque_all_register_ra_update γ l n res_n:
  (0 < res_n ≤ length l)%nat ->
  own γ (cell_list_contents_auth_ra l 0) -∗
  thread_queue_state γ n ==∗
  own γ (cell_list_contents_auth_ra l res_n)
  ∗ [∗] replicate res_n (awakening_permit γ)
  ∗ thread_queue_state γ (n - res_n)
  ∗ deq_front_at_least γ res_n.
Proof.
  intros [Hgt0 Hleql].
  rewrite awakening_permit_combine; last by lia.
  iIntros "H● H◯".
  iMod (own_update_2 with "H● H◯") as "($ & $ & $ & $)"; last done.
  apply auth_update, prod_local_update=>/=.
  apply prod_local_update_2, prod_local_update=>/=.
  - rewrite ucmra_unit_right_id. by apply nat_local_update.
  - apply max_nat_local_update; simpl; lia.
  - apply prod_local_update_2. rewrite ucmra_unit_right_id=>/=.
    apply local_update_total_valid=> _ _. rewrite Excl_included=> ->.
    etransitivity. by apply delete_option_local_update, _.
    rewrite !drop_length.
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
    + iDestruct "H" as "($ & H)". iDestruct "H" as (? ?) "H".
      iExists _, _. 
      iDestruct "H" as "($ & $ & $ & $ & $ & _)".
      by iFrame.
    + iDestruct "H" as "($ & H)".  iDestruct "H" as (? ?) "H".
      iExists _, _. iNext. iDestruct "H" as "(-> & $ & $ & $ & $ & $ & _ & $ & $)".
      by iFrame.
    + iDestruct "H" as "($ & _)". 
      by done.
  * iApply (big_sepL_mono with "HTail"). iIntros (? ? ?) "H".
    rewrite !bool_decide_false; first done; lia.
Qed.

Lemma advance_deqFront_all res_n l γtq γa γe γd:
  res_n < length l ->
  □ ▷ R -∗
  ▷ ([∗ list] k ↦ y ∈ l, cell_resources γtq γa γe γd k y
                                        (bool_decide (k < 0))) -∗
  ▷ ([∗ list] k ↦ y ∈ l, cell_resources γtq γa γe γd k y
                                        (bool_decide (k < S res_n))).
Proof.
  iInduction res_n as [|res_n] "IH".
  - iIntros (Hlen) "#HR HRRs". 
    iApply (advance_deqFront 0).
    lia. iAssumption. iAssumption.
  - iIntros (Hlen) "#HR HRRs".
    assert (res_n < length l) by lia.
    iSpecialize ("IH" $! H3 with "HR HRRs").
    iPoseProof (advance_deqFront (S res_n) with "HR IH") as "H".
    lia.
    rewrite Nat.add_1_r.
    iAssumption.
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

Lemma thread_queue_register_for_dequeue_all γtq γa γe γd l n res_n:
  res_n ≤ length l →
  □ ▷ R -∗ ▷ thread_queue_invariant γa γtq γe γd l 0 -∗
  ▷ thread_queue_state γtq n ==∗
  ▷ ([∗] replicate res_n (awakening_permit γtq)
  ∗ deq_front_at_least γtq res_n
  ∗ thread_queue_invariant γa γtq γe γd l res_n
  ∗ thread_queue_state γtq (n - res_n)).
Proof.
  destruct res_n as [|res_n].
  - iIntros (Hleq) "#HR (>H● & HRRs & _) >H◯".
    iMod (deq_front_at_least_from_auth_ra with "H●") as "[H● HDeqFront]".
    iModIntro. iNext.
    iFrame.
    iSplit; first done.
    iSplit; first by iPureIntro; lia.
    rewrite Nat.sub_0_r.
    by iAssumption.
  - iIntros (Hleq) "#HR (>H● & HRRs & _) >H◯".
    iMod (deque_all_register_ra_update with "H● H◯")
      as "($ & HAwaks & H◯ & $)".
    { split. lia. lia. }
    iFrame.
    iModIntro.
    iSplit; last by iPureIntro; lia.
    iApply (advance_deqFront_all with "HR HRRs").
    by lia.
Qed.


(* a.d. Dequeue registration If it is known that the size is nonzero, it is possible to decrease the size and provide an R,
obtaining in exchange an awakening permit — a permission to call resume(v). *)
(* Theorem thread_queue_register_for_dequeue' E' γtq γa γe γd γres n e d:
  ↑NTq ⊆ E' ->
  n > 0 ->
  is_thread_queue γa γtq γe γd γres e d -∗
  ▷ R -∗ ▷ thread_queue_state γtq n ={E'}=∗
  thread_queue_state γtq (n - 1) ∗ awakening_permit γtq.
Proof.
  iIntros (HMask Hn) "[HInv _] HR >HState".
  iInv "HInv" as (l deqFront) "(HResShot & HOpen)" "HClose".
  iAssert (▷⌜deqFront < length l⌝)%I with "[-]" as "#>HLen".
  { iDestruct "HOpen" as "(>H● & _)".
    iDestruct (thread_queue_state_valid with "H● HState") as %->.
    rewrite drop_length in Hn.
    iPureIntro. lia. }
  iDestruct "HLen" as %HLen.
  iMod (thread_queue_register_for_dequeue with "HR HOpen HState")
       as "(>HAwak & _ & HOpen & >HState)"=> //.
  iFrame. iMod ("HClose" with "[HResShot HOpen]"); last done.
  iExists _, _. iFrame.
Qed. *)

Global Instance resume_all_permit_Timeless γres: Timeless (resume_all_permit γres).
Proof. by apply _. Qed.

Lemma resume_all_permit_exclusive γres:
  resume_all_permit γres -∗ resume_all_permit γres -∗ False.
Proof.
  (* exclusive_r *)
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as "%".
  iPureIntro.
  apply (exclusive_r _ _ H3).
Qed.

(* new theorem to change thread queue state and dequeue everything. *)
Theorem thread_queue_register_for_dequeue_all' E' γtq γa γe γd γres n res_n e d:
  ↑NTq ⊆ E' →
  res_n ≤ n →
  resume_all_permit γres -∗
  is_thread_queue γa γtq γe γd γres e d -∗
  □ ▷ R -∗ ▷ thread_queue_state γtq n ={E'}=∗
  thread_queue_state γtq (n - res_n) ∗ (▷ [∗] replicate res_n (awakening_permit γtq)).
Proof.
  iIntros (HMask Hn) "HResShot [#HInv _] HR >HState".
  iInv "HInv" as (l deqFront) "(>[->|HResShot'] & HOpen)" "HClose".
  2: { iDestruct (resume_all_permit_exclusive with "HResShot HResShot'") as %[]. }
  (* iAssert (▷⌜deqFront < length l⌝)%I with "[-]" as "#>HLen".
  { iDestruct "HOpen" as "(>H● & _)".
    iDestruct (thread_queue_state_valid with "H● HState") as %->.
    rewrite drop_length in Hn.
    iPureIntro. lia. }
  iDestruct "HLen" as %HLen. *)
  iAssert (▷ ⌜ n = length l ⌝)%I with "[#]" as ">->".
  { iNext.
    iDestruct "HOpen" as "(H● & _)". iApply (thread_queue_state_valid with "H● HState"). }
  iMod (thread_queue_register_for_dequeue_all with "HR HOpen HState")
       as "(HAwaks & _ & HOpen & >HState)"=> //.
  iFrame. iMod ("HClose" with "[HResShot HOpen]") as "_".
  { iExists _, _. iFrame. }
  by iModIntro.
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
             ]%prod_included _]%auth_both_valid_discrete.
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
             _]%prod_included _]%auth_both_valid_discrete.
  simpl in *. iPureIntro; lia.
Qed.

Global Instance is_thread_queue_persistent γa γtq γe γd γres e d:
  Persistent (is_thread_queue γa γtq γe γd γres e d).
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
  iDestruct "HRR" as "(_ & HRR)". iDestruct "HRR" as (ℓ ℓk) "(-> & _ & _ & HRR)".
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

Lemma deq_front_at_least_from_iterator_issued E' γa γtq γe γd γres e d i:
  ↑N ⊆ E' ->
  is_thread_queue γa γtq γe γd γres e d -∗
  iterator_issued γd i ={E'}=∗
  deq_front_at_least γtq (S i) ∗
  iterator_issued γd i.
Proof.
  iIntros (HMask) "(HInv & _ & _ & HD) HIsRes".
  iMod (access_iterator_resources with "HD [#]") as "HH"; first by solve_ndisj.
  by iDestruct (iterator_issued_is_at_least with "HIsRes") as "$".
  rewrite awakening_permit_combine; last lia.
  iDestruct "HH" as "[>HH HHRestore]".
  iInv NTq as (l deqFront) "(HResShot & >H● & HRRs & HRest)" "HClose".
  rewrite -awakening_permit_combine; last lia.
  iDestruct (awakening_permit_implies_bound with "H● HH") as "#%".
  iMod (cell_list_contents__deq_front_at_least with "H●") as "[H● $]"; first lia.
  iFrame "HIsRes".
  iMod ("HClose" with "[-HH HHRestore]") as "_".
  { iExists _, _. iFrame. }
  by iMod ("HHRestore" with "HH").
Qed.

Lemma inhabit_cell_spec γa γtq γe γd γres γk i ptr (ℓk: loc) e d:
  {{{ callback_invariant V' γk ℓk CallbackWaiting ∗
      cell_location γtq γa i ptr ∗
      is_thread_queue γa γtq γe γd γres e d ∗
      callback_invokation_permit γk 1%Qp ∗
      iterator_issued γe i }}}
    CAS #ptr (InjLV #()) (InjLV #ℓk)
  {{{ (r: bool), RET #r;
      if r
      then rendezvous_thread_handle γtq γk #ℓk i
      else filled_rendezvous_state γtq i ε
           ∗ iterator_issued γe i
           ∗ callback_invariant V' γk ℓk CallbackWaiting
           ∗ callback_invokation_permit γk 1%Qp }}}.
Proof.
  iIntros (Φ) "(HF & #H↦ & #(HInv & HInfArr & HE & _) & HInvoke & HEnq)
               HΦ".
  wp_bind (CmpXchg _ _ _).
  iMod (access_iterator_resources with "HE [#]") as "HH"; first done.
  by iApply (iterator_issued_is_at_least with "HEnq").
  iDestruct "HH" as "[HH HHRestore]".
  iInv "HInv" as (l' deqFront) "(HResShot & >H● & HRRs & >HLen)" "HTqClose".
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
    { (* with auth_update_dfrac_alloc we can extract a persistent fraction out of the auth
         (namely that the cell is filled). We just need to prove that it holds using the HEl assumption. *)
      apply auth_update_dfrac_alloc. by apply _.
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
    by iAssumption.
    iMod ("HTqClose" with "[-HΦ HHRestore]").
    2: by iModIntro; iMod "HHRestore"; iModIntro; wp_pures.
    iExists _, _. iFrame "H●". rewrite insert_length. iFrame "HLen".
    iDestruct (big_sepL_insert_acc with "HRRs") as "[HPre HRRsRestore]";
      first done.
    iFrame.
    iApply "HRRsRestore". simpl. iFrame "HEnq".
    iNext.
    iExists _, _.
    iSplit; first done.
    iSplit; first done.
    iFrame "HLoc Hℓ HCancHandle HF". iDestruct "HPre" as "[$ $]".
    by iAssumption.
Qed.

Lemma pass_value_to_empty_cell_spec
      γtq γa γe γd γres i ptr e d :
  {{{ is_thread_queue γa γtq γe γd γres e d ∗
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
  iIntros (Φ) "(#HTq & #H↦ & HIsRes) HΦ".
  iMod (deq_front_at_least_from_iterator_issued with "[$] HIsRes")
    as "[#HDeqFront HIsRes]"; first done.
  wp_bind (CmpXchg _ _ _).
  iDestruct "HTq" as "(HInv & HInfArr & _ & _)".
  iInv "HInv" as (l deqFront) "(HResShot & >H● & HRRs & >HLen)" "HTqClose".
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
      simpl. iDestruct "HRR" as "($ & HRR)".
      iDestruct "HRR" as (? ?) "(>-> & H↦' & HRR)". 
      iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
      destruct r as [[|]|].
      + (* cell resumed with v' *) 
        iNext.
        iExists _.
        iDestruct "HRR" as "($ & Hℓ & HRest)".
        iFrame "Hℓ". iSplitR.
        done.
        iIntros "Hℓ". 
        iExists _, _. iFrame.
        by iSplit.
      + (* cell cancelled *)
        iNext.
        iDestruct "HRR" as "($ & Hℓ & HRest)".
        iExists _; iFrame "Hℓ". iSplitR.
        done.
        iIntros "Hℓ". 
        iExists _, _. iFrame.
        by iSplit.
      + (* cell inhabited by k. *)
        iNext.
        iDestruct "HRR" as "($ & Hℓ & HRest)".
        iExists _; iFrame "Hℓ". iSplitR.
        done.
        iIntros "Hℓ". 
        iExists _, _. iFrame.
        by iSplit.
    }
    wp_cmpxchg_fail.
    iDestruct ("HRRRestore" with "Hℓ") as "HRR".
    iDestruct ("HRRsRestore" with "HRR") as "HRRs".
    iMod (own_update with "H●") as "[H● H◯]".
    2: iSpecialize ("HΦ" $! false with "[H◯ HIsRes]");
      first by iFrame; iExists _, _.
    {
      apply auth_update_dfrac_alloc. by apply _.
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
    iSpecialize ("HΦ" $! true with "HE").
    (* a.d. FIXME this actually seems like a bug, you don't take the value here so the internal state gets messed up. *)
    (* iMod (take_cell_value_ra with "H●") as "[H● #H◯]".
    { erewrite list_lookup_insert=> //. lia. } *)
    (* rewrite list_insert_insert. *)
    iMod ("HTqClose" with "[-HΦ]"); last by iModIntro; wp_pures.
    iExists _, _. iFrame "H●". rewrite insert_length.
    iFrame. iSplitL.
    2: iPureIntro; by lia.
    iApply "HRRsRestore". simpl. iFrame. 
    iExists _. iFrame "H↦".
    iNext.
    by iFrame.
Qed.

Lemma acquire_resumer_resource_from_immediately_cancelled E' γtq γa γe γd γres i e d ℓ:
  (↑NTq ∪ ↑NArr) ⊆ E' ->
  is_thread_queue γa γtq γe γd γres e d -∗
  deq_front_at_least γtq (S i) -∗
  cell_cancelled γa i -∗
  cell_location γtq γa i ℓ -∗
  iterator_issued γd i ={E'}=∗
  ▷ R.
Proof.
  iIntros (HMask) "[#HInv _] #HDeqFront #HCancelled #H↦ HIsRes".
  iInv "HInv" as (l deqFront) "(HResShot & HTq)" "HClose".
  iMod (cell_cancelled_means_present with "HCancelled H↦ HTq") as
      "[HTq >HSkippable]"; first by solve_ndisj.
  iDestruct "HSkippable" as %(c & HEl & HCancelled).
  simpl in HCancelled.
  destruct c as [|? ? [[|]|]]=> //.
  iDestruct "HTq" as "(>H● & HRRs & HRest)".
  iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRs]"; first done.
  iDestruct (deq_front_at_least_valid with "H● HDeqFront") as %HDeqFront.
  rewrite bool_decide_true; last lia.
  simpl. iDestruct "HRR" as "(HIsSus & HRR)".
  iDestruct "HRR" as (ℓ' ℓk') "(>-> & H↦' & HLoc & Hℓ & HRR)".
  iDestruct "HRR" as "(HCallback & [>HIsRes' | HR])".
  1: iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
  iFrame "HR".
  iMod ("HClose" with "[-]"); last done. iExists _, _. iFrame "H● HRest HResShot".
  iApply "HRRs". iFrame. iExists _, _. by iFrame.
Qed.

(* TRANSITIONS ON CELLS IN THE NON-SUSPENDING CASE *****************************)

(* a.d. here the cell breaking token is used to rule out a case. We might have to add it 
   back just for this purpose even though we never break cells. *)
(* Lemma check_passed_value (suspender_side: bool) γtq γa γe γd i (ptr: loc):
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
Qed. *)

(* a.d. TODO it feels kinda weird to use the alter lemma here since they don't use it in other places.
   The question is then how do they update the logical state? 
   DONE they use big_sepL_insert_acc
   TODO also remove logically atomicity *)
(* Lemma read_cell_value_by_suspender_spec γtq γa γe γd i (ptr: loc):
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
    iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRsRestore]";
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
      * iApply "HRRsRestore".
        iFrame. iExists _. iFrame. by done.
      * rewrite insert_length. by iAssumption. 
    + by iPureIntro. 
    + iPureIntro. rewrite list_lookup_insert. done.
      apply lookup_lt_is_Some. eexists. by apply HEl.
    + iSplit; first by iPureIntro.
      by iApply "HRR".
Qed. *)

(* WHOLE OPERATIONS ON THE THREAD QUEUE ****************************************)

Lemma read_cell_value_by_resumer_spec γtq γa γe γd γres i ptr e d:
  {{{ is_thread_queue γa γtq γe γd γres e d ∗
      cell_location γtq γa i ptr ∗
      (* Needed to rule out the case of the cell being filled in multiple places. *)
      iterator_issued γd i }}}
    !#ptr
  {{{ (v: val), RET v;
      (⌜v = NONEV⌝ ∧ iterator_issued γd i ∨
       ⌜v = CANCELLEDV⌝ ∧ R ∨
       ∃ γk (ℓk: loc), ⌜v = InjLV #ℓk⌝ ∧ rendezvous_thread_handle γtq γk (#ℓk) i ∗ iterator_issued γd i)
  }}}.
Proof.
  iIntros (Φ) "(#HTq & #H↦ & HIsRes) HΦ".
  rewrite -fupd_wp.
  iMod (deq_front_at_least_from_iterator_issued with "[$] HIsRes")
    as "[#HDeqFront HIsRes]"; first done.
  iModIntro.
  iMod (acquire_cell _ _ _ _ _ _ with "H↦")
    as "[[#>HCellInit|[>Hℓ HCancHandle]] HCloseCell]"; first by solve_ndisj.
  2: { (* Cell was not yet inhabited, so NONEV is written in it. *)
    wp_load. iMod ("HCloseCell" with "[Hℓ HCancHandle]") as "_".
    by iRight; iFrame. iModIntro. 
    iApply "HΦ". by iLeft; iFrame.
  }
  (* We will not change the cell status so we can pack it back up. But we keep the knowledge that the cell is initialized. *)
  iSpecialize ("HCloseCell" with "[HCellInit]"); first by iLeft.
  (* So we open the invariant to check how exactly it is initialized. *)
  iDestruct "HTq" as "#(HInv & HInfArr & _ & HD)".
  iInv "HInv" as (l deqFront) "(HResShot & >H● & HRRs & >HLen)" "HTqClose".
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
  iDestruct "HRR" as "(HIsSus & HRR)". iDestruct "HRR" as (ℓ ℓk) "(>-> & H↦' & HLoc & HRR)".
  iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
  destruct c' as [[|]|].
  - (* Cell could not have been resumed already. *)
    iDestruct "HRR" as "(_ & >HContra & _)".
    iDestruct (iterator_issued_exclusive with "HContra HIsRes") as %[].
  - (* Cell is cancelled *)
    iDestruct "HRR" as "(Hℓ & HCallback & [HIsRes'|HR])".
    1: by iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as ">[]".
    wp_load.
    iSpecialize ("HΦ" $! CANCELLEDV with "[HR]").
    { iRight. iLeft. by iFrame. }
    iMod ("HTqClose" with "[-HCloseCell HΦ]").
    2: iModIntro; iMod "HCloseCell"; iModIntro; iApply "HΦ".
    iExists _, _. iNext. iFrame "H● HLen". iFrame. iApply "HRRsRestore".
    rewrite /cell_resources.
    iFrame. iExists _, _.
    iSplit; first done.
    by iFrame.
  - (* Cell is inhabited *) 
    iDestruct "HRR" as "(Hℓ & HCancHandle & HE & HR & HCallback &
      HInvoke)".
    (* a.d. TODO here they originally split the invokation permit and replaced one half with the resume pemit.
       I want to get the resume permit back so I don't do it here. So can we remove this construction and just keep the 
       invokation permit in cell_resources. *)
    (* iEval (rewrite -Qp_half_half callback_invokation_permit_Fractional)
      in "HInvoke".
    iDestruct "HInvoke" as "[HInvoke1 HInvoke2]". *)
    wp_load.
    iSpecialize ("HΦ" $! (InjLV _) with "[HIsRes]").
    { repeat iRight. iExists _, _. iFrame. iSplit=>//. }
    iMod ("HTqClose" with "[-HCloseCell HΦ]").
    2: iModIntro; iMod "HCloseCell"; iModIntro; by iAssumption.
    iExists _, _. iFrame "H● HLen". iFrame. iApply "HRRsRestore".
    iNext.
    iFrame. iExists _, _. iFrame.
    iSplit; first done. 
    iAssumption.
Qed.

Lemma take_cell_callback_spec γtq γa γe γd γk γres e d i (ptr ℓk: loc):
  {{{
    is_thread_queue γa γtq γe γd γres e d ∗
    rendezvous_thread_handle γtq γk #ℓk i ∗
    cell_location γtq γa i ptr ∗
    iterator_issued γd i
  }}}
  CAS #ptr (InjLV #ℓk) EIORESUMEDV @ ⊤
  {{{ (r: bool), RET #r;
      if r then 
        ∃ k, is_callback γk k ∗ callback_is_invoked γk #() ∗ WP (k #()) {{r, ⌜ r = #() ⌝ }} ∗ E
      else R }}}.
Proof.
  iIntros (Φ) "(#HTq & #HTh & #H↦ & HIsRes) HΦ".
  rewrite -fupd_wp.
  iMod (deq_front_at_least_from_iterator_issued with "[$] HIsRes")
    as "[#HDeqFront HIsRes]"; first done.
  iModIntro.
  wp_pures.
  wp_bind (CmpXchg _ _ _).
  (* open invariant to read reference *)
  iDestruct "HTq" as "(HInv & HTqRest)".
  iInv "HInv" as (l deqFront) "HOpen" "HClose".
  iDestruct "HOpen" as "(HResShot & >H● & HRRs & >%)".
  iDestruct (cell_list_contents_ra_locs with "H● HTh") as %(c & HEl).
  iAssert (⌜ S i ≤ deqFront ⌝)%I as %Hns.
  { by iApply (deq_front_at_least_valid with "H● HDeqFront"). }
  rewrite /cell_resources.
  destruct c as [[|]|].
  - (* cell cannot be already resumed *)
    iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    rewrite bool_decide_true; last by lia.
    iDestruct "HRR" as "(_ & HRR)".
    iDestruct "HRR" as (??) "(_ & _ & _ & _ & >HIsRes' & _)".
    iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
  - (* cell may already be cancelled, so return false. *) 
    iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    rewrite bool_decide_true; last by lia.
    iDestruct "HRR" as "(HIsSus & HRR)".
    iDestruct "HRR" as (??) "(>-> & #H↦' & _ & Hptr & HCallback & [>HIsRes'|HR])".
    iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
    iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
    wp_cmpxchg_fail.
    iMod ("HClose" with "[-HΦ HR]") as "_".
    { iExists _, _. iFrame. iSplit; last done. 
      iNext. iApply "HRRsRestore". 
      iFrame. iExists _, _.
      iFrame. 
      iSplit; first done. 
      by iSplit. }
    iModIntro.
    wp_pures.
    iApply "HΦ". by iFrame.
  - (* cell is waiting, CAS succeeds and we change the logical state. *)
    iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    rewrite bool_decide_true; last by lia.
    iDestruct "HRR" as "(HIsSus & HRR)".
    iDestruct "HRR" as (??) "(>#Hℓeq & #H↦' & #HTh' & Hptr & HCancHandle & HE & HR & HCallback & HRRes)".
    iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as ">->".
    wp_cmpxchg_suc.
    iDestruct "HRRes" as "HInvoke".
    (* now we need to update the logical state *)
    iMod (invokeCallback_spec with "HInvoke HCallback [HR]") as (k) "(Hk & HCallback & #HIsInvoked & #HIsCallback)".
    rewrite /V'. by iFrame.
    iMod (resume_cell_ra with "H●") as "(H● & HThResumed)"; first done.
    iMod ("HClose" with "[-HΦ Hk HE]") as "_".
    { iNext. iExists _, _. iFrame.
      rewrite insert_length.
      iSplit; last done.
      iApply ("HRRsRestore" $! (Some (cellInhabited γk #ℓk (Some cellResumed))) with "[Hptr HIsSus HIsRes HCancHandle HCallback]").
      iFrame. iExists _, _.
      iDestruct "Hℓeq" as %->.
      iSplit; first done. iFrame. 
      by iSplit. }
    iModIntro.
    wp_pures.
    iApply "HΦ".
    iExists _. iFrame.
    iModIntro. by iSplit.
Qed.

Lemma resume_spec γa γtq γe γd γres e d:
  {{{ is_thread_queue γa γtq γe γd γres e d ∗ awakening_permit γtq }}}
    resume array_interface d
  {{{ (r: bool), RET #r; if r then E else R }}}.
Proof.
  iIntros (Φ) "(#HTq & HAwak) HΦ".
  wp_lam. wp_bind (iteratorStepOrIncreaseCounter _ _ _).
  iApply (iteratorStepOrIncreaseCounter_spec _ _ NArr NDeq with "[HAwak]").
  by solve_ndisj.
  { iDestruct "HTq" as "(HInv & $ & HEnq & $)". by iFrame. }
  iIntros "!>" (?) "[[-> HCancelled]|HSuccess]".
  { rewrite -wp_fupd. 
    iDestruct "HCancelled" as (i) "(HCancelled & H↦ & HIsRes)".
    iDestruct "H↦" as (ℓ) "H↦".
    iMod (deq_front_at_least_from_iterator_issued with "[$] HIsRes")
      as "[#HDeqFront HIsRes]"; first done.
    iMod (acquire_resumer_resource_from_immediately_cancelled
            with "[$] HDeqFront HCancelled H↦ HIsRes") as "HR";
      first by solve_ndisj.
    wp_pures. iApply "HΦ". by iFrame.
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
  iIntros "!>" (?) "[[-> HIsSus]|[[-> HR]|HInhabited]]".
  - (* The cell is empty yet. *)
    wp_pures. wp_bind (Snd _).
    iApply (pass_value_to_empty_cell_spec with "[$]")=> //.
    iIntros "!>" (passingResult) "HPassingResult".
    destruct passingResult; wp_pures.
    2: { iDestruct "HPassingResult" as "(_ & HIsRes)".
         iApply ("IH" with "HΦ HIsRes"). }
    iApply ("HΦ"). by iFrame.
  - iClear "IH". 
    wp_pures. iApply "HΦ". by iFrame.
  - iClear "IH".
    iDestruct "HInhabited" as (γk k ->) "(#HTh & HIsRes)".
    wp_pures.
    wp_bind (Snd _).
    iApply (take_cell_callback_spec with "[$]").
    iIntros "!>" (takeResult) "HTakeResult".
    destruct takeResult.
    + (* take the callback out of the cell. *)
      iDestruct "HTakeResult" as (k') "(#HIsCallback & HCallbackInvoked & Hk & HE)".
      wp_pures.  
      (* a.d. TODO here I need to open the invariant to read again.
        I think it would be better if we just put a callback_is_invoked into the cellstate and return 
        the whole callback_invariant above, then we don't need to open the invariant again. *)
      wp_bind (! _)%E.
      (* open invariant to read callback reference *)
      iDestruct "HTq" as "(HInv & HTqRest)".
      iInv "HInv" as (l deqFront) "HOpen" "HClose".
      iDestruct "HOpen" as "(HResShot & >H● & HRRs & >%)".
      iDestruct (cell_list_contents_ra_locs with "H● HTh") as %(c & HEl).
      iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
        first done.
      iAssert (⌜ S ns ≤ deqFront ⌝)%I as %Hns.
      { by iApply (deq_front_at_least_valid with "H● HDeqFront"). }
      rewrite bool_decide_true; last by lia.
      rewrite /cell_resources.
      destruct c as [[|]|].
      2: {
        iDestruct "HRR" as "(_ & HRR)". 
        iDestruct "HRR" as (? ?) "(_ & _ & _ & _ & HCallback & _)".
        iDestruct "HCallback" as (?) "(_ & >HCallback● & _)".
        rewrite -fupd_wp.
        iMod (callback_is_cancelled_from_auth_ra with "HCallback●") as "(HCallback● & HCallbackCancelled)".
        iDestruct (callback_is_invoked_not_cancelled with "HCallbackInvoked HCallbackCancelled") as %[].
      }
      2: {
        iDestruct "HRR" as "(_ & HRR)". 
        iDestruct "HRR" as (? ?) "(_ & _ & _ & _ & _ & _ & _ & HCallback & _)".
        iDestruct "HCallback" as (?) "(_ & >HCallback● & _)".
        iDestruct (callback_is_invoked_not_waiting with "HCallbackInvoked HCallback●") as %[].
      }
      (* The invoked case is the only case that works. *)
      iDestruct "HRR" as "(HIsSus & HRR)".
      iDestruct "HRR" as (? ?) "(>-> & H↦' & _ & Hptr & HIsRes & HCancHandle & HCallback)".
      iDestruct "HCallback" as (?) "(Hℓk & HCallback● & _)".
      wp_load.
      iMod (is_callback_from_auth_ra with "HCallback●") as "(HCallback● & #HIsCallback')".
      (* closing everything up again *)
      iMod ("HClose" with "[-Hk HE HΦ]").
      { iExists _, _. iFrame. iSplit; last done.
        iApply "HRRsRestore". iFrame.
        iExists _, _. iFrame. iSplit; first done.
        iSplit; first done. 
        iNext. iExists _. iFrame. } 
      iModIntro.
      wp_pures.
      iDestruct (is_callback_agree with "HIsCallback HIsCallback'") as "->".
      wp_bind (k0 #()).
      iApply (wp_strong_mono with "Hk").
      by done. by done.
      iIntros (?) "-> !>".
      wp_pures.
      iApply "HΦ".
      by iFrame.
    + wp_pures. iApply "HΦ". by iFrame.
Qed.

Lemma resume_all_loop_spec γa γtq γe γd γres e d n:
  {{{ 
    is_thread_queue γa γtq γe γd γres e d ∗
    [∗] replicate n (awakening_permit γtq)
  }}}
  (rec: "loop" "n" :=
    if: "n" = #0 then #()
    else resume array_interface d;; "loop" ("n" - #1))%V #n
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(#HTq & HAwaks) HΦ".  
  iInduction n as [|n'] "IH".
  - wp_pures. by iApply "HΦ".
  - wp_pures.
    rewrite replicate_S.
    rewrite big_sepL_cons.
    iDestruct "HAwaks" as "(HAwak & HAwaks)".
    wp_bind (resume _ _).
    iApply (resume_spec with "[$]").
    iIntros "!>" (?) "_".
    do 3 wp_pure _.
    replace (Z.sub (S n') 1) with (Z.of_nat n'); last by lia.
    iApply ("IH" with "HAwaks HΦ").
Qed.

Theorem resume_all_spec γa γtq γe γd γres e d n:
  NTq ## NDeq →
  NTq ## NEnq →
  {{{
    is_thread_queue γa γtq γe γd γres e d ∗
    □ ▷ R ∗
    resume_all_permit γres ∗
    thread_queue_state γtq n
  }}}
    resume_all array_interface e d
  {{{ RET #(); True }}}.
Proof.
  iIntros (HDisj1 HDisj2 Φ) "(#HTq & #HR & HResShot & HState) HΦ".
  iAssert (is_thread_queue γa γtq γe γd γres e d)%I with "HTq" as "#HTq'".
  iDestruct "HTq'" as "(HInv & HArray & HEnq & HDeq)".
  wp_lam. wp_pures.
  rewrite /is_iterator.
  (* read from enqueue iterator *)
  wp_bind (! _)%E.
  iDestruct "HEnq" as (ℓe pe) "(-> & HeInv)".
  wp_pures.
  iInv "HeInv" as (enqCtr) "HOpen" "HClose".
  rewrite /iterator_contents /iterator_counter.
  iDestruct "HOpen" as "((Hℓe & Hcounter) & HOpen)". 
  wp_load.
  iMod (iterator_counter_is_at_least with "Hcounter") as "(Hcounter & #HeAtLeast)".
  iMod ("HClose" with "[Hℓe Hcounter HOpen]") as "_".
  { iExists _. iFrame. }
  iModIntro.
  wp_pures.
  (* read from dequeue iterator *)
  wp_bind (! _)%E.
  iDestruct "HDeq" as (ℓd pd) "(-> & HdInv)".
  wp_pures.
  iInv "HdInv" as (deqCtr) "HOpen" "HClose".
  rewrite /iterator_contents /iterator_counter.
  iDestruct "HOpen" as "((Hℓd & Hcounter) & HOpen)". 
  wp_load.
  iMod (iterator_counter_is_at_least with "Hcounter") as "(Hcounter & #HdAtLeast)".
  iMod ("HClose" with "[Hℓd Hcounter HOpen]") as "_".
  { iExists _. iFrame. }
  iModIntro.
  do 2 wp_pure _.
  wp_bind (_ - _)%E.
  (* open thread queue invariant to know its size. *)
  iInv "HInv" as (l deqFront) "(>[-> | HResShot'] & HOpen)" "HClose". 
  2: { iDestruct (resume_all_permit_exclusive with "HResShot HResShot'") as %[]. }
  iDestruct "HOpen" as "(>H● & HRRs & >%)".
  iMod (access_iterator_resources _ _ _  NEnq with "[HeInv] HeAtLeast") as "(HRes & HResRestore)";
    first by solve_ndisj. 
  { iExists _, _. iSplit; first done. iAssumption. }
  iAssert (▷ ⌜ enqCtr ≤ length l ⌝)%I with "[#]" as ">%".
  { iNext. iApply (suspension_permit_implies_bound with "H● HRes"). }
  iMod ("HResRestore" with "HRes") as "_".
  iMod (access_iterator_resources _ _ _  NDeq with "[HdInv] HdAtLeast") as "(HRes & HResRestore)";
    first by solve_ndisj. 
  { iExists _, _. iSplit; first done. iAssumption. }
  iAssert (▷ ⌜ deqCtr ≤ 0 ⌝)%I with "[#]" as ">%".
  { iNext. iApply (awakening_permit_implies_bound with "H● HRes"). }
  iMod ("HResRestore" with "HRes") as "_".
  iDestruct (thread_queue_state_valid with "H● HState") as %Hn.
  rewrite drop_length in Hn. rewrite Nat.sub_0_r in Hn.
  assert (HdeqCtr: deqCtr = 0) by lia.
  iMod ("HClose" with "[H● HRRs]") as "_".
  { iExists _, 0. iSplitR; first by iLeft.
    iNext. iFrame. iPureIntro. lia. }
  (* take awakening permits *)
  rewrite -fupd_wp.
  iMod (thread_queue_register_for_dequeue_all' _ γtq γa γe γd γres _ enqCtr with "HResShot HTq HR HState") as "(HState & HAwaks)"; 
    first by solve_ndisj.
  by lia.
  iModIntro.
  simplify_eq.
  wp_pure _.
  iApply fupd_mask_intro_subseteq; first by solve_ndisj.
  iApply fupd_mask_intro_subseteq; first by solve_ndisj.
  iApply fupd_mask_intro_subseteq; first by solve_ndisj.
  replace (Z.sub enqCtr O) with (Z.of_nat enqCtr) by lia.
  do 3 wp_pure _.
  iApply (resume_all_loop_spec with "[HAwaks]").
  { by iFrame. }
  iNext.
  by iAssumption.
Qed.

Definition is_thread_queue_suspend_result γtq γa γk (r: val) k: iProp :=
  (* a.d. TODO this should also directly use a location instead of a value k. *)
  ∃ ℓk i, rendezvous_thread_handle γtq γk ℓk i ∗
    is_callback γk k ∗
    callback_cancellation_permit γk 1%Qp ∗
    (* TODO why do we have this? *)
    is_infinite_array_cell_pointer _ _ array_spec NArr γa r i.

Lemma read_cell_value_by_suspender_spec' γtq γa γe γd i (ptr: loc) l deqFront Mask:
  {{{  
  (* this implies that there is a value (but it might already have been taked).
     a.d. TODO check that the iterator_issued below makes sure that we can only be in the non-taken case. *)
  rendezvous_filled_value γtq #() i ∗
  (* this is used to read from the infinite array *)
  cell_location γtq γa i ptr ∗
  (* used to swap out of the R in the cellState *)
  iterator_issued γe i ∗
  ▷ thread_queue_invariant γa γtq γe γd l deqFront }}}
    !#ptr @ Mask
  {{{ v, RET v; ∃ l', thread_queue_invariant γa γtq γe γd l' deqFront ∗
           ⌜ l' = <[i := Some (cellPassedValue (Some tt))]> l ⌝ ∗
           ⌜v = EIORESUMEDV⌝ ∧ R }}}.
Proof.
  iIntros (Φ) "(#HFilled & #H↦ & HCellBreaking & HInv) HΦ". 
  rewrite /thread_queue_invariant.
  iDestruct "HInv" as "(>H● & HRRs & >HLen)".
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
    iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    simpl. iDestruct "HRR" as "(HIsRes & HCancHandle & HRR)".
    iDestruct "HRR" as (ℓ) "[H↦' HRR]".
    iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
    iDestruct "HRR" as "(Hptr & HRR)".
    iApply fupd_wp.
    iMod (take_cell_value_ra with "H●") as "[H● #H◯]"; first by done.
    iModIntro. wp_load.
    iApply "HΦ".
    iExists _. iFrame. 
    iModIntro.
    iSplit; iSplit.
    + iApply "HRRsRestore".
      iFrame. iExists _. iFrame. iAssumption.
    + by rewrite insert_length.
    + done.
    + done.
Qed.

Theorem suspend_spec γa γtq γe γd γres e d k:
  (* the invariant about the state of CQS. *) 
  {{{ is_thread_queue γa γtq γe γd γres e d ∗ 
  (* a generic permit to call suspend *)
      suspension_permit γtq ∗ 
  (* the WP of the closure k so that we can create a callback. *)
      is_waker V' k
       }}}
    suspend array_interface e k
  {{{ v, RET v; ⌜v = NONEV⌝ ∨
                ∃ γk v', ⌜v = SOMEV v'⌝ ∗
                         is_thread_queue_suspend_result γtq γa γk v' k }}}.
Proof.
  iIntros (Φ) "(#HTq & HIsSus & Hk) HΦ".
  wp_lam. wp_pures. wp_bind (newCallback _).
  iApply  (newCallback_spec with "Hk"). 
  iNext.
  iIntros (ℓk γk) "(#HIsCallback & HCallback & HInvoke & HCancel)".
  wp_pures.
  wp_bind (iteratorStep _ _). iApply (iteratorStep_spec with "[HIsSus]").
  2: { by iDestruct "HTq" as "(_ & $ & $ & _)". }
  by solve_ndisj.
  iIntros "!>" (n ns s) "HEnqResult". destruct (decide (ns = n)) as [->|HContra].
  2: { (* someone else cancelled our cell, but it's impossible. *)
    iDestruct "HEnqResult" as "(% & HIsSus & _ & #HCancelled)".
    iDestruct ("HCancelled" $! n with "[%]") as "[HNCancelled H↦]"; first lia.
    iDestruct "H↦" as (ℓ) "H↦". iDestruct "HTq" as "[HInv _]". rewrite -fupd_wp.
    iInv "HInv" as (? ?) "(HResShot & HOpen)" "HClose".
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
    iExists _, _.
    iModIntro.
    iSplit; first done.
    iSplit; first done.
    by iAssumption.
  }
  (* the cell is already filled. 
     we know it can only be due to a value, so we call the callback ourselves *)
  wp_pures. wp_bind (!_)%E.
  iDestruct "HResult" as "(#HFilled & HIsSus & HCallback & HInvoke)".
  iDestruct "HTq" as "(HInv & HRest)". iInv "HInv" as (l deqFront) "(HResShot & HOpen)" "HClose".
  iApply (read_cell_value_by_suspender_spec' with "[HFilled H↦ HIsSus HOpen]").
  { iFrame. repeat iSplit. 
    iApply "HFilled". iApply "H↦". }
  iNext.
  iIntros (?) "H".
  iDestruct "H" as (l') "(HTq & HEl & -> & HRR)".
  (* iAssert (▷ callback_invariant V' γk k CallbackWaiting)%I with "HCallback" as "HCallback". *)
  (* awp_apply (read_cell_value_by_suspender_spec with "HFilled H↦ HIsSus")
    without "HΦ".
  iAaccIntro with "HOpen". iIntros "HOpen !>"; iSplitR "HCallback HInvoke HCancel"; first iExists _, _. 
    by done. 
    by iFrame. *)
  (* iIntros (? ?) "(HTq & -> & HEl & -> & HRR)".  *)
  iMod ("HClose" with "[HResShot HTq]").
  { iNext. iExists _, _. iFrame. }
  iModIntro.
  (* rendezvous succeeded, we may safely leave. *)
  wp_pures.
  wp_bind (k #()).
  (* change the logical state of the callback. *)
  iApply fupd_wp.
  iMod (invokeCallback_spec with "HInvoke HCallback [HRR]") as (k') "(Hk & HCallback & #HCallbackInvoked & #HIsCallback')".
  { rewrite /V'. by iFrame. }
  iDestruct (is_callback_agree with "HIsCallback HIsCallback'") as %->.
  iModIntro.
  iApply (wp_strong_mono with "Hk"); [by done|by done|].
  iIntros (? ->).
  iModIntro.
  wp_pures.
  iApply "HΦ".
  iModIntro.
  by iLeft. 
Qed.

Lemma read_cell_value_by_canceller_spec γtq γa γe γd γk i ptr k l deqFront Mask:
  {{{ cell_location γtq γa i ptr ∗
      rendezvous_thread_locs_state γtq γk k i ∗
      callback_cancellation_permit γk 1%Qp ∗
      ▷ thread_queue_invariant γa γtq γe γd l deqFront }}}
    !#ptr @ Mask
  {{{ (v: val), RET v;
      thread_queue_invariant γa γtq γe γd l deqFront ∗
      (⌜v = EIORESUMEDV⌝ ∨ 
      (* a.d. TODO maybe use #ℓk directly instead of a generic k?
         Then I don't need all the inequalities. *)
      ⌜v = InjLV k⌝ ∗ ⌜ k ≠ #1 ⌝ ∗ ⌜ k ≠ #() ⌝ ∗ callback_cancellation_permit γk 1%Qp)
  }}}.
Proof.
  iIntros (Φ) "(#H↦ & HInhabited & HCancel & HInv) HΦ". 
  rewrite /thread_queue_invariant.
  iDestruct "HInv" as "(>H● & HRRs & >HLen)".
  iDestruct (cell_list_contents_ra_locs with "H● HInhabited") as %(c' & HEl).
  destruct c' as [[|]|]=> /=.
  - (* value was already taken *) 
    iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    simpl. iDestruct "HRR" as "(HIsRes & HRR)".
    iDestruct "HRR" as (ℓ ℓk) "(>-> & H↦' & HHandle & HRR)".
    iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
    iDestruct "HRR" as "(Hptr & HRR)".
    wp_load.
    iApply "HΦ". iSplitL; last by iLeft.
    iFrame.
    iApply "HRRsRestore". iFrame.
    iExists _, _. iModIntro. iFrame.
    iSplit; first done. by iAssumption.
  - (* cell is already cancelled, this cannot happen *) 
    iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    simpl. iDestruct "HRR" as "(HIsRes & HRR)".
    iDestruct "HRR" as (ℓ ℓk) "(>-> & H↦' & HHandle & Hptr & >HCallback & _)".
    iDestruct "HCallback" as (k) "(Hℓk & HCallback & _)".
    rewrite -fupd_wp.
    iMod (callback_is_cancelled_from_auth_ra with "HCallback") as "[_ HCallbackCancelled]".
    iDestruct (callback_cancellation_permit_implies_not_cancelled with "HCancel HCallbackCancelled") as %[].
  - (* callback is in waiting state. *)
    iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    simpl. iDestruct "HRR" as "(HIsRes & HRR)".
    iDestruct "HRR" as (ℓ ℓk) "(>-> & H↦' & HHandle & HRR)".
    iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
    iDestruct "HRR" as "(Hptr & HRR)".
    wp_load.
    iApply "HΦ". iSplitR "HCancel".
    2: { iRight. 
          iModIntro.
          iSplit; first done.
          iSplit; first done.
          iSplit; first done.
          iFrame. }
    iFrame. iApply "HRRsRestore".
    iFrame. 
    iExists _, _. iFrame.
    iModIntro.
    iSplit; done.
Qed.


Theorem try_cancel_spec γa γtq γe γd γres e d γk r k:
  (* the invariant about the state of CQS. *)
  {{{ is_thread_queue γa γtq γe γd γres e d ∗ 
      is_thread_queue_suspend_result γtq γa γk r k}}}
    try_cancel array_interface r
  {{{ (b: bool), RET #b; if b then 
                  (* is_waker gives us the WP for executing k *)
                          is_waker V' k ∗ 
                  (* we have a persistent piece of information that the callback is cancelled. *)
                          callback_is_cancelled γk
                  (* if cancellation fails we don't know anything (on the metalevel we know that another thread will eventually call k, but we don't have this linearity in the Iris proof yet). *)
                  else True }}}.
Proof.
  iIntros (Φ) "(#HTq & HRes) HΦ".
  rewrite /is_thread_queue_suspend_result.
  iDestruct "HRes" as (ℓk i) "(#HHandle & #HIsCallback & HCancel & #HArray)".
  wp_lam.
  wp_bind (derefCellPointer _ _). iApply (derefCellPointer_spec with "[]").
  { iDestruct "HTq" as "(_ & $ & _)". done. }
  iIntros "!>" (ℓ) "#H↦". wp_pures. 
  wp_bind (!_)%E.
  (* a.d. TODO move opening the invariant into read_cell_value_by_cancelled_spec like in the other two lemmas. *)
  iDestruct "HTq" as "(HInv & HIsArray & HEnqueue & HDequeue)".
  iInv "HInv" as (l deqFront) "(HResShot & HOpen)" "HClose".
  iApply (read_cell_value_by_canceller_spec with "[HOpen HCancel]").
  { iFrame. iSplit; done. }
  iNext.
  iIntros (v) "(HOpen & HResult)".
  iMod ("HClose" with "[HResShot HOpen]").
  { iNext. iExists _, _. by iFrame. }
  clear l deqFront.
  iModIntro.
  iDestruct "HResult" as "[->|(-> & % & % & HCancel)]".
  - (* already resumed so we just return false. *)
    wp_pures.
    by iApply "HΦ".
  - (* at the moment there is an uncancelled callback. We try to CAS it and then call it. *)
    wp_pures. 
    rewrite bool_decide_false; last by injection.
    wp_pures. 
    rewrite bool_decide_false; last by injection.
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    iInv "HInv" as (l deqFront) "(HResShot & >H● & HRRs & >HLen)" "HTqClose".
    iDestruct "HLen" as %HLen.
    iAssert (⌜∃ c : option cellTerminalState,
                  l !! i = Some (Some (cellInhabited γk ℓk c))⌝)%I as %(c & HEl).
    { iApply (cell_list_contents_ra_locs with "H● HHandle"). }
    iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    destruct c as [[|]|].
    + (* now the callback is already resumed. *)
      iDestruct "HRR" as "(>HIsSus & HRR)".
      iDestruct "HRR" as (ℓ' ℓk') "(>-> & #H↦' & HHandle' & Hℓ & HRR)".
      iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
      wp_cmpxchg_fail. 
      iDestruct ("HRRsRestore" $! (Some (cellInhabited γk #ℓk' (Some cellResumed))) with "[HIsSus HHandle' H↦' HRR Hℓ]") as "HRRs".
      { iFrame. 
        iExists _, _. 
        iSplit; first done. by iFrame. }
      iMod ("HTqClose" with "[-HΦ]") as "_".
      { iExists _, _. iFrame. iNext.
        rewrite list_insert_id; last by done.
        iSplit; last by done.
        done. }
      iModIntro. wp_pures.
      by iApply "HΦ".
    + (* callback is cancelled should lead to contradiction. *)
      rewrite /cell_resources.
      iDestruct "HRR" as "(>HIsSus & HRR)".
      iDestruct "HRR" as (ℓ' ℓk') "(>-> & _ & _ & _ & >HCallback & _)".
      iApply fupd_wp.
      iDestruct "HCallback" as (k') "(Hℓk & HCallback● & _)".
      iMod (callback_is_cancelled_from_auth_ra with "HCallback●") as "[HCallback● HCallbackCancelled]".
      by iDestruct (callback_cancellation_permit_implies_not_cancelled with "HCancel HCallbackCancelled") as %[].
    + (* callback is still not resumed *)
      iDestruct "HRR" as "(>HIsSus & HRR)".
      iDestruct "HRR" as (ℓ' ℓk') "(>-> & #H↦' & HHandle' & Hℓ & HCancHandle & HRR)".
      iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
      simpl.
      wp_cmpxchg_suc.
      iDestruct "HRR" as "(HE & HR & HCallback & HRR)".
      (* update the callback invariant *)
      iMod (cancelCallback_spec with "HIsCallback HCancel HCallback") as "(Hk & HCallback & HCallbackCancelled)".
      iDestruct ("HRRsRestore" $! (Some (cellInhabited γk #ℓk' (Some cellImmediatelyCancelled))) with "[HIsSus HHandle' H↦' HRR Hℓ HCallback HR]") as "HRRs".
      { iFrame. 
        iExists _, _. 
        iSplit; first done. 
        iFrame.
        by iAssumption. }
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
      iModIntro.
      iFrame.
Qed.

End proof.

Print Assumptions suspend_spec.
Print Assumptions resume_all_spec.
Print Assumptions try_cancel_spec.

Typeclasses Opaque inhabited_rendezvous_state
 filled_rendezvous_state
 thread_queue_state deq_front_at_least
 rendezvous_thread_locs_state rendezvous_filled_value
 rendezvous_thread_handle rendezvous_initialized suspension_permit
 awakening_permit cell_resources cell_enqueued
 thread_queue_invariant is_thread_queue_suspend_result.
