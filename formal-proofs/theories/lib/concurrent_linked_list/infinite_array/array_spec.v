From iris.program_logic Require Import atomic.
From iris.heap_lang Require Export proofmode notation lang.
Require Export
        SegmentQueue.lib.concurrent_linked_list.infinite_array.array_interfaces.

(* a.d. Note that there are 3 different kinds of indices commonly used in the infinite array.
  idx              : index of the cell in the infinite array, theoretically 0..∞
  id               : index of the segment, increments in steps of SEGMENT_SIZE
  i (ix sometimes) : index of the cell within a segment, 0..SEGMENT_SIZE

  we have idx = id * SEGMENT_SIZE + i
  but the naming seems to be not consistent.
*)
Record infiniteArraySpec Σ `{!heapG Σ} (impl: infiniteArrayInterface) :=
  InfiniteArraySpec {
      (* a.d. proposition to be an infinite array.
        cell_is_owned seems to be a predicate on array indices that says that the cell is not in the initial NONEV state. *)
      is_infinite_array (N: namespace) (γ: gname)
                        (cell_is_owned: nat → iProp Σ): iProp Σ;
      is_infinite_array_persistent N γ co:
        Persistent (is_infinite_array N γ co);
      (* a.d. ℓ is the i'th item in the infinite array identified by γ and points to some cell data. *)
      infinite_array_mapsto (N: namespace) (cell_is_owned: nat -> iProp Σ)
                            (γ: gname) (i: nat) (ℓ: loc): iProp Σ;
      infinite_array_mapsto_persistent N co γ i ℓ:
        Persistent (infinite_array_mapsto N co γ i ℓ);
      infinite_array_mapsto_agree N co γ i ℓ ℓ':
        infinite_array_mapsto N co γ i ℓ -∗ infinite_array_mapsto N co γ i ℓ'
                              -∗ ⌜ℓ = ℓ'⌝;
      (* a.d. a cell pointer (pair of segment & cell index) identifies a cell with index i in the infinite array. *)
      is_infinite_array_cell_pointer N (γ: gname) (p: val) (i: nat):
          iProp Σ;
      (* a.d. the result of dereferencing a segment pointer.
         p is is the segment
         start_id is the id of the first cell in the segment, so it's segment_id * SEGMENT_SIZE *)
      is_infinite_array_cutoff_reading (N: namespace) (γ: gname)
                                       (p: val) (start_id: nat): iProp Σ;
      is_infinite_array_cutoff_reading_persistent N γ p start_id:
        Persistent (is_infinite_array_cutoff_reading N γ p start_id);
      is_infinite_array_cell_pointer_persistent N γ p i:
        Persistent (is_infinite_array_cell_pointer N γ p i);
      (* a.d. a "cutoff" is a segment pointer (CQS has 2, resumeSegm & suspendSegm),
         which are the push-head & pop-head of the queue. 
         start_index is the id of the segment the segment pointer is pointing to right now. *)
      is_infinite_array_cutoff
        (N: namespace) (γ: gname) (v: val)
        (start_index: nat): iProp Σ;
      (* a.d. i'th cell in the infinite array γ is cancelled. *)
      cell_is_cancelled (N: namespace) (γ: gname) (i: nat): iProp Σ;
      cell_is_cancelled_persistent N γ i: Persistent (cell_is_cancelled N γ i);
      (* a.d. permission to cancel the i'th cell in the infinite array γ *)
      cell_cancellation_handle
        (N: namespace) (γ: gname) (i: nat): iProp Σ;
      cell_cancellation_handle_exclusive N γ i:
        cell_cancellation_handle N γ i -∗ cell_cancellation_handle N γ i -∗ False;
      (* a.d. the cancellation handle is consumed when cancelling the cell, so it cannot both exist and be cancelled. *)
      cell_cancellation_handle_not_cancelled N γ i:
        cell_is_cancelled N γ i -∗ cell_cancellation_handle N γ i -∗ False;
      (* A logical operation of accessing an infinite array cell for the first time is introduced. This operation provides
each caller either with both the exclusive right for writing to the cell and the cell cancellation handle, or with
the evidence that the caller was not in fact the first one to attempt this operation; this evidence is called the
knowledge that the cell is owned. The user of the infinite array themselves decide what logical resource is
used to signify that the cell is owned.
      
         a.d. invariant access lemma (mapsto seems to be a general resource that just says the cell exists)
         cell_is_owned seems to say that cell is not in the original NONEV state, 
          either it is already owned or ℓ ↦ NONEV and we get a cancellation handle.
          Then we can write something else to ℓ and probably get a cell_is_owned to put back into the invariant.  *)
      acquire_cell N cell_is_owned E γ i ℓ:
        ↑N ⊆ E →
        infinite_array_mapsto N cell_is_owned γ i ℓ ={E, E∖↑N}=∗
        ▷ (cell_is_owned i ∨ ℓ ↦ NONEV ∗ cell_cancellation_handle N γ i) ∗
        (▷ (cell_is_owned i ∨ ℓ ↦ NONEV ∗ cell_cancellation_handle N γ i)
         ={E∖↑N, E}=∗ True);
      (* Array creation that allocates n segment pointers (with n = 2 in case of the CQS, the pointers being resume-
Segm and suspendSegm)—performed by allocating the concurrent linked list.
         a.d. the addition ℓ +₁ i seems to be for returning an multiple pointers. *)
      newInfiniteArray_spec N co k:
        {{{ ⌜(k > 0)%nat⌝ ∧ inv_heap_inv }}}
          newInfiniteArray impl #k
        {{{ γ ℓ, RET #ℓ; is_infinite_array N γ co ∗
                        [∗ list] i ∈ seq 0 k,
                          is_infinite_array_cutoff N γ #(ℓ +ₗ Z.of_nat i) 0
        }}};
      (* Cancelling a cell—done with a call to onCancelledCell() on the underlying segment; *)
      cancelCell_spec N γ co p i:
        is_infinite_array N γ co -∗
        is_infinite_array_cell_pointer N γ p i -∗
        <<< ▷ cell_cancellation_handle N γ i >>>
            cancelCell impl p @ ⊤ ∖ ↑N
        <<< ▷ cell_is_cancelled N γ i, RET #() >>>;
      (* Finding a cell with the given id—performed with a call to s0 = findSegment(s, id / SEGM SIZE) and
later checking whether the requested segment identifier corresponds with the requested one and returning
(s0 , id mod SEGM SIZE) if so and (s0 , 0) otherwise.

        p is s from the paper (a segment)
        source_id is the segment id of p
        id is the array index of the cell we want to advance p to. *)
      findCell_spec N γ co p (source_id id: nat):
        {{{ is_infinite_array N γ co ∗
            is_infinite_array_cutoff_reading N γ p source_id }}}
        findCell impl p #id @ ⊤
        {{{ p' id', RET p'; is_infinite_array_cell_pointer N γ p' id'
            ∗ ⌜(id ≤ id')%nat⌝
            ∗ ∀ i, (⌜max source_id id ≤ i < id'⌝)%nat -∗
              cell_is_cancelled N γ i ∗ ∃ ℓ, infinite_array_mapsto N co γ i ℓ
        }}};
      (* a.d. dereferencing a cell pointer gives you a reference to the cell contents (kind of weird nesting) *)
      derefCellPointer_spec N co γ (p: val) i:
        {{{ is_infinite_array N γ co ∗ is_infinite_array_cell_pointer N γ p i }}}
          derefCellPointer impl p
        {{{ ℓ, RET #ℓ; infinite_array_mapsto N co γ i ℓ }}};
      (* Moving a segment pointer forward—done with a call to moveForward(..).

         a.d. in Coq they call a segment pointer ("resumeSegm"/"suspendSegm") a "cutoff".
         p is "to" from the paper
         v is "resumeSegm/suspendSegm" from the paper.
         
         This tries to move the segment pointer forwards so that it points to a segment of at least the segment index corresponding to the array index i. 
         If it succeeds, then there is some segment id i' and the segment pointer now points to this segment.
         Otherwise, the segment pointer was not changed. (TODO kind of strange since the segment pointer can be mutated concurrently, that's the reason why this function can fail.)
         *)
      cutoffMoveForward_spec N co γ (p v: val) i:
        is_infinite_array N γ co -∗
        is_infinite_array_cell_pointer N γ p i -∗
        <<< ∀ start_index, ▷ is_infinite_array_cutoff N γ v start_index >>>
          cutoffMoveForward impl v p @ ⊤ ∖ ↑N
        <<< ∃ (success: bool), if success
            then ∃ i', ⌜start_index ≤ i' ≤ max i start_index⌝ ∧
                      is_infinite_array_cutoff N γ v i'
            else ▷ is_infinite_array_cutoff N γ v start_index, RET #success >>>;
      (* Reading a segment pointer.
      
        a.d. reading a segment pointer gives you a segment pointer reading. duh
        the segment pointer reading is value p representing a segment, and i is the segment id. 
        v is #ℓ for some location ℓ *)
      cutoffGetPointer_spec N γ (v: val):
        ⊢ <<< ∀ i, ▷ is_infinite_array_cutoff N γ v i >>>
          cutoffGetPointer impl v @ ⊤
        <<< ∃ (p: val), is_infinite_array_cutoff N γ v i ∗
                        is_infinite_array_cutoff_reading N γ p i, RET p >>>;
      (* Checking the index of a cell—equal to s.id · SEGM SIZE + i, where the cell is (s, i); *)
      cellPointerId_spec N co γ (p: val) i:
        {{{ is_infinite_array N γ co ∗ is_infinite_array_cell_pointer N γ p i }}}
          cellPointerId impl p
        {{{ RET #i; True }}};
      (* Setting prev of the underlying segment of a cell to null;  *)
      cellPointerCleanPrev_spec N co γ (p: val) i:
        {{{ is_infinite_array N γ co ∗ is_infinite_array_cell_pointer N γ p i }}}
          cellPointerCleanPrev impl p
        {{{ RET #(); True }}};
    }.

Existing Instances is_infinite_array_persistent
         infinite_array_mapsto_persistent
         is_infinite_array_cell_pointer_persistent
         is_infinite_array_cutoff_reading_persistent
         cell_is_cancelled_persistent.
