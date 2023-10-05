From SegmentQueue.lib.concurrent_linked_list
     Require Export list_interfaces segment_spec.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Export proofmode notation lang.
Open Scope nat.

Record listSpec Σ `{!heapG Σ}
       (impl: listInterface)
       {seg_impl: segmentInterface}
       (segment_spec: segmentSpec Σ seg_impl) :=
  ListSpec {
      (* a.d. a proposition that the gname identifies a linked list 
        TODO what are the parameters?  *)
      is_concurrentLinkedList:
        namespace ->
        linkedListNode_parameters _ _ (linkedListNode_base _ _ segment_spec) ->
        gname -> iProp Σ;
      is_concurrentLinkedList_persistent N p γ:
        Persistent (is_concurrentLinkedList N p γ);
      (* a.d. a proposition that γs represents a segment in the whole list identified by γ
          γ identifies the whole linked list
          γs identifies the segment (TODO I'm not sure why they don't just use gname, but do some indirection with the linkedListNode_name)
          id the ID of the segment
          v the value representing the segment in the program *)
      segment_in_list
        (γ: gname)
        (γs: linkedListNode_name _ _ (linkedListNode_base _ _ segment_spec))
        (id: nat)
        (v: val): iProp Σ;
      segment_in_list_persistent γ γs id v:
        Persistent (segment_in_list γ γs id v);
      segment_in_list_agree γ id γs v γs' v':
        segment_in_list γ γs id v -∗ segment_in_list γ γs' id v' -∗
                        ⌜v = v' ∧ γs = γs'⌝;
      (* First, we have the knowledge that a segment is logically removed; this resource is freely duplicable,
which implies that a once-removed segment cannot stop being removed, and is physically represented as cancelled
being equal to SEGM SIZE and pointers being 0 simultaneously.
      If pointers is 0 and cancelled is SEGM SIZE, the segment is logically removed; otherwise, it is not logically
removed and either there exist some pieces of the cancelled counter or pointers is not yet SEGM SIZE.

      a.d. γ identifies the linked list, id is the segment ID. *)
      segment_is_cancelled: gname -> nat -> iProp Σ;
      segment_is_cancelled_persistent γ id:
        Persistent (segment_is_cancelled γ id);
      (* The second resource is the knowledge that a segment
pointer p (in this program, p is either resumeSegm or suspendSegm) points to i, which means two things: first, that
p contains a reference to a segment whose id is i 
      a.d. gname identifies the whole list
           loc is the pointer to the segment
           nat is the segment ID *)
      pointer_location: gname -> loc -> nat -> iProp Σ;
      (* a.d. TODO not sure what a Node is
        if we have a linked list and a segment, then we can also get a node and we associate the segment ID with γs. *)
      segment_in_list_is_node N p E γ γs id v:
        ↑N ⊆ E →
        is_concurrentLinkedList N p γ -∗
        segment_in_list γ γs id v ={E}=∗
        ▷ is_linkedListNode _ _ (linkedListNode_base _ _ segment_spec) p γs v ∗
        ▷ has_value (id_uniqueValue _ _ segment_spec) γs id;
      (* If a segment n was part of the linked list at some point, then segments [0..n − 1] also were part of the list. *)
      segment_implies_preceding_segments N p E γ γs id v:
        ↑N ⊆ E →
        is_concurrentLinkedList N p γ -∗
        segment_in_list γ γs id v ={E}=∗
        ∀ i, ⌜i ≤ id⌝ -∗ ∃ γs' v', segment_in_list γ γs' i v';
      (* a.d. creating a new list of size k returns an array of pointers ℓ that point to segments. *)
      newList_spec N p (k: nat):
        {{{ ⌜k > 0⌝ ∧ initialization_requirements _ _ segment_spec }}}
          newList impl #k
        {{{ γ ℓ, RET #ℓ; is_concurrentLinkedList N p γ ∗
                        [∗ list] i ∈ seq 0 k,
                            pointer_location γ (ℓ +ₗ (i: nat)) 0
        }}};
      (* The findSegment(s, id) operation takes as arguments a segment s with identifier s.id and id, and returns some
segment t such that t.id ≥ s.id, t.id ≥ id, and all the segments in [max(s.id, id); t.id) are cancelled. *)
      findSegment_spec N p γ γs' (start_id id: nat) v:
        {{{ is_concurrentLinkedList N p γ ∗ segment_in_list γ γs' start_id v }}}
          findSegment impl v #id
        {{{ (v': val) (id': nat), RET (SOMEV v');
          (∃ γs, segment_in_list γ γs id' v')
          ∗ ⌜(start_id ≤ id' ∧ id ≤ id')%nat⌝
          ∗ ∀ i, (⌜max start_id id ≤ i < id'⌝)%nat -∗ segment_is_cancelled γ i
        }}};
      (* The moveForward[p](to) operation is a logically atomic operation that, if p points to from, returns true if p now
points to the maximum of from and to.id, and false if to is logically removed, in which case p points to from. *)
      moveForward_spec N p γ γs (ℓ: loc) id v:
        is_concurrentLinkedList N p γ -∗
        segment_in_list γ γs id v -∗
        <<< ∀ id', ▷ pointer_location γ ℓ id' >>>
          moveForward impl #ℓ v @ ⊤ ∖ ↑N
        <<< ∃ (r: bool), if r then pointer_location γ ℓ (max id id')
                              else ▷ pointer_location γ ℓ id'
                                   ∗ segment_is_cancelled γ id,
            RET #r >>>;
      (* Last, setting the prev of a segment to null is always valid and has no effect. *)
      cleanPrev_spec N p γ γs id ptr:
        {{{ is_concurrentLinkedList N p γ ∗ segment_in_list γ γs id ptr }}}
          cleanPrev impl ptr
        {{{ RET #(); True }}};
      (* The onCancelledCell() operation is a logically atomic operation that is parameterized by some logical resources Φ
and Ψ such that the existence of Φ implies that the cancelled counter in the segment is not yet equal to SEGM SIZE
and it is possible to correctly increase it by 1 by relinquishing the ownership of Φ, obtaining Ψ in return. The operation
atomically exchanges Φ for Ψ, which means that the ability to increase cancelled both existed and was utilized. *)
      onSlotCleaned_spec N pars Ψ P γ γs id p:
        is_concurrentLinkedList N pars γ -∗
        segment_in_list γ γs id p -∗
        (* a.d. segment_content counts how many cells are ALIVE, so cancelled is the inverse. *)
        (P ==∗ ∀ n, segment_content _ _ segment_spec γs n ==∗
         Ψ ∗ ∃ n', ⌜(n = S n')%nat⌝ ∧ segment_content _ _ segment_spec γs n') -∗
        <<< P >>>
          onSlotCleaned impl p @ ⊤ ∖ ↑N
        <<< Ψ, RET #() >>>;
      (* a.d. if we know a pointer to a segment, we can load it and get a segment *)
      pointer_location_load γ (ℓ: loc):
        ⊢ <<< ∀ id, ▷ pointer_location γ ℓ id >>>
          ! #ℓ @ ⊤
        <<< ∃ γs p, pointer_location γ ℓ id ∗ segment_in_list γ γs id p,
            RET p >>>;
      (* a.d. specialized invariant access lemma to get the number n of active cells.
      Either n is 0 (so the segment is cancelled) or it's >= 1, then known_is_removed must be false. *)
      access_segment N pars (known_is_removed: bool) E γ γs id ptr:
        ↑N ⊆ E ->
        is_concurrentLinkedList N pars γ -∗
        segment_in_list γ γs id ptr -∗
        (if known_is_removed then segment_is_cancelled γ id else True) -∗
        |={E, E ∖ ↑N}=> ∃ n, ⌜known_is_removed = false ∨ n = 0⌝ ∧
                            ▷ segment_content _ _ _ γs n ∗
                            (▷ segment_content _ _ _ γs n ={E ∖ ↑N, E}=∗ emp);
    }.

Check findSegment_spec.

Existing Instances is_concurrentLinkedList_persistent
         segment_in_list_persistent
         segment_is_cancelled_persistent.
