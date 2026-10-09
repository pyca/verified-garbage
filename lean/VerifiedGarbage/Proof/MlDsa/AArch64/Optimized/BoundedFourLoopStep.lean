import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourLoopState

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorBody)

theorem vectorLoopStep_ok {σ s : State} {η done : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L : List Zq} {X : List Byte}
    (hY : Layout σ table p q X) (h : LoopInv σ η table p q L X done s)
    (hd : done+2≤X.length) (hL : (parsed η L X done).length≤252) :
    WP isa (.block (vectorBody true η)) s (LoopInv σ η table p q L X (done+2)) := by
  refine WP.mono (vectorBody_ok hη h.consts h.table
    (fun m hm=>by rw [h.keep.rd,h.keep.wr]; exact hY.tableRead m hm)
    (by rw [h.keep.rd,h.keep.wr,h.input]; exact hY.read done hd)
    hL (by omega) h.stored h.output h.remaining h.bytes
    (by rw [h.keep.wr]; exact hY.write _ hL)) fun t ht=>?_
  have hl : parsed η L X (done+2)=parsed η L X done++bodyValues η s := by
    rw [parsed_two hη hd hL,h.values hY hd]
  have hbytes : X.length-(done+2)=(X.length-done)-2:=by omega
  refine ⟨by omega,by have:=h.even; omega,
    h.consts.body ht.keep ht.vectors,
    h.table.frame ht.frame (fun r hr=>by rw [List.mem_singleton.mp hr]; exact hY.tableApart),
    (h.keep.trans ht.keep).mono ?_,h.frame.trans ht.frame,?_,?_,?_,?_,?_,?_⟩
  · intro r hr
    simpa only [List.mem_append,or_self] using hr
  · rw [hl]; exact ht.stored
  · rw [ht.input,h.input,BitVec.add_assoc,BitVec.ofNat_add]
    rfl
  · rw [hl]; exact ht.output
  · rw [hl]; exact ht.remaining
  · rw [hbytes]; exact ht.remainingBytes
  · rw [hl,hbytes]; exact ht.guard

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
