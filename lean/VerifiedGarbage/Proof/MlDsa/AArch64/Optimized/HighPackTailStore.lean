import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

/-- The eight-byte store used by both packing widths. -/
theorem storeEight_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hw : InRegions s.wr (s.gpr .x1) 8)
    (k : ∀ t, Keep [.x9] s t → t.v = s.v →
      t.mem = s.mem.writeW (s.gpr .x1) ((s.v .v4).extractLsb' 0 64) →
      WP isa (.block rest) t Q) :
    WP isa (.block (([.umov .x .x9 .v4 0, .str .x .x9 .x1 0] : List Instr) ++ rest)) s Q := by
  let u := s.write .x .x9 ((s.v .v4).extractLsb' 0 64)
  let t := { u with mem := s.mem.writeW (s.gpr .x1) ((s.v .v4).extractLsb' 0 64) }
  refine WP.cons (s' := u) (by rfl) (WP.cons (s' := t) ?_ ?_)
  · simp [u, t, exec, addr, State.store, State.read, State.write, Size.bytes, Mem.writeW, hw]
  · apply k t
    · exact ⟨fun r hr => by simpa only [List.mem_singleton] using (only_write s .x .x9 _).gpr r hr,
        rfl, rfl, rfl, fun _ _ => rfl⟩
    · rfl
    · rfl

/-- Width six appends exactly the next four bytes; no bytes beyond the 12-byte block are written. -/
theorem storeFour_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hw : InRegions s.wr (s.gpr .x1 + 8) 4)
    (k : ∀ t, Keep [.x9] s t → t.v = s.v →
      t.mem = s.mem.writeW (s.gpr .x1 + 8) ((s.v .v4).extractLsb' 64 32) →
      WP isa (.block rest) t Q) :
    WP isa (.block (([.umov .w .x9 .v4 2, .str .w .x9 .x1 8] : List Instr) ++ rest)) s Q := by
  let u := s.write .w .x9 ((s.v .v4).extractLsb' 64 32)
  let t := { u with mem := s.mem.writeW (s.gpr .x1 + 8) ((s.v .v4).extractLsb' 64 32) }
  refine WP.cons (s' := u) (by rfl) (WP.cons (s' := t) ?_ ?_)
  · have hn (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    simp [u, t, exec, addr, State.store, State.read, State.write, Size.bytes, hn, Mem.writeW]
    exact hw
  · apply k t
    · exact ⟨fun r hr => by simpa only [List.mem_singleton] using (only_write s .w .x9 _).gpr r hr,
        rfl, rfl, rfl, fun _ _ => rfl⟩
    · rfl
    · rfl

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
