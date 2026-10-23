module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.State
import VerifiedGarbage.Proof.Framework.Offset

/-! # The checker leaves the saved registers and consumption slots untouched -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom.CheckCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

/-- The frame above its argument words is apart from where the call writes. -/
theorem call_frame_byte {s₀ : State} (A : KeyABI s₀) {m m' : Mem} (hf : Frame (callWrites s₀) m m')
    {d : Nat} (h₁ : 44 ≤ d) (h₂ : d < 120) : m' (off (rBase s₀) d) = m (off (rBase s₀) d) := by
  rw [rBase_off, rLow_off]
  have hs : (rStack s₀).Contains (off (rCall s₀) (88 + (24 + d))) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  refine hf _ fun r hr => ?_
  simp only [callWrites, callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.stackScratchWide _ hs
  · rw [rLow_off]
    exact (Offset.disjoint (rCall s₀) (d := 88 + (24 + d)) (n := 1) (e := 88 + 24) (k := 24) (by omega)
      (by omega) (by omega)) _ (self_contains _)
  · exact (Offset.disjoint_base (rCall s₀) (d := 88 + (24 + d)) (n := 1) (k := 112) (by omega)
      (by omega)) _ (self_contains _)

theorem call_frame_slot {s₀ : State} (A : KeyABI s₀) {m m' : Mem} (hf : Frame (callWrites s₀) m m')
    {d : Nat} (h₁ : 44 ≤ d) (h₂ : d + 4 ≤ 120) : slot m' (rBase s₀) d = slot m (rBase s₀) d :=
  Mem.readW_congr fun i hi => by
    have : i < 4 := hi
    rw [show off (rBase s₀) d + BitVec.ofNat 64 i = off (rBase s₀) (d + i) by
      rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]]
    exact call_frame_byte A hf (by omega) (by omega)

end VG.Proof.Dsa.X86.KeyRandom.CheckCall
