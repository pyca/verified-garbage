module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceSlice
import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices

/-! # Read exactly the complete seed chunk selected by the native tape loop -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.Generation.Layout

theorem source_octets {s : State} {B ptr : Addr} {Z : Nat} {bs : List Byte}
    (h : Src s B Z ptr bs) : Spec.Rsa.bytesAt s.mem ptr bs.length = bs := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i _ hi
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  exact h.val i hi

theorem GenerationTapeMemory.slice {p : GenerationGeometry} {tape : GenerationTape p} {s : State}
    (h : GenerationTapeMemory tape s) {used len : Nat} (room : used + len ≤ tape.bytes.length) :
    GenerationTapeMemory (tape.slice used len room) s := by
  have hl : ((tape.bytes.drop used).take len).length = len := by
    simp only [List.length_take, List.length_drop]; omega
  refine ⟨?_, ?_⟩
  · apply Covers.trans (rs' := [⟨tape.ptr, tape.bytes.length⟩]) ?_ h.cover
    apply Covers.of_sub
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact ⟨⟨tape.ptr, tape.bytes.length⟩, by simp, used, rfl, by
      change used + ((tape.bytes.drop used).take len).length ≤ tape.bytes.length
      rw [hl]; exact room⟩
  · exact source_octets (source_slice (h.source (d := 0) (n := usedBytes p.pLen) (by omega)) room)

end VG.Proof.Dsa.AArch64.Generation
