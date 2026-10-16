module

public import VerifiedGarbage.Proof.Bignum.Arm.ExportBufferMasked
public import VerifiedGarbage.Proof.Bignum.Arm.MaskOutputCT
meta import VerifiedGarbage.Impl.Bignum.Arm.ExportBufferMasked
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Wide-result serialization keeps both the result and acceptance secret -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem exportBufferMasked_ct {src dst : BitVec 32} {n k : Nat} :
    RelCT isa (fun s t => (∃ accepted, ExportBufferInput src dst n k accepted s) ∧
      (∃ accepted, ExportBufferInput src dst n k accepted t) ∧ s.sp = t.sp)
      exportBufferMasked (fun _ _ => True) := by
  let P := fun s : State => ∃ accepted, ExportBufferInput src dst n k accepted s
  have exportCT : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) exportBuffer (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r1, .r4, .r6]) _ (by taint_decide)
    intro s t h
    obtain ⟨_, hs⟩ := h.1
    obtain ⟨_, ht⟩ := h.2.1
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.source.trans ht.source.symm
    · exact hs.output.trans ht.output.symm
    · exact hs.count.trans ht.count.symm
  have wp (s : State) (h : P s) : WP isa exportBuffer s (MaskOutputInput dst k) := by
    obtain ⟨_, h⟩ := h
    refine WP.mono (exportBuffer_ok s h) ?_
    rintro t ⟨_, _, rest⟩
    exact ⟨(rest.gpr .r4 (by simp)).trans h.output, (rest.gpr .r6 (by simp)).trans h.count,
      by rw [rest.sp]; exact h.stackFits, by rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead⟩
  have first := (relCT_keep_sp exportCT (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  exact first.seq (maskOutput_ct.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
