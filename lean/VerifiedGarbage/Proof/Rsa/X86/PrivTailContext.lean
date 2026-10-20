module

public import VerifiedGarbage.Proof.Rsa.X86.PrivTail
public import VerifiedGarbage.Proof.Rsa.X86.PrivContext
import VerifiedGarbage.Proof.Rsa.X86.PrivCrtCall
import VerifiedGarbage.Proof.Rsa.X86.PrivStackWord
import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-! # Retained caller arguments supply the final fault comparison and output release -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

theorem PrivContext.tailInput {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) : TailInput g.output g.temporary (g.sources 2) g.length s := by
  have R : ReleaseInput g.output g.temporary g.length s :=
    ⟨by have := h.valid.minLength; omega, by have := h.valid.maxLength; omega,
      h.readArg (by decide : 0 < 20), h.readArg (by decide : 3 < 20),
      h.argumentValue (by decide : 0 < 20), h.argumentValue (by decide : 3 < 20),
      by rw [h.sp]; rfl, h.valid.temporaryFit, h.valid.outputFit,
      h.temporaryWrite, h.outputWrite, by
        have sub : (⟨byteAddr g.temporary, g.length⟩ : Region).Sub g.innerRegion := by
          rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
          exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)
        exact h.valid.stackOutput.sub_left (fun x hx => h.valid.innerSub x (sub x hx))⟩
  refine ⟨R, ?_, h.argumentValue (by decide : 6 < 20), h.valid.sourceFits 2, (h.sources 2).read⟩
  refine ⟨?_, ?_, h.readArg (by decide : 0 < 20), h.readArg (by decide : 6 < 20), h.readArg (by decide : 3 < 20)⟩
  · rw [h.address (by decide : crtStatusOffset < VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 80)]
    exact h.inner.read (by decide : crtStatusOffset + 4 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes)
  · rw [h.address (by decide : precomputeStatusOffset < VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 80)]
    exact h.inner.read (by decide : precomputeStatusOffset + 4 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes)

end VG.Proof.Rsa.X86.PrivChecked
