module
import VerifiedGarbage.Proof.Dsa.X86.CallerSlice
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Spec.Dsa.Generate
import VerifiedGarbage.Proof.Dsa.X86.PackedKeyBuffers

/-! # Packed p||q||g identifies the generation specification's domain -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem parameters_buffers {s : State} {base : Addr} {size full pLen qLen : Nat} {key : List Byte}
    (B : CallerBuffer s base size (.input .p) full)
    (hpl : 0 < pLen) (hql : 0 < qLen) (hlen : 2 * pLen + qLen ≤ full)
    (bytes : Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .p)).setWidth 64) full = key)
    (qptr : pointerValue base s (.input .q) = pointerValue base s (.input .p) + BitVec.ofNat 32 pLen)
    (gptr : pointerValue base s (.input .g) = pointerValue base s (.input .p) + BitVec.ofNat 32 (pLen + qLen)) :
    CallerBuffer s base size (.input .p) pLen ∧
    CallerBuffer s base size (.input .q) qLen ∧
    CallerBuffer s base size (.input .g) pLen ∧
    Spec.Dsa.paramsBytes pLen qLen key =
      ⟨operandValue s base (.input .p) pLen, operandValue s base (.input .q) qLen,
        operandValue s base (.input .g) pLen⟩ := by
  refine ⟨B.prefix (by omega), B.slice hql (by omega) qptr,
    B.slice hpl (by omega) gptr, ?_⟩
  have P := B.slice_bytes (dest := .input .p) (offset := 0) hpl (by omega) (by simp)
  have Q := B.slice_bytes hql (by omega) qptr
  have G := B.slice_bytes hpl (by omega) gptr
  rw [bytes, List.drop_zero] at P
  rw [bytes] at Q G
  simp only [Spec.Dsa.paramsBytes, Spec.Dsa.publicKeyBytes, operandValue, ← P, ← Q, ← G]

end VG.Proof.Dsa.X86
