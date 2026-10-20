module
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Spec.Dsa.SignVerify

import VerifiedGarbage.Proof.Dsa.X86.CallerSlice
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.X86.Exec

/-! # Installed packed-key pointers identify the specification's components -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem CallerBuffer.slice_bytes {s : State} {base : Addr} {size full offset count : Nat} {source dest : Pointer}
    (B : CallerBuffer s base size source full) (hc : 0 < count) (hb : offset + count ≤ full)
    (hp : pointerValue base s dest = pointerValue base s source + BitVec.ofNat 32 offset) :
    Spec.Rsa.bytesAt s.mem ((pointerValue base s dest).setWidth 64) count =
      ((Spec.Rsa.bytesAt s.mem ((pointerValue base s source).setWidth 64) full).drop offset).take count := by
  rw [VG.Proof.Dsa.bytesAt_slice _ _ hb, hp]
  congr 1
  exact addr_eq (by have := B.fits; omega)

theorem publicKey_buffers {s : State} {base : Addr} {size full pLen qLen : Nat} {key : List Byte}
    (B : CallerBuffer s base size (.input .p) full)
    (hpl : 0 < pLen) (hql : 0 < qLen) (hlen : 3 * pLen + qLen ≤ full)
    (bytes : Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .p)).setWidth 64) full = key)
    (qptr : pointerValue base s (.input .q) = pointerValue base s (.input .p) + BitVec.ofNat 32 pLen)
    (gptr : pointerValue base s (.input .g) = pointerValue base s (.input .p) + BitVec.ofNat 32 (pLen + qLen))
    (yptr : pointerValue base s (.input .y) = pointerValue base s (.input .p) + BitVec.ofNat 32 (2 * pLen + qLen)) :
    CallerBuffer s base size (.input .p) pLen ∧
    CallerBuffer s base size (.input .q) qLen ∧
    CallerBuffer s base size (.input .g) pLen ∧
    CallerBuffer s base size (.input .y) pLen ∧
    Spec.Dsa.publicKeyBytes pLen qLen key =
      ⟨⟨operandValue s base (.input .p) pLen, operandValue s base (.input .q) qLen,
        operandValue s base (.input .g) pLen⟩, operandValue s base (.input .y) pLen, none⟩ := by
  refine ⟨B.prefix (by omega), B.slice hql (by omega) qptr,
    B.slice hpl (by omega) gptr, B.slice hpl (by omega) yptr, ?_⟩
  have P := B.slice_bytes (dest := .input .p) (offset := 0) hpl (by omega) (by simp)
  have Q := B.slice_bytes hql (by omega) qptr
  have G := B.slice_bytes hpl (by omega) gptr
  have Y := B.slice_bytes hpl (by omega) yptr
  rw [bytes, List.drop_zero] at P
  rw [bytes] at Q G Y
  simp only [Spec.Dsa.publicKeyBytes, operandValue, ← P, ← Q, ← G, ← Y]

theorem privateKey_buffers {s : State} {base : Addr} {size full pLen qLen : Nat} {key : List Byte}
    (B : CallerBuffer s base size (.input .p) full)
    (hpl : 0 < pLen) (hql : 0 < qLen) (hlen : 3 * pLen + 2 * qLen ≤ full)
    (bytes : Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .p)).setWidth 64) full = key)
    (qptr : pointerValue base s (.input .q) = pointerValue base s (.input .p) + BitVec.ofNat 32 pLen)
    (gptr : pointerValue base s (.input .g) = pointerValue base s (.input .p) + BitVec.ofNat 32 (pLen + qLen))
    (yptr : pointerValue base s (.input .y) = pointerValue base s (.input .p) + BitVec.ofNat 32 (2 * pLen + qLen))
    (xptr : pointerValue base s (.input .x) = pointerValue base s (.input .p) + BitVec.ofNat 32 (3 * pLen + qLen)) :
    CallerBuffer s base size (.input .p) pLen ∧
    CallerBuffer s base size (.input .q) qLen ∧
    CallerBuffer s base size (.input .g) pLen ∧
    CallerBuffer s base size (.input .y) pLen ∧
    CallerBuffer s base size (.input .x) qLen ∧
    Spec.Dsa.privateKeyBytes pLen qLen key =
      ⟨⟨operandValue s base (.input .p) pLen, operandValue s base (.input .q) qLen,
        operandValue s base (.input .g) pLen⟩, operandValue s base (.input .y) pLen,
        some (operandValue s base (.input .x) qLen)⟩ := by
  obtain ⟨P, Q, G, Y, Value⟩ := publicKey_buffers B hpl hql (by omega) bytes qptr gptr yptr
  refine ⟨P, Q, G, Y, B.slice hql (by omega) xptr, ?_⟩
  have X := B.slice_bytes hql (by omega) xptr
  rw [bytes] at X
  simp only [Spec.Dsa.privateKeyBytes, Value, operandValue, ← X]

end VG.Proof.Dsa.X86
