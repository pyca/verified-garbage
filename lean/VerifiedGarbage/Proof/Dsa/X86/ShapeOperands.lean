module

public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Dsa.X86.RunBytes
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Spill

/-! # Caller operands survive public shape checking -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def shapeRanges : List (Nat × Nat) := [(0, contextBytes 48), (Layout.field .digestPrefixLen, 8)]

def ShapePointer : Pointer → Prop
  | .input f => f ≠ .mask ∧ f ≠ .digestPrefixLen
  | .local _ => True
  | .signatureS => True

instance (p : Pointer) : Decidable (ShapePointer p) := by
  cases p <;> unfold ShapePointer <;> infer_instance

theorem shapeFrame_field {s t : State} {base : Addr} {f : Field}
    (O : Outs base shapeRanges s.mem t.mem) (hf : f ≠ .mask ∧ f ≠ .digestPrefixLen) :
    pointerValue base t (.input f) = pointerValue base s (.input f) := by
  have B := VG.Proof.Dsa.X86.Layout.field_bounds f
  have high : Layout.field f + 4 ≤ 8240 := by cases f <;> simp_all [Layout.field]
  have H : val32 t.mem base (Layout.field f) 1 = val32 s.mem base (Layout.field f) 1 := by
    apply O.val32
    · intro pair hp
      simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · change Layout.field f + 4 ≤ 0 ∨ 7048 ≤ Layout.field f; omega
      · change Layout.field f + 4 ≤ 8240 ∨ 8248 ≤ Layout.field f; omega
    · omega
  apply BitVec.eq_of_toNat_eq
  simpa only [val32, w32, pointerValue, Nat.mul_zero, Nat.add_zero] using H

theorem shapeFrame_pointer {s t : State} {base : Addr} {p : Pointer} {regs : List Reg}
    (O : Outs base shapeRanges s.mem t.mem) (K : Keeps regs s t) (hd : .edi ∉ regs) (hp : ShapePointer p) :
    pointerValue base t p = pointerValue base s p := by
  cases p with
  | input f => exact shapeFrame_field O hp
  | «local» offset => simp only [pointerValue, K.1 _ hd]
  | signatureS =>
    have S := shapeFrame_field (f := .signature) O (by decide)
    have Q := shapeFrame_field (f := .qLen) O (by decide)
    change pointerValue base t (.input .signature) + pointerValue base t (.input .qLen) = _
    rw [S, Q]; rfl

theorem CallerBuffer.keep_shape {s t : State} {base : Addr} {size len : Nat} {p : Pointer} {regs : List Reg}
    (B : CallerBuffer s base size p len) (O : Outs base shapeRanges s.mem t.mem)
    (K : Keeps regs s t) (hd : .edi ∉ regs) (hp : ShapePointer p) (hsp : .esp ∉ regs := by decide) : CallerBuffer t base size p len := by
  have P := shapeFrame_pointer O K hd hp
  exact ⟨by rw [K.1 _ hsp]; exact B.room, by rw [P]; exact B.fits,
    by rw [P, K.2.1, K.2.2]; exact B.read, by rw [P]; exact B.apart,
    by rw [P, K.1 _ hsp]; exact B.stack⟩

theorem CallerBuffer.value_keep_shape {s t : State} {base : Addr} {size len : Nat} {p : Pointer} {regs : List Reg}
    (B : CallerBuffer s base size p len) (O : Outs base shapeRanges s.mem t.mem)
    (K : Keeps regs s t) (hd : .edi ∉ regs) (hp : ShapePointer p) (hz : 8248 ≤ size) :
    operandValue t base p len = operandValue s base p len := by
  unfold operandValue
  rw [shapeFrame_pointer O K hd hp]
  congr 1
  apply outs_bytes O (by have := B.fits; omega)
  · intro pair hr
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  · intro pair hr
    apply B.apart.sub_right
    apply Offset.sub_base
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change 7048 ≤ size; omega
    · change 8248 ≤ size; omega

theorem CallerBuffer.bytes_keep_shape {s t : State} {base : Addr} {size len : Nat} {p : Pointer} {regs : List Reg}
    (B : CallerBuffer s base size p len) (O : Outs base shapeRanges s.mem t.mem)
    (K : Keeps regs s t) (hd : .edi ∉ regs) (hp : ShapePointer p) (hz : 8248 ≤ size) :
    Spec.Rsa.bytesAt t.mem ((pointerValue base t p).setWidth 64) len =
      Spec.Rsa.bytesAt s.mem ((pointerValue base s p).setWidth 64) len := by
  rw [shapeFrame_pointer O K hd hp]
  apply outs_bytes O (by have := B.fits; omega)
  · intro pair hr
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  · intro pair hr
    apply B.apart.sub_right
    apply Offset.sub_base
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change 7048 ≤ size; omega
    · change 8248 ≤ size; omega

end VG.Proof.Dsa.X86
