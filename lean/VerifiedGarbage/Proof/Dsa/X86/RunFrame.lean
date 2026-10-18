module

public import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame

/-! # Memory and pointer invariants across complete DSA arithmetic schedules -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

/-- Arithmetic scratch, the acceptance mask, and persistent intermediates. -/
def runRanges : List (Nat × Nat) :=
  [(0, contextBytes 48), (Layout.field .mask, 4), (r, usedBytes - r)]

def StablePointer : Pointer → Prop
  | .input f => f ≠ .mask
  | .local _ => True
  | .signatureS => True

instance (p : Pointer) : Decidable (StablePointer p) := by
  cases p <;> unfold StablePointer <;> infer_instance

theorem runFrame_field {s t : State} {base : Addr}
    (O : StackOuts base (s.gpr .esp) runRanges s.mem t.mem) {f : Field} (hf : f ≠ .mask) :
    t.mem.readW (off base (Layout.field f)) 32 = s.mem.readW (off base (Layout.field f)) 32 := by
  have lo := (VG.Proof.Dsa.X86.Layout.field_bounds f).1
  have hi : Layout.field f + 4 ≤ 8244 := by cases f <;> simp_all [Layout.field]
  apply BitVec.eq_of_toNat_eq
  have H : val32 t.mem base (Layout.field f) 1 = val32 s.mem base (Layout.field f) 1 := by
    apply O.val32
    · intro pair hp
      simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · change Layout.field f + 4 ≤ 0 ∨ 7048 ≤ Layout.field f
        omega
      · change Layout.field f + 4 ≤ 8244 ∨ 8248 ≤ Layout.field f
        omega
      · change Layout.field f + 4 ≤ 14720 ∨ 15712 ≤ Layout.field f
        omega
    · change _ ≤ 15712; omega
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

theorem runFrame_pointer {s t : State} {base : Addr} {rs : List Reg} {p : Pointer}
    (O : StackOuts base (s.gpr .esp) runRanges s.mem t.mem) (K : Keeps rs s t) (hdi : .edi ∉ rs) (hp : StablePointer p) :
    pointerValue base t p = pointerValue base s p := by
  cases p with
  | input f => exact runFrame_field O hp
  | «local» offset => simp only [pointerValue, K.1 _ hdi]
  | signatureS =>
    simp only [pointerValue, runFrame_field O (f := .signature) (by decide), runFrame_field O (f := .qLen) (by decide)]

theorem OperandReady.keep_pointer {s t : State} {base : Addr} {n len : Nat} {rs : List Reg} {p : Pointer}
    (R : OperandReady s base n p len) (K : Keeps rs s t) (P : pointerValue base t p = pointerValue base s p) :
    OperandReady t base n p len :=
  ⟨⟨by rw [P]; exact R.fits, by rw [P, K.2.1, K.2.2]; exact R.reads⟩, by rw [P]; exact R.apart⟩

theorem OperandReady.keep_run {s t : State} {base : Addr} {n len : Nat} {rs : List Reg} {p : Pointer}
    (R : OperandReady s base n p len) (O : StackOuts base (s.gpr .esp) runRanges s.mem t.mem)
    (K : Keeps rs s t) (hdi : .edi ∉ rs) (hp : StablePointer p) : OperandReady t base n p len :=
  R.keep_pointer K (runFrame_pointer O K hdi hp)

end VG.Proof.Dsa.X86
