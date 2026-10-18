module

public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer

/-! # Validated modulus inputs shared by all DSA arithmetic stages -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure Moduli (base : Addr) (size pLen qLen p q : Nat) (s : State) : Prop where
  scr : Scr s base size
  extent : usedBytes ≤ size
  widths : Spec.Dsa.lengthsValid pLen qLen
  pBuffer : CallerBuffer s base size (.input .p) pLen
  qBuffer : CallerBuffer s base size (.input .q) qLen
  pValue : operandValue s base (.input .p) pLen = p
  qValue : operandValue s base (.input .q) qLen = q
  pLarge : 1 < p
  qLarge : 255 < q
  pOdd : p % 2 = 1
  qOdd : q % 2 = 1

theorem Moduli.room {base : Addr} {size pLen qLen p q : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) : Pow.Room (s.gpr .esp) base size := M.pBuffer.room

theorem Moduli.lengths {base : Addr} {size pLen qLen p q : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) :
    128 ≤ pLen ∧ pLen ≤ 384 ∧ 20 ≤ qLen ∧ qLen ≤ 32 ∧ qLen ≤ pLen := by
  have H := M.widths
  unfold Spec.Dsa.lengthsValid at H
  omega

/-- Every supported width is a whole number of 32-bit words. -/
theorem Moduli.aligned {base : Addr} {size pLen qLen p q : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) : pLen % 4 = 0 ∧ qLen % 4 = 0 := by
  have H := M.widths
  unfold Spec.Dsa.lengthsValid at H
  omega

theorem Moduli.saved {base : Addr} {size pLen qLen p q : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) : Layout.saved ≤ size := by
  have H := M.extent
  change 15712 ≤ size at H
  change 8256 ≤ size
  omega

theorem Moduli.context {base : Addr} {size pLen qLen p q n : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) (hn : n ≤ 48) : contextBytes n ≤ size :=
  Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn) (Nat.le_trans (by decide : 7048 ≤ usedBytes) M.extent)

theorem Moduli.pReady {base : Addr} {size pLen qLen p q : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) : OperandReady s base ((pLen + 7) / 8) (.input .p) pLen :=
  M.pBuffer.ready (M.context (by have := M.lengths; omega))

theorem Moduli.qReady {base : Addr} {size pLen qLen p q : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) : OperandReady s base ((qLen + 7) / 8) (.input .q) qLen :=
  M.qBuffer.ready (M.context (by have := M.lengths; omega))

theorem Moduli.valueBounds {base : Addr} {size pLen qLen p q : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) : p < 256 ^ pLen ∧ q < 256 ^ qLen := by
  have P := VG.Proof.Dsa.decodeBE_lt (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .p)).setWidth 64) pLen)
  have Q := VG.Proof.Dsa.decodeBE_lt (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) qLen)
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at P Q
  change operandValue s base (.input .p) pLen < 256 ^ pLen at P
  change operandValue s base (.input .q) qLen < 256 ^ qLen at Q
  rw [M.pValue] at P
  rw [M.qValue] at Q
  exact ⟨P, Q⟩

theorem Moduli.keep {base : Addr} {size pLen qLen p q : Nat} {s t : State} {rs : List Reg}
    (M : Moduli base size pLen qLen p q s) (O : StackOuts base (s.gpr .esp) runRanges s.mem t.mem)
    (K : Keeps rs s t) (hdi : .edi ∉ rs) (hsp : .esp ∉ rs) : Moduli base size pLen qLen p q t := by
  refine ⟨M.scr.of_keeps K hdi hsp, M.extent, M.widths,
    M.pBuffer.keep O K hdi (by decide) hsp, M.qBuffer.keep O K hdi (by decide) hsp,
    ?_, ?_, M.pLarge, M.qLarge, M.pOdd, M.qOdd⟩
  · rw [M.pBuffer.value_keep O K hdi (by decide) M.extent, M.pValue]
  · rw [M.qBuffer.value_keep O K hdi (by decide) M.extent, M.qValue]

end VG.Proof.Dsa.X86
