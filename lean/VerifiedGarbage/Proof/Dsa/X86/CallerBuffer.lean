module

public import VerifiedGarbage.Proof.Dsa.X86.StreamFrame
public import VerifiedGarbage.Proof.Dsa.X86.RunFrame
import VerifiedGarbage.Proof.Dsa.X86.RunBytes
import VerifiedGarbage.Proof.Framework.Offset

/-! # Caller-owned operands remain readable and unchanged throughout DSA -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

abbrev operandValue (s : State) (base : Addr) (p : Pointer) (len : Nat) : Nat :=
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s p).setWidth 64) len)

structure CallerBuffer (s : State) (base : Addr) (size : Nat) (p : Pointer) (len : Nat) : Prop where
  room : Pow.Room (s.gpr .esp) base size
  fits : (pointerValue base s p).toNat + len ≤ 2 ^ 32
  read : ∀ d k, d + k ≤ len → InRegions (s.rd ++ s.wr)
    ((pointerValue base s p).setWidth 64 + BitVec.ofNat 64 d) k
  apart : Region.Disjoint ⟨(pointerValue base s p).setWidth 64, len⟩ ⟨base, size⟩
  stack : Region.Disjoint ⟨(pointerValue base s p).setWidth 64, len⟩ (callStack (s.gpr .esp))

theorem CallerBuffer.ready {s : State} {base : Addr} {size n len : Nat} {p : Pointer}
    (B : CallerBuffer s base size p len) (hn : contextBytes n ≤ size) : OperandReady s base n p len := by
  refine ⟨⟨B.fits, fun d hd => B.read d 4 hd⟩, B.apart.sub_right ?_⟩
  intro x hx
  change (x - base).toNat + 1 ≤ contextBytes n at hx
  change (x - base).toNat + 1 ≤ size
  omega

theorem CallerBuffer.stream {s : State} {base : Addr} {size n len : Nat} {p : Pointer}
    (B : CallerBuffer s base size p len) (hn : contextBytes n ≤ size) :
    StreamInput s base (contextBytes n) (pointerValue base s p) len := by
  refine ⟨B.fits, fun i hi => B.read i 1 (by omega), ?_⟩
  intro i hi
  have ilt : i < 2 ^ 64 := by have := B.fits; omega
  have inside : (⟨(pointerValue base s p).setWidth 64, len⟩ : Region).Contains
      ((pointerValue base s p).setWidth 64 + BitVec.ofNat 64 i) 1 := Offset.contains_base _ (by omega) ilt
  have outside := B.apart _ inside
  change ¬ (ofs base ((pointerValue base s p).setWidth 64 + BitVec.ofNat 64 i) + 1 ≤ size) at outside
  omega

theorem CallerBuffer.keep {s t : State} {base : Addr} {size len : Nat} {p : Pointer} {rs : List Reg}
    (B : CallerBuffer s base size p len) (O : StackOuts base (s.gpr .esp) runRanges s.mem t.mem)
    (K : Keeps rs s t) (hdi : .edi ∉ rs) (hp : StablePointer p) (hsp : .esp ∉ rs := by decide) : CallerBuffer t base size p len := by
  have P := runFrame_pointer O K hdi hp
  exact ⟨by rw [K.1 _ hsp]; exact B.room, by rw [P]; exact B.fits, by rw [P, K.2.1, K.2.2]; exact B.read, by rw [P]; exact B.apart, by rw [P, K.1 _ hsp]; exact B.stack⟩

theorem CallerBuffer.value_keep {s t : State} {base : Addr} {size len : Nat} {p : Pointer} {rs : List Reg}
    (B : CallerBuffer s base size p len) (O : StackOuts base (s.gpr .esp) runRanges s.mem t.mem)
    (K : Keeps rs s t) (hdi : .edi ∉ rs) (hp : StablePointer p) (hz : usedBytes ≤ size) :
    operandValue t base p len = operandValue s base p len := by
  unfold operandValue
  rw [runFrame_pointer O K hdi hp, runFrame_bytes O hz (by have := B.fits; omega) B.apart B.stack]

theorem CallerBuffer.prefix {s : State} {base : Addr} {size len count : Nat} {p : Pointer}
    (B : CallerBuffer s base size p len) (hc : count ≤ len) : CallerBuffer s base size p count := by
  refine ⟨B.room, by have := B.fits; omega, fun d k hd => B.read d k (by omega), B.apart.sub_left ?_, B.stack.sub_left ?_⟩
  all_goals
    intro x hx
    change (x - (pointerValue base s p).setWidth 64).toNat + 1 ≤ count at hx
    change (x - (pointerValue base s p).setWidth 64).toNat + 1 ≤ len
    omega

end VG.Proof.Dsa.X86
