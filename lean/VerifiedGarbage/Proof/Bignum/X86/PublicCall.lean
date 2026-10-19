module

public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn

/-! # Stable cdecl arguments while RSA uses its disjoint scratch buffer -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (StackArgument stackValue)

structure CallArgument (s : State) (base : Addr) (bytes i : Nat) (v : BitVec 32) : Prop where
  stack : StackArgument s base bytes i
  value : stackValue s i = v

theorem CallArgument.readSrc {s : State} {base : Addr} {bytes i : Nat} {v : BitVec 32}
    (h : CallArgument s base bytes i v) :
    readSrc s (.mem (PublicFn.argument i)) = some v := by
  have H := h.stack.readSrc
  rw [h.value] at H
  exact H

theorem CallArgument.keep {s t : State} {base : Addr} {bytes i : Nat} {v : BitVec 32}
    (h : CallArgument s base bytes i v) {regs : List Reg} (K : Keeps regs s t)
    (sp : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem) :
    CallArgument t base bytes i v :=
  ⟨h.stack.keep K sp, (h.stack.value_keep K sp O).trans h.value⟩

/-- All ten public-primitive arguments remain available throughout scratch work. -/
def CallArguments (s : State) (base : Addr) (bytes : Nat) (args : Nat → BitVec 32) : Prop :=
  ∀ i, i < 10 → CallArgument s base bytes i (args i)

theorem CallArguments.keep {s t : State} {base : Addr} {bytes : Nat} {args : Nat → BitVec 32}
    (h : CallArguments s base bytes args) {regs : List Reg} (K : Keeps regs s t)
    (sp : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem) : CallArguments t base bytes args :=
  fun i hi => (h i hi).keep K sp O

end VG.Proof.Bignum.X86
