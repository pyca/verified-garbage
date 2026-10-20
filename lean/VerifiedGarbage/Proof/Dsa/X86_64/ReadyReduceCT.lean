module

public import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCallCT
public import VerifiedGarbage.Proof.Dsa.X86_64.CallReduceCT

/-! # Streaming reduction timing in the persistent workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure ReadyReducePublic (d : Nat) where
  layout : ExecutionLayout
  length : Nat
  greater : 255 < layout.subgroup
  odd : layout.subgroup % 2 = 1
  lengthBound : length < 2 ^ 64
  outputStart : activeBytes ≤ d
  outputEnd : d + layout.qLen ≤ usedBytes

def ReadyReducePublic.call {d : Nat} (p : ReadyReducePublic d) (a : Operand) : CallReducePublic where
  bytes := ⟨⟨p.layout.base, activeBytes, qWorkspace, outerWords, p.layout.qWords⟩,
    p.layout.pointer a.pointer, p.length⟩
  minv := p.layout.qInverse
  modulus := p.layout.subgroup
  lower := (ModulusSide.q.bounds p.layout).1
  fits := (ModulusSide.q.bounds p.layout).2.1
  upper := by change outerWords < 2 ^ 30; decide
  greater := by have := p.greater; omega
  odd := p.odd
  greater255 := p.greater
  lengthBound := p.lengthBound
  output := off p.layout.base d
  outputLen := p.layout.qLen
  parentInverse := 0
  extent := by change pWorkspace ≤ activeBytes; decide
  childLow := (ModulusSide.q.bounds p.layout).2.2.1
  childHigh := (ModulusSide.q.bounds p.layout).2.2.2.2.1
  offset := rfl
  width48 := (ModulusSide.q.bounds p.layout).2.1
  outputPositive := (ModulusSide.q.bounds p.layout).2.2.2.2.2.1
  outputBound := (ModulusSide.q.bounds p.layout).2.2.2.2.2.2
  outputWidth := rfl

def ReadyReducePre (d : Nat) (a : Operand) (p : ReadyReducePublic d) (s : State) : Prop :=
  Ready p.layout s ∧ ∃ ba : List Byte, OperandBytes s p.layout.base activeBytes a ba ∧ ba.length = p.length

theorem readyReduce_ct (M : Mont) (d : Nat) (a : Operand)
    (ha : pointerFits a.pointer) (hpa : stablePointer a.pointer) (hd : d < 2 ^ 31)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (reduceHead a (Core.scalar d))) hc).isSome = true) :
    RelCT isa (Two (ReadyReducePre d a)) (Core.reduce M.mm a (Core.scalar d)) (fun _ _ => True) := by
  refine two_map (fun p : ReadyReducePublic d => p.call a) ?_ (coreReduce_ct M ha hd hT)
  intro p s ⟨hr, ba, has, hbl⟩
  exact ⟨hr.parent, hr.qChild, ⟨ba, has, hbl⟩, hr.publicPointer a.pointer hpa, rfl,
    hr.length .q, hr.local_write p.outputEnd, hr.local_out p.outputStart p.outputEnd⟩

end VG.Proof.Dsa.X86_64
