module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.LoopState

/-! The caller observes the shared primality result and its exact unused tape suffix. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86

structure PrimalityResult (s₀ : State) (base : Addr) (bytes len : Nat)
    (result : Option (Bool × List Byte)) (r : List Byte) (ptr : BitVec 32) (s : State) : Prop where
  tape : WitnessTape base bytes (s₀.gpr .esp) ptr r s
  cursor : s.mem.readW (off base witnessCursor) 32 = ptr
  remaining : s.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 r.length
  answer : match result with
    | none => s.gpr .eax = 0#32
    | some (b, rest) => r = rest ∧ s.gpr .eax = BitVec.ofNat 32 (if b then 1 else 3)
  frame : SampleRoundFrame base (s₀.gpr .esp) len s₀ s
  regs : Keeps loopRegs s₀ s

theorem LoopResult.primality {s₀ s : State} {base : Addr} {bytes n len candidate : Nat}
    {result : Option (Bool × List Byte)} {r : List Byte} {ptr : BitVec 32}
    (R : LoopResult s₀ base bytes n len candidate result r ptr s) :
    PrimalityResult s₀ base bytes len result r ptr s :=
  ⟨R.tape, R.cursor, R.remaining, R.answer, R.frame, R.regs⟩

theorem PrimalityResult.prefix {s₀ s t : State} {base : Addr} {bytes len : Nat}
    {result : Option (Bool × List Byte)} {r : List Byte} {ptr : BitVec 32}
    (R : PrimalityResult s base bytes len result r ptr t)
    (F : SampleRoundFrame base (s₀.gpr .esp) len s₀ s) (K : Keeps loopRegs s₀ s) :
    PrimalityResult s₀ base bytes len result r ptr t := by
  have tape := R.tape
  have frame := R.frame
  rw [K.1 .esp (by decide)] at tape frame
  exact ⟨tape, R.cursor, R.remaining, R.answer, F.trans frame, K.trans R.regs⟩

end VG.Proof.Dsa.X86.Generation
