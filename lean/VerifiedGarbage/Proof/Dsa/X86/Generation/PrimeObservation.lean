module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimalityResult

/-! The common caller-visible primality result, with a complete workspace frame. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

structure PrimeObservation (s₀ : State) (base : Addr) (bytes : Nat)
    (result : Option (Bool × List Byte)) (r : List Byte) (ptr : BitVec 32) (s : State) : Prop where
  tape : WitnessTape base bytes (s₀.gpr .esp) ptr r s
  cursor : s.mem.readW (off base VG.Impl.Dsa.X86.Generation.witnessCursor) 32 = ptr
  remaining : s.mem.readW (off base VG.Impl.Dsa.X86.Generation.witnessRemaining) 32 = BitVec.ofNat 32 r.length
  answer : match result with
    | none => s.gpr .eax = 0#32
    | some (b, rest) => r = rest ∧ s.gpr .eax = BitVec.ofNat 32 (if b then 1 else 3)
  frame : Frame [⟨base, bytes⟩, below (s₀.gpr .esp) 1184] s₀.mem s.mem
  regs : Keeps loopRegs s₀ s

theorem PrimalityResult.observation {s₀ s : State} {base : Addr} {bytes len : Nat}
    {result : Option (Bool × List Byte)} {r : List Byte} {ptr : BitVec 32}
    (R : PrimalityResult s₀ base bytes len result r ptr s) (capacity : 40960 ≤ bytes) (length : len ≤ 384) :
    PrimeObservation s₀ base bytes result r ptr s :=
  ⟨R.tape, R.cursor, R.remaining, R.answer, sample_round_enclose R.frame capacity length, R.regs⟩

theorem PrimeObservation.prefix {s₀ s t : State} {base : Addr} {bytes : Nat}
    {result : Option (Bool × List Byte)} {r : List Byte} {ptr : BitVec 32}
    (R : PrimeObservation s base bytes result r ptr t)
    (F : Frame [⟨base, bytes⟩, below (s₀.gpr .esp) 1184] s₀.mem s.mem) (K : Keeps loopRegs s₀ s) :
    PrimeObservation s₀ base bytes result r ptr t := by
  have tape := R.tape
  have frame := R.frame
  rw [K.1 .esp (by decide)] at tape frame
  exact ⟨tape, R.cursor, R.remaining, R.answer, F.trans frame, K.trans R.regs⟩

end VG.Proof.Dsa.X86.Generation
