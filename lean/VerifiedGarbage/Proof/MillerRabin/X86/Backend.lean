module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.ScrubSide
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Impl.Mont.X86.Sse2
import VerifiedGarbage.Proof.Mont.X86.Sse2.Shape
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! ### `MillerRabin.X86.MontInstance`, which the modules that import this one used -/

section

/-! ### `MillerRabin.X86.Baseline`, which the modules that import this one used -/

section

/-! # Baseline i686 round stack bounds and disciplined stack-pointer use -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86
open VG.Impl.MillerRabin.X86

abbrev montName : String := "vg_rsa_mont_mul"
abbrev montCode : Prog isa := VG.Impl.Mont.X86.Sse2.preparedBody

theorem body_noSp : NoSp (body montName montCode) := .of_all (by decide +kernel)
theorem body_stack : stackUse (body montName montCode) ≤ 80 := by decide +kernel

theorem code_noSp : NoSp (code montName montCode) := .of_all (by decide +kernel)
theorem code_stack : stackUse (code montName montCode) ≤ 96 := by decide +kernel

end VG.Proof.MillerRabin.X86

end

end

/-! # The emitted prepared multiplier fits the round's nested call budget -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86

theorem compact_noSp : NoSp VG.Impl.Mont.X86.Sse2.preparedBody := VG.Proof.Mont.X86.Sse2.preparedBody_NoSp

theorem compact_stack : stackUse VG.Impl.Mont.X86.Sse2.preparedBody ≤ 56 := by
  rw [VG.Proof.Mont.X86.Sse2.preparedBody_stack]

end VG.Proof.MillerRabin.X86

end

end

/-! # Prepared i686 Miller–Rabin implementations for generic callers -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86

structure RoundImpl where
  code : Prog isa
  verified : Verified target code (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96)
  noSp : NoSp code
  spSafe : code.allInstrs (fun i => !isa.writesSp i) = true
  stack : stackUse code ≤ 96
  /-- Its code, and the code it calls, has no MMX instruction and makes no indirect call (`calleeOk`):
  what the cleanup of every function that calls it needs of it, with its
  stack (`X86.Scrub.calleeSide`), so that each proves only its own code,
  whatever the implementation (`Proof/Framework/X86/ScrubCall.lean`). -/
  scrub : calleeOk code = true
  suffix : String
  features : List String

def RoundImpl.name (v : RoundImpl) : String :=
  "vg_miller_rabin_round" ++ v.suffix

end VG.Proof.MillerRabin.X86
