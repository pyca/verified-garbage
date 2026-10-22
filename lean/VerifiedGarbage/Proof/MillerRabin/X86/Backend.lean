module

public import VerifiedGarbage.Proof.MillerRabin.X86.Verified
import VerifiedGarbage.Proof.Framework.CodeAll

/-! # Verified prepared-round implementations for generic i686 callers -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86

structure RoundImpl where
  code : Prog isa
  verified : Verified target code (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact stackBytes)
  stack : stackUse code ≤ stackBytes
  spSafe : code.all (fun i => !isa.writesSp i) = true
  suffix : String
  features : List String

def RoundImpl.name (v : RoundImpl) : String :=
  (Spec.MillerRabin.roundApi Spec.MillerRabin.compact).name ++ v.suffix

theorem RoundImpl.noSp (v : RoundImpl) : NoSp v.code := by
  intro i hi
  have safe : isa.writesSp i = false := by simpa using Code.all_instrs v.spSafe i hi
  cases i <;> simp_all [isa, Instr.dst, Taint.clobbers, Taint.dst]

end VG.Proof.MillerRabin.X86
