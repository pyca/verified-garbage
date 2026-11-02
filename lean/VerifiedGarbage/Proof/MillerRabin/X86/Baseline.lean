module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Impl.Mont.X86.Sse2
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! # Baseline i686 round stack bounds and disciplined stack-pointer use -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86
open VG.Impl.MillerRabin.X86

abbrev montName : String := "vg_rsa_mont_mul"
abbrev montCode : Prog isa := VG.Impl.Mont.X86.Sse2.preparedBody

theorem core_noSp : NoSp (core montName montCode) := .of_all (by decide +kernel)
theorem core_stack : stackUse (core montName montCode) ≤ 80 := by decide +kernel

theorem body_noSp : NoSp (body montName montCode) := .of_all (by decide +kernel)
theorem body_stack : stackUse (body montName montCode) ≤ 80 := by decide +kernel

theorem code_noSp : NoSp (code montName montCode) := .of_all (by decide +kernel)
theorem code_stack : stackUse (code montName montCode) ≤ 96 := by decide +kernel

end VG.Proof.MillerRabin.X86
