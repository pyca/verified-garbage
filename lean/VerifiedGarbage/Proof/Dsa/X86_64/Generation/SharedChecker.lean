module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64.Base
import VerifiedGarbage.Proof.Dsa.X86_64.ParametersVerified
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateSafety
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Impl.Dsa.X86_64.Generate
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
public import VerifiedGarbage.Proof.Dsa.X86_64.ParametersCT
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract

/-! # The domain checker parameter generation calls

Generation's own arithmetic (the generator search and this check) is a few
public exponentiations, against the many Miller–Rabin rounds its
probable-prime calls run: it multiplies with the baseline round's inlined
Montgomery multiplication on every backend, so one checker serves them all. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation.SharedChecker
open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

/-- The Montgomery multiplication generation's own arithmetic uses. -/
abbrev arith : RoundImpl := Proof.Variants.MillerRabin.X86_64.Base.variant

def name : String := "vg_dsa_generation_check_parameters"

def code : Prog isa :=
  Impl.Dsa.X86_64.Generate.checkParameters arith.inlineMont.toS.mm arith.inlineMont.mm

theorem safe : generationSafe code :=
  checkParameters_safe _ _ (arith.inlineSafe _ _ _) arith.inlineSafe

theorem verified : Verified target code (Proof.Dsa.checkParametersContract abi) :=
  parameters_verified _ _ (by
    rw [Code.allInstrs_eq]
    apply List.all_eq_true.mpr
    intro i hi
    have h := safe
    rw [generationSafe, Code.allInstrs_eq] at h
    have h := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)
    exact h.1)

end VG.Proof.Dsa.X86_64.Generation.SharedChecker
