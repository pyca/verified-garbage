module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
import VerifiedGarbage.Proof.Dsa.X86_64.ParametersVerified
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateSafety
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Spec.Dsa.GenerationCheck
public import VerifiedGarbage.Impl.Dsa.X86_64.Generate
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
public import VerifiedGarbage.Proof.Dsa.X86_64.ParametersCT
public import VerifiedGarbage.Spec.Dsa.Derive

/-! # Register one shared domain checker per generation arithmetic backend -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation.SharedChecker
open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

def suffix (v : RoundImpl) : String :=
  Emit.qualifiedName "" [("mr", v.suffix)]

def name (v : RoundImpl) : String := Spec.Dsa.generationCheckApi.name ++ suffix v

def code (v : RoundImpl) : Prog isa :=
  Impl.Dsa.X86_64.Generate.checkParameters v.inlineMont.toS.mm v.inlineMont.mm

theorem safe (v : RoundImpl) : generationSafe (code v) :=
  checkParameters_safe _ _ (v.inlineSafe _ _ _) v.inlineSafe

theorem verified (v : RoundImpl) :
    Verified target (code v) (Spec.Dsa.checkParametersContract abi) :=
  parameters_verified _ _ (by
    rw [Code.allInstrs_eq]
    apply List.all_eq_true.mpr
    intro i hi
    have h := (safe v)
    rw [generationSafe, Code.allInstrs_eq] at h
    have h := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)
    exact h.1)

end VG.Proof.Dsa.X86_64.Generation.SharedChecker
