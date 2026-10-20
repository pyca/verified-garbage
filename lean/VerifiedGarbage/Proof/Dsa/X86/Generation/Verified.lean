module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import VerifiedGarbage.Proof.Dsa.X86.Generation.ConstantTime
import VerifiedGarbage.Proof.Dsa.X86.Generation.Correct
import VerifiedGarbage.Proof.Dsa.X86.Generation.Satisfiable

/-! # Complete verification of x86 DSA parameter generation -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation

theorem verified (H : GenerationHashes) (F : KeyRandom.CheckCall.CheckFn) :
    Verified target (code H.sha1 H.sha256 F.name F.code) (Spec.Dsa.generateParametersContract abi 292) :=
  ⟨generateParameters_correct H F, generation_constantTime H F, generation_satisfiable⟩
end VG.Proof.Dsa.X86.Generation
