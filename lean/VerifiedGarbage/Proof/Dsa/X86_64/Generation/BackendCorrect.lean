module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Verified

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashVariants
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundCode
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashCode
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateDepth
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryDepth
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySafety
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Correct
import Mathlib.Data.Nat.Basic

/-! # Functional correctness for the existing hash and primality backends -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Pbkdf2.Md.X86_64 VG.Proof.MillerRabin.X86_64


variable {checkName : String}

theorem backend_safe (v1 v256 : MdHash) (v : RoundImpl) :
    generationSafe (Impl.Dsa.X86_64.Generation.code (checkName := checkName) v1.H.stream v256.H.stream
      v.inlineMont.toS.mm v.inlineMont.mm (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v).run) :=
  entry_safe (checkName := checkName) (hashCode_safe v1) (hashCode_safe v256) _ _ _
    (v.inlineSafe _ _ _) v.inlineSafe fun bits => (ProbablePrime.testCode_safe v bits).call _

theorem backend_depth (v1 v256 : MdHash) (v : RoundImpl) :
    (Impl.Dsa.X86_64.Generation.code (checkName := checkName) v1.H.stream v256.H.stream
      v.inlineMont.toS.mm v.inlineMont.mm (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v).run).x86_64Depth ≤ 536 :=
  entry_depth (checkName := checkName) (hashCode_depth v1) (hashCode_depth v256) _ _ _
    (inlineMul_depth v _ _ _) (inlineMul_depth v) (fun bits => by
      have := (ProbablePrime.primeTest v).depth bits
      have : ProbablePrime.stack = 184 := rfl
      change ((ProbablePrime.primeTest v).code bits).x86_64Depth + 8 ≤ 192
      omega) (by
      have h := checkParameters_depth_bound v.inlineMont.toS.mm v.inlineMont.mm
        (n := 0) (by rw [VG.Proof.Bignum.X86_64.Mont.toS, v.inlineDepth])
        (fun o a b => by rw [v.inlineDepth])
      change (VG.Impl.Dsa.X86_64.Generate.checkParameters _ _).x86_64Depth + 8 ≤ 128
      omega)

theorem backend_correct (v1 v256 : MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256")
    (s : State) (pre : (Spec.Dsa.generateParametersContract abi 536).pre s) :
    ∃ trace t, Exec isa (Impl.Dsa.X86_64.Generation.code (checkName := checkName) v1.H.stream v256.H.stream
      v.inlineMont.toS.mm v.inlineMont.mm (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v).run) s trace t ∧
      abiPreserved s t ∧ (Spec.Dsa.generateParametersContract abi 536).post s t :=
  generation_correct (checkName := checkName) (generationHashes v1 v256 h1 h256) v.inlineMont v.inlineMont.toS (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v)
    (backend_safe (checkName := checkName) v1 v256 v).sp (backend_depth (checkName := checkName) v1 v256 v) (backend_safe (checkName := checkName) v1 v256 v).mx s pre

end VG.Proof.Dsa.X86_64.Generation
