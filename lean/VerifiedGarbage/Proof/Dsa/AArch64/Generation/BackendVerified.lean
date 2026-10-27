module

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashVariants
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Correct
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ConstantTime
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Satisfiable
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Verified
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Verified
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Spec.Dsa.Generate

/-! Complete verification for the existing hash backends and the shared probable-prime tests. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Pbkdf2.Md.AArch64 VG.Proof.MillerRabin.AArch64

theorem backend_verified (v1 v256 : MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256") :
    Verified target (Impl.Dsa.AArch64.Generation.code v1.H v256.H (Generator.generatorStage v).run
      (ProbablePrime.primeTest v).run)
      (Spec.Dsa.generateParametersContract abi 736) :=
  ⟨generation_correct (generationHashes v1 v256 h1 h256) (Generator.generatorStage v) (ProbablePrime.primeTest v),
    generation_ct (generationHashes v1 v256 h1 h256) (Generator.generatorStage v) (ProbablePrime.primeTest v),
    generation_satisfiable⟩

end VG.Proof.Dsa.AArch64.Generation
