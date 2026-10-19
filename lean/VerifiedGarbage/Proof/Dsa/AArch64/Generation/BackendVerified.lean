module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashVariants
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Correct
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ConstantTime
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Satisfiable
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend

/-! Complete verification for the existing hash and shared primality backends. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Pbkdf2.Md.AArch64 VG.Proof.MillerRabin.AArch64

theorem backend_verified (v1 v256 : MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256") :
    Verified target (Impl.Dsa.AArch64.Generation.code v1.H v256.H v.mont.mm v.kernel.run)
      (Spec.Dsa.generateParametersContract abi 464) :=
  ⟨generation_correct (generationHashes v1 v256 h1 h256) v.mont v.kernel,
    generation_ct (generationHashes v1 v256 h1 h256) v.mont v.kernel, generation_satisfiable⟩

end VG.Proof.Dsa.AArch64.Generation
