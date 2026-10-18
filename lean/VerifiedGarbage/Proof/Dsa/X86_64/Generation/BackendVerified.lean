module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BackendCorrect
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ConstantTime
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Satisfiable

/-! # Complete verification of parameter generation with existing hash and primality backends -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Pbkdf2.Md.X86_64 VG.Proof.MillerRabin.X86_64

theorem backend_constantTime (v1 v256 : MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256") :
    ConstantTime isa (Spec.Dsa.generateParametersContract abi 472).pre
      (Spec.Dsa.generateParametersContract abi 472).pub
      (Impl.Dsa.X86_64.Generation.code v1.H.stream v256.H.stream v.mont.toS.mm v.mont.mm (Kernel.called v).run) :=
  generation_constantTime (generationHashes v1 v256 h1 h256) v.mont v.mont.toS (Kernel.called v)

theorem backend_verified (v1 v256 : MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256") :
    Verified target
      (Impl.Dsa.X86_64.Generation.code v1.H.stream v256.H.stream v.mont.toS.mm v.mont.mm (Kernel.called v).run)
      (Spec.Dsa.generateParametersContract abi 472) :=
  ⟨backend_correct v1 v256 v h1 h256, backend_constantTime v1 v256 v h1 h256, generation_satisfiable⟩

end VG.Proof.Dsa.X86_64.Generation
