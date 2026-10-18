module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashVariants
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundCode

/-! # Functional correctness for the existing hash and primality backends -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Pbkdf2.Md.X86_64 VG.Proof.MillerRabin.X86_64

theorem backend_safe (v1 v256 : MdHash) (v : RoundImpl) :
    generationSafe (Impl.Dsa.X86_64.Generation.code v1.H.stream v256.H.stream
      v.mont.toS.mm v.mont.mm (Kernel.called v).run) :=
  entry_safe (hashCode_safe v1) (hashCode_safe v256) _ _ _
    (v.arithSafe _ _ _) v.arithSafe (roundCode_safe v)

theorem backend_depth (v1 v256 : MdHash) (v : RoundImpl) :
    (Impl.Dsa.X86_64.Generation.code v1.H.stream v256.H.stream
      v.mont.toS.mm v.mont.mm (Kernel.called v).run).x86_64Depth ≤ 472 :=
  entry_depth (hashCode_depth v1) (hashCode_depth v256) _ _ _
    (roundMul_depth v _ _ _) (roundMul_depth v) (roundCode_depth v)

theorem backend_correct (v1 v256 : MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256")
    (s : State) (pre : (Spec.Dsa.generateParametersContract abi 472).pre s) :
    ∃ trace t, Exec isa (Impl.Dsa.X86_64.Generation.code v1.H.stream v256.H.stream
      v.mont.toS.mm v.mont.mm (Kernel.called v).run) s trace t ∧
      abiPreserved s t ∧ (Spec.Dsa.generateParametersContract abi 472).post s t :=
  generation_correct (generationHashes v1 v256 h1 h256) v.mont v.mont.toS (Kernel.called v)
    (backend_safe v1 v256 v).sp (backend_depth v1 v256 v) (backend_safe v1 v256 v).mx s pre

end VG.Proof.Dsa.X86_64.Generation
