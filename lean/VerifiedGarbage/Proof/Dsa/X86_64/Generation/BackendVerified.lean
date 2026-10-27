module
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Verified
import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Spec.Dsa.Generate

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BackendCorrect
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ConstantTime
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Satisfiable
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashVariants

/-! # Complete verification of parameter generation with existing hash and primality backends -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Pbkdf2.Md.X86_64 VG.Proof.MillerRabin.X86_64


variable {checkName : String}

theorem backend_constantTime (v1 v256 : MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256") :
    ConstantTime isa (Spec.Dsa.generateParametersContract abi 536).pre
      (Spec.Dsa.generateParametersContract abi 536).pub
      (Impl.Dsa.X86_64.Generation.code (checkName := checkName) v1.H.stream v256.H.stream v.inlineMont.toS.mm v.inlineMont.mm (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v).run) :=
  generation_constantTime (checkName := checkName) (generationHashes v1 v256 h1 h256) v.inlineMont v.inlineMont.toS (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v)

theorem backend_verified (v1 v256 : MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256") :
    Verified target
      (Impl.Dsa.X86_64.Generation.code (checkName := checkName) v1.H.stream v256.H.stream v.inlineMont.toS.mm v.inlineMont.mm (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v).run)
      (Spec.Dsa.generateParametersContract abi 536) :=
  ⟨backend_correct (checkName := checkName) v1 v256 v h1 h256, backend_constantTime (checkName := checkName) v1 v256 v h1 h256, generation_satisfiable⟩

end VG.Proof.Dsa.X86_64.Generation
