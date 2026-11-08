module

public import VerifiedGarbage.Proof.Dsa.X86_64.ParameterSearchInit
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCode
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyVerified
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyCorrect
public import VerifiedGarbage.Proof.Variants.DsaArithmetic.X86_64
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillVerified
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64

/-! # DSA parameter search on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Dsa.X86_64

def direct : List Artifact := [
  Spec.Dsa.parameterInitApi.artifact X86_64.target {
    code := Impl.Dsa.X86_64.ParameterSearch.init
    verified := Proof.Dsa.X86_64.ParameterSearchInit.init_verified }]

end VG.Artifacts.Dsa.X86_64

-- DSA signing and verification for every x86-64 arithmetic backend
namespace VG.Artifacts.Dsa.X86_64.DsaArithmetic
open VG.Proof.Dsa.X86_64

def artifacts (v : Backend) : List Artifact := [
  Spec.Dsa.randomSignPrevalidatedApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.Dsa.X86_64.RandomSign.code (prevalidatedSignerName v)
      (Impl.Dsa.X86_64.PrevalidatedSign.sign v.sq v.mul)
    stack := v.stack + 256
    verified := random_sign_prevalidated_verified v
    spSafe := random_sign_sp v.prevalidatedSigner
    features := v.features },
  Spec.Dsa.validatePrivateKeyApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.Dsa.X86_64.PrevalidatedSign.validate v.sq v.mul
    stack := v.stack
    verified := v.validatePrivateVerified
    spSafe := v.validatePrivateSp
    features := v.features },
  Spec.Dsa.validatePublicKeyApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.Dsa.X86_64.Prevalidated.validate v.sq v.mul
    stack := v.stack
    verified := v.validateVerified
    spSafe := v.validateSp
    features := v.features },
  Spec.Dsa.verifyPrevalidatedApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.Dsa.X86_64.Prevalidated.verify v.sq v.mul
    stack := v.stack
    verified := v.prevalidatedVerified
    spSafe := v.prevalidatedSp
    features := v.features },
  Spec.Dsa.generateKeyApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.Dsa.X86_64.GenerateKey.code (keygenCheckName v) (keygenDeriveName v)
      (Impl.Dsa.X86_64.Generate.checkParameters v.sq v.mul) (Impl.Dsa.X86_64.Generate.deriveChecked v.sq v.mul)
    stack := v.stack + 256
    verified := keygen_verified v
    spSafe := keygen_sp v
    features := v.features },
  Spec.Dsa.deriveKeyApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.Dsa.X86_64.Generate.deriveKey v.sq v.mul
    stack := v.stack
    verified := v.deriveVerified
    spSafe := v.deriveSp
    features := v.features }]

end VG.Artifacts.Dsa.X86_64.DsaArithmetic

-- DSA parameter generation over refillable tapes with every SHA-1, SHA-256 and Miller–Rabin backend on x86-64
namespace VG.Artifacts.Dsa.X86_64.MdHashMdHashMillerRabin
open VG.Proof.Dsa.X86_64.Generation.RefillBackend VG.Proof.MillerRabin.X86_64

/-- DSA's parameter search for a SHA-1 and a SHA-256 backend for the same
CPUs (both baselines, both SHA extensions, or SHA-1's AVX and BMI code with
SHA-256's AVX2 code, BMI2 coming only with AVX2), with each Miller–Rabin
round: any other pair needs the features of one of these, which runs both
hashes with them. -/
def artifacts (v1 v256 : Proof.Pbkdf2.Md.X86_64.MdHash) (v : RoundImpl) : List Artifact :=
  if !(v1.suffix == v256.suffix || (v1.suffix == "_avx_bmi" && v256.suffix == "_avx2")) then [] else
  if h1 : v1.mgf.G.rust = "sha1" then
    if h256 : v256.mgf.G.rust = "sha256" then
      let hashes := v1.features ++ v256.features.filter (!v1.features.contains ·)
      [Spec.Dsa.parameterSearchApi.artifact X86_64.target {
        suffix := Emit.qualifiedName "" [("sha1", v1.suffix), ("sha256", v256.suffix), ("mr", v.suffix)]
        stack := 632
        code := searchCode v1 v256 v
        verified := search_verified v1 v256 v h1 h256
        spSafe := searchCode_spSafe v1 v256 v
        features := hashes ++ v.features.filter (!hashes.contains ·) }]
    else []
  else []

end VG.Artifacts.Dsa.X86_64.MdHashMdHashMillerRabin

namespace VG.Artifacts.Dsa.X86_64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.DsaArithmetic.X86_64.variants.flatMap fun v => DsaArithmetic.artifacts v) ++
  (VG.Proof.Variants.MdHash.X86_64.variants.flatMap fun v => VG.Proof.Variants.MdHash.X86_64.variants.flatMap fun v2 => VG.Proof.Variants.MillerRabin.X86_64.variants.flatMap fun v3 => MdHashMdHashMillerRabin.artifacts v v2 v3)

end VG.Artifacts.Dsa.X86_64
