module

public import VerifiedGarbage.Proof.Dsa.X86_64.ParameterSearchInit
public import VerifiedGarbage.Proof.Dsa.X86_64.ParameterSearchInitScrub
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
public import VerifiedGarbage.Proof.Framework.QualifiedName

/-! # DSA (FIPS 186-4) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Dsa.X86_64

def direct : List Artifact := [
  Spec.Dsa.parameterInitApi.artifact X86_64.target Proof.Dsa.X86_64.ParameterSearchInit.initReg]

end VG.Artifacts.Dsa.X86_64

namespace VG.Artifacts.Dsa.X86_64

open VG.Proof.Dsa.X86_64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.DsaArithmetic.X86_64.variants.flatMap fun (v : Backend) => [
    Spec.Dsa.randomSignPrevalidatedApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.RandomSign.code (prevalidatedSignerName v)
        (Impl.Dsa.X86_64.PrevalidatedSign.sign v.sq v.mul)
      stack := v.stack + 256
      verified := random_sign_prevalidated_verified v
      spSafe := random_sign_sp v.prevalidatedSigner },
    Spec.Dsa.validatePrivateKeyApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.PrevalidatedSign.validate v.sq v.mul
      stack := v.stack
      verified := v.validatePrivateVerified
      spSafe := v.validatePrivateSp },
    Spec.Dsa.validatePublicKeyApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.Prevalidated.validate v.sq v.mul
      stack := v.stack
      verified := v.validateVerified
      spSafe := v.validateSp },
    Spec.Dsa.verifyPrevalidatedApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.Prevalidated.verify v.sq v.mul
      stack := v.stack
      verified := v.prevalidatedVerified
      spSafe := v.prevalidatedSp },
    Spec.Dsa.generateKeyApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.GenerateKey.code (keygenCheckName v) (keygenDeriveName v)
        (Impl.Dsa.X86_64.Generate.checkParameters v.sq v.mul) (Impl.Dsa.X86_64.Generate.deriveChecked v.sq v.mul)
      stack := v.stack + 256
      verified := keygen_verified v
      spSafe := keygen_sp v },
    Spec.Dsa.deriveKeyApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.Generate.deriveKey v.sq v.mul
      stack := v.stack
      verified := v.deriveVerified
      spSafe := v.deriveSp }]) ++
  (Generation.RefillBackend.hashPairs.flatMap fun (p : Generation.RefillBackend.Hashes) =>
    VG.Proof.Variants.MillerRabin.X86_64.variants.map fun (v : Proof.MillerRabin.X86_64.RoundImpl) =>
    Spec.Dsa.parameterSearchApi.artifact X86_64.target {
      suffix := qualifiedName "" [("sha1", p.sha1.suffix), ("sha256", p.sha256.suffix), ("mr", v.suffix)]
      stack := 632
      code := Generation.RefillBackend.searchCode p.sha1 p.sha256 v
      verified := Generation.RefillBackend.search_verified p.sha1 p.sha256 v p.h1 p.h256
      spSafe := Generation.RefillBackend.searchCode_spSafe p.sha1 p.sha256 v })

end VG.Artifacts.Dsa.X86_64
