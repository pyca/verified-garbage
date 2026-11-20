module

public import VerifiedGarbage.Impl.Dsa.X86_64.Fn
public import VerifiedGarbage.Proof.Dsa.X86_64.BackendScrub
public import VerifiedGarbage.Proof.Dsa.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
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
  Spec.Dsa.parameterInitApi.artifact X86_64.target { code := Impl.Dsa.X86_64.Fn.parameterInit, verified := .scrubbed Proof.Dsa.X86_64.ParameterSearchInit.init_scrubbed, spSafe := Proof.Dsa.X86_64.ParameterSearchInit.init_spSafe }]

end VG.Artifacts.Dsa.X86_64

namespace VG.Artifacts.Dsa.X86_64

open VG.Proof.Dsa.X86_64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.DsaArithmetic.X86_64.variants.flatMap fun (v : Backend) => [
    Spec.Dsa.randomSignPrevalidatedApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.Fn.randomSignPrevalidated v.level (prevalidatedSignerName v) v.sq v.mul
      verified := .scrubbed (Proof.Dsa.X86_64.BackendScrub.randomSign_scrubbed v)
      spSafe := Proof.Dsa.X86_64.BackendScrub.randomSign_spSafe v },
    Spec.Dsa.validatePrivateKeyApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.Fn.validatePrivateKey v.level v.sq v.mul
      verified := .scrubbed (Proof.Dsa.X86_64.BackendScrub.validatePrivate_scrubbed v)
      spSafe := Proof.Dsa.X86_64.BackendScrub.validatePrivate_spSafe v },
    Spec.Dsa.validatePublicKeyApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.Fn.validatePublicKey v.level v.sq v.mul
      verified := .scrubbed (Proof.Dsa.X86_64.BackendScrub.validatePublic_scrubbed v)
      spSafe := Proof.Dsa.X86_64.BackendScrub.validatePublic_spSafe v },
    Spec.Dsa.verifyPrevalidatedApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.Fn.verifyPrevalidated v.level v.sq v.mul
      verified := .scrubbed (Proof.Dsa.X86_64.BackendScrub.verify_scrubbed v)
      spSafe := Proof.Dsa.X86_64.BackendScrub.verify_spSafe v },
    Spec.Dsa.generateKeyApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.Fn.generateKey v.level (keygenCheckName v) (keygenDeriveName v) v.sq v.mul
      verified := .scrubbed (Proof.Dsa.X86_64.BackendScrub.generateKey_scrubbed v)
      spSafe := Proof.Dsa.X86_64.BackendScrub.generateKey_spSafe v },
    Spec.Dsa.deriveKeyApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.Fn.deriveKey v.level v.sq v.mul
      verified := .scrubbed (Proof.Dsa.X86_64.BackendScrub.deriveKey_scrubbed v)
      spSafe := Proof.Dsa.X86_64.BackendScrub.deriveKey_spSafe v }]) ++
  (Generation.RefillBackend.hashPairs.flatMap fun (p : Generation.RefillBackend.Hashes) =>
    VG.Proof.Variants.MillerRabin.X86_64.variants.map fun (v : Proof.MillerRabin.X86_64.RoundImpl) =>
    Spec.Dsa.parameterSearchApi.artifact X86_64.target (X86_64.RScrub.withScrubAllM {
      suffix := qualifiedName "" [("sha1", p.sha1.suffix), ("sha256", p.sha256.suffix), ("mr", v.suffix)]
      code := Generation.RefillBackend.searchCode p.sha1 p.sha256 v
      verified := Generation.RefillBackend.search_verified p.sha1 p.sha256 v p.h1 p.h256
      spSafe := Generation.RefillBackend.searchCode_spSafe p.sha1 p.sha256 v }
      (Proof.Dsa.X86_64.Scrub.parameterSearchOut _)))

end VG.Artifacts.Dsa.X86_64
