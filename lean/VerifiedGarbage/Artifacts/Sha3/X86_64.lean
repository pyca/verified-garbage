module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sha3.Instances
import VerifiedGarbage.Impl.Sha3.X86_64.Fn
import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
import VerifiedGarbage.Proof.Sha3.X86_64.Instances
import VerifiedGarbage.Proof.Sha3.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis


/-! # SHA-3 and SHAKE (FIPS 202) on x86-64 -/

namespace VG.Artifacts.Sha3.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Sha3.updateSha3_224Api.artifact X86_64.target { code := Impl.Sha3.X86_64.Fn.absorbSha3_224, verified := Proof.Sha3.X86_64.Scrub.absorbSha3_224_scrubbed, spSafe := Proof.Sha3.X86_64.Scrub.absorbSha3_224_spSafe },
  Spec.Sha3.finalizeSha3_224Api.artifact X86_64.target { code := Impl.Sha3.X86_64.Fn.finalizeSha3_224, verified := Proof.Sha3.X86_64.Scrub.finalizeSha3_224_scrubbed, spSafe := Proof.Sha3.X86_64.Scrub.finalizeSha3_224_spSafe },
  Spec.Sha3.updateSha3_256Api.artifact X86_64.target { code := Impl.Sha3.X86_64.Fn.absorbSha3_256, verified := Proof.Sha3.X86_64.Scrub.absorbSha3_256_scrubbed, spSafe := Proof.Sha3.X86_64.Scrub.absorbSha3_256_spSafe },
  Spec.Sha3.finalizeSha3_256Api.artifact X86_64.target { code := Impl.Sha3.X86_64.Fn.finalizeSha3_256, verified := Proof.Sha3.X86_64.Scrub.finalizeSha3_256_scrubbed, spSafe := Proof.Sha3.X86_64.Scrub.finalizeSha3_256_spSafe },
  Spec.Sha3.updateSha3_384Api.artifact X86_64.target { code := Impl.Sha3.X86_64.Fn.absorbSha3_384, verified := Proof.Sha3.X86_64.Scrub.absorbSha3_384_scrubbed, spSafe := Proof.Sha3.X86_64.Scrub.absorbSha3_384_spSafe },
  Spec.Sha3.finalizeSha3_384Api.artifact X86_64.target { code := Impl.Sha3.X86_64.Fn.finalizeSha3_384, verified := Proof.Sha3.X86_64.Scrub.finalizeSha3_384_scrubbed, spSafe := Proof.Sha3.X86_64.Scrub.finalizeSha3_384_spSafe },
  Spec.Sha3.updateSha3_512Api.artifact X86_64.target { code := Impl.Sha3.X86_64.Fn.absorbSha3_512, verified := Proof.Sha3.X86_64.Scrub.absorbSha3_512_scrubbed, spSafe := Proof.Sha3.X86_64.Scrub.absorbSha3_512_spSafe },
  Spec.Sha3.finalizeSha3_512Api.artifact X86_64.target { code := Impl.Sha3.X86_64.Fn.finalizeSha3_512, verified := Proof.Sha3.X86_64.Scrub.finalizeSha3_512_scrubbed, spSafe := Proof.Sha3.X86_64.Scrub.finalizeSha3_512_spSafe },
  Spec.Sha3.updateShake128Api.artifact X86_64.target { code := Impl.Sha3.X86_64.Fn.absorbShake128, verified := Proof.Sha3.X86_64.Scrub.absorbShake128_scrubbed, spSafe := Proof.Sha3.X86_64.Scrub.absorbShake128_spSafe },
  Spec.Sha3.finalizeShake128Api.artifact X86_64.target { code := Impl.Sha3.X86_64.Fn.finalizeShake128, verified := Proof.Sha3.X86_64.Scrub.finalizeShake128_scrubbed, spSafe := Proof.Sha3.X86_64.Scrub.finalizeShake128_spSafe },
  Spec.Sha3.squeezeShake128Api.artifact X86_64.target { code := Impl.Sha3.X86_64.Fn.squeezeShake128, verified := Proof.Sha3.X86_64.Scrub.squeezeShake128_scrubbed, spSafe := Proof.Sha3.X86_64.Scrub.squeezeShake128_spSafe },
  Spec.Sha3.finalizeShake256Api.artifact X86_64.target { code := Impl.Sha3.X86_64.Fn.finalizeShake256, verified := Proof.Sha3.X86_64.Scrub.finalizeShake256_scrubbed, spSafe := Proof.Sha3.X86_64.Scrub.finalizeShake256_spSafe },
  Spec.Sha3.squeezeShake256Api.artifact X86_64.target { code := Impl.Sha3.X86_64.Fn.squeezeShake256, verified := Proof.Sha3.X86_64.Scrub.squeezeShake256_scrubbed, spSafe := Proof.Sha3.X86_64.Scrub.squeezeShake256_spSafe }]

spec_apis artifacts

end VG.Artifacts.Sha3.X86_64
