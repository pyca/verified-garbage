module

public import VerifiedGarbage.Proof.Sha256.X86.Scrub
public import VerifiedGarbage.Impl.Sha256.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
public import VerifiedGarbage.Proof.Variants.Sha1.X86

/-! # SHA-256 (FIPS 180-4) on x86 -/

@[expose] public section

namespace VG.Artifacts.Sha256.X86.Digest

def artifactsFor (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  Spec.Sha256.digest256Api.artifact X86.target {
    suffix := v.suffix
    code := Impl.Sha256.X86.Fn.digest (Proof.Pbkdf2.Stream.X86.sha256H v.stream)
    verified := Proof.Sha256.X86.Scrub.digest_scrubbed v
    spSafe := Proof.Sha256.X86.Scrub.digest_spSafe v }]

def artifacts : List Artifact :=
  VG.Proof.Variants.Sha256.X86.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Sha256.X86.Digest

-- SHA-224 (FIPS 180-4) on x86, for every x86 SHA-256 backend
namespace VG.Artifacts.Sha256.X86.Sha224Digest

def artifactsFor (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  Spec.Sha256.digest224Api.artifact X86.target {
    suffix := v.suffix
    code := Impl.Sha256.X86.Fn.digest (Proof.Pbkdf2.Stream.X86.sha224H v.stream)
    verified := Proof.Sha256.X86.Scrub.digest224_scrubbed v
    spSafe := Proof.Sha256.X86.Scrub.digest224_spSafe v }]

def artifacts : List Artifact :=
  VG.Proof.Variants.Sha256.X86.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Sha256.X86.Sha224Digest

namespace VG.Artifacts.Sha256.X86

def artifacts : List Artifact :=
  Digest.artifacts ++
  Sha224Digest.artifacts ++
  [
    Spec.Sha256.init224Api.artifact X86.target {
      code := Impl.Sha256.X86.Fn.init224
      verified := Proof.Sha256.X86.Scrub.init224_scrubbed },
    Spec.Sha256.initApi.artifact X86.target {
      code := Impl.Sha256.X86.Fn.init
      verified := Proof.Sha256.X86.Scrub.init_scrubbed }] ++
  (VG.Proof.Variants.Sha256.X86.variants.flatMap fun (v : Proof.Sha256.X86.Variants.Backend) => [
    Spec.Sha256.updateApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.Sha256.X86.Fn.update v.stream.upd
      verified := Proof.Sha256.X86.Variants.Backend.update_scrubbed v
      spSafe := Proof.Sha256.X86.Variants.Backend.update_spSafe v },
    Spec.Sha256.finalizeApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.Sha256.X86.Fn.finalize v.stream.fin
      verified := Proof.Sha256.X86.Variants.Backend.finalize_scrubbed v
      spSafe := Proof.Sha256.X86.Variants.Backend.finalize_spSafe v },
    Spec.Sha256.finalize224Api.artifact X86.target {
      suffix := v.suffix
      code := Impl.Sha256.X86.Fn.finalize224 v.cmpN v.cmpC
      verified := Proof.Sha256.X86.Variants.Backend.finalize224_scrubbed v
      spSafe := Proof.Sha256.X86.Variants.Backend.finalize224_spSafe v }])

end VG.Artifacts.Sha256.X86
