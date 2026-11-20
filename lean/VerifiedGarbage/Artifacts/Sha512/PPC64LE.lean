module

public import VerifiedGarbage.Proof.Sha512.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Stream.Init
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha384
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_224
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_256
import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Shared
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sha512.PPC64LE

def artifacts : List Artifact := [
  Spec.Sha512.init384Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_384
    verified := .scrubbed ⟨Proof.Sha512.PPC64LE.Shared.init Spec.Sha512.H0_384,
      Proof.Sha512.PPC64LE.Stream.init_noResidue _ _ _⟩ },
  Spec.Sha512.init512Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_512
    verified := .scrubbed ⟨Proof.Sha512.PPC64LE.Shared.init Spec.Sha512.H0_512,
      Proof.Sha512.PPC64LE.Stream.init_noResidue _ _ _⟩ },
  Spec.Sha512.init512_224Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_512_224
    verified := .scrubbed ⟨Proof.Sha512.PPC64LE.Shared.init Spec.Sha512.H0_512_224,
      Proof.Sha512.PPC64LE.Stream.init_noResidue _ _ _⟩ },
  Spec.Sha512.init512_256Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_512_256
    verified := .scrubbed ⟨Proof.Sha512.PPC64LE.Shared.init Spec.Sha512.H0_512_256,
      Proof.Sha512.PPC64LE.Stream.init_noResidue _ _ _⟩ },
  Spec.Sha512.updateApi.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Fn.update
    verified := .scrubbed Proof.Sha512.PPC64LE.update_scrubbed },
  Spec.Sha512.finalizeApi.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Fn.finalize
    verified := .scrubbed Proof.Sha512.PPC64LE.finalize_scrubbed },
  Spec.Sha512.finalize384Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Fn.finalize384
    verified := .scrubbed Proof.Sha512.PPC64LE.finalize384_scrubbed },
  Spec.Sha512.finalize512_256Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Fn.finalize512_256
    verified := .scrubbed Proof.Sha512.PPC64LE.finalize512_256_scrubbed },
  Spec.Sha512.finalize512_224Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Fn.finalize512_224
    verified := .scrubbed Proof.Sha512.PPC64LE.finalize512_224_scrubbed },
  Spec.Sha512.digest384Api.artifact PPC64LE.target Proof.Sha512.PPC64LE.digest384Reg,
  Spec.Sha512.digest512Api.artifact PPC64LE.target Proof.Sha512.PPC64LE.digest512Reg,
  Spec.Sha512.digest512_224Api.artifact PPC64LE.target Proof.Sha512.PPC64LE.digest512_224Reg,
  Spec.Sha512.digest512_256Api.artifact PPC64LE.target Proof.Sha512.PPC64LE.digest512_256Reg]

end VG.Artifacts.Sha512.PPC64LE
