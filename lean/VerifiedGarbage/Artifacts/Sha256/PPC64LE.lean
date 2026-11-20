module

public import VerifiedGarbage.Proof.Sha256.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha256
import VerifiedGarbage.Proof.Sha256.PPC64LE.Lit
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Sha224
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha224

/-! # SHA-256 (FIPS 180-4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sha256.PPC64LE

def artifacts : List Artifact := [
  Spec.Sha256.init224Api.artifact PPC64LE.target {
    code := Impl.Sha256.PPC64LE.Stream.init224
    verified := .scrubbed Proof.Sha256.PPC64LE.init224_scrubbed },
  Spec.Sha256.finalize224Api.artifact PPC64LE.target {
    code := Impl.Sha256.PPC64LE.Fn.finalize224
    verified := .scrubbed Proof.Sha256.PPC64LE.finalize224_scrubbed },
  Spec.Sha256.digest224Api.artifact PPC64LE.target Proof.Sha256.PPC64LE.digest224Reg,
  Spec.Sha256.initApi.artifact PPC64LE.target {
    code := Impl.Sha256.PPC64LE.Stream.init
    verified := .scrubbed Proof.Sha256.PPC64LE.init_scrubbed },
  Spec.Sha256.updateApi.artifact PPC64LE.target {
    code := Impl.Sha256.PPC64LE.Fn.update
    verified := .scrubbed Proof.Sha256.PPC64LE.update_scrubbed },
  Spec.Sha256.finalizeApi.artifact PPC64LE.target {
    code := Impl.Sha256.PPC64LE.Fn.finalize
    verified := .scrubbed Proof.Sha256.PPC64LE.finalize_scrubbed },
  Spec.Sha256.digest256Api.artifact PPC64LE.target Proof.Sha256.PPC64LE.digest256Reg]

end VG.Artifacts.Sha256.PPC64LE
