module

public import VerifiedGarbage.Impl.Aes.X86_64.Fn
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
public import VerifiedGarbage.Proof.Aes.X86_64.Frame
public import VerifiedGarbage.Proof.Aes.X86_64.Scrub
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # AES (FIPS 197) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Aes.X86_64

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact X86_64.target {
    suffix := "_aesni"
    code := Impl.Aes.X86_64.Fn.expandKeyAesni
    verified := .scrubbed Proof.Aes.X86_64.Scrub.expandKeyAesni_scrubbed
    spSafe := Proof.Aes.X86_64.Scrub.expandKeyAesni_spSafe },
  Spec.Aes.expandKeyApi.artifact X86_64.target {
    code := Impl.Aes.X86_64.Fn.expandKey
    verified := .scrubbed Proof.Aes.X86_64.Scrub.expandKey_scrubbed
    spSafe := Proof.Aes.X86_64.Scrub.expandKey_spSafe }]

end VG.Artifacts.Aes.X86_64
