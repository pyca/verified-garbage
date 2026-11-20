module

public import VerifiedGarbage.Impl.AesEcb.X86
public import VerifiedGarbage.Proof.AesEcb.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-ECB (NIST SP 800-38A §6.1) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesEcb.X86

open VG.Proof.AesEcb.X86.Scrub

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    if h : v.encWritten = 0 ∧ v.enc.code.noCalls = true then
      Spec.AesEcb.encryptApi.artifact X86.target {
        suffix := v.suffix
        code := Impl.AesEcb.X86.Fn.free v.enc
        verified := .scrubbed (encryptFree_scrubbed v h)
        spSafe := encryptFree_fnSpSafe v }
    else
      Spec.AesEcb.encryptApi.artifact X86.target {
        suffix := v.suffix
        code := Impl.AesEcb.X86.Fn.wiped v.enc v.encWritten
        verified := .scrubbed (encryptWiped_scrubbed v)
        spSafe := encryptWiped_fnSpSafe v },
    if h : v.decWritten = 0 ∧ v.dec.code.noCalls = true then
      Spec.AesEcb.decryptApi.artifact X86.target {
        suffix := v.suffix
        code := Impl.AesEcb.X86.Fn.free v.dec
        verified := .scrubbed (decryptFree_scrubbed v h)
        spSafe := decryptFree_fnSpSafe v }
    else
      Spec.AesEcb.decryptApi.artifact X86.target {
        suffix := v.suffix
        code := Impl.AesEcb.X86.Fn.wiped v.dec v.decWritten
        verified := .scrubbed (decryptWiped_scrubbed v)
        spSafe := decryptWiped_fnSpSafe v }]

end VG.Artifacts.AesEcb.X86
