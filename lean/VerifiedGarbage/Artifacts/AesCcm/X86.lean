module

public import VerifiedGarbage.Proof.AesCcm.X86.Frame
public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Cmac.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyRecurrence
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Load
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Restore
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
public import VerifiedGarbage.Proof.AesCcm.X86.Aad
public import VerifiedGarbage.Proof.AesCcm.X86.AadCT
public import VerifiedGarbage.Proof.AesCcm.X86.Blocks
public import VerifiedGarbage.Proof.AesCcm.X86.Entry
public import VerifiedGarbage.Proof.AesCcm.X86.Mac
public import VerifiedGarbage.Proof.AesCcm.X86.Run
public import VerifiedGarbage.Proof.AesCcm.X86.SealCT
public import VerifiedGarbage.Proof.AesGcm.X86.CryptHead
public import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
public import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
public import VerifiedGarbage.Proof.AesGcm.X86.Flush
public import VerifiedGarbage.Proof.AesGcm.X86.Top
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Absorb
public import VerifiedGarbage.Proof.CmacAes.X86.UpdateCT
public import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect
public import VerifiedGarbage.Proof.CmacAes.X86.Verified
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86

/-! # AES-CCM (NIST SP 800-38C) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesCcm.X86

open VG.Proof.AesCcm.X86

def artifactsFor (v : Proof.Aes.X86.Ctr32Impl) : List Artifact := [
  Spec.Ccm.sealApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2608 10 (Impl.AesCcm.X86.seal v.callee v.suffix)
    stack := 2668
    verified := Proof.AesCcm.seal_keyed (seal_framed v)
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (seal_spSafe v)
    features := v.features },
  Spec.Ccm.openApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2608 10 (Impl.AesCcm.X86.open v.callee v.suffix)
    stack := 2668
    verified := Proof.AesCcm.open_keyed (open_framed v)
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (open_spSafe v)
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.AesCtr32.X86.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.AesCcm.X86
