module

public import VerifiedGarbage.Proof.AesSiv.X86.Verified
public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Cmac.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyRecurrence
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Load
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Restore
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
public import VerifiedGarbage.Proof.AesCcm.Mac
public import VerifiedGarbage.Proof.AesGcm.X86.CryptHead
public import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
public import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
public import VerifiedGarbage.Proof.AesGcm.X86.Flush
public import VerifiedGarbage.Proof.AesGcm.X86.Top
public import VerifiedGarbage.Proof.AesSiv.X86.Dec
public import VerifiedGarbage.Proof.AesSiv.X86.FinRaw
public import VerifiedGarbage.Proof.AesSiv.X86.Finish
public import VerifiedGarbage.Proof.AesSiv.X86.FinishCT
public import VerifiedGarbage.Proof.AesSiv.X86.FinishLong
public import VerifiedGarbage.Proof.AesSiv.X86.Init
public import VerifiedGarbage.Proof.AesSiv.X86.Run
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

/-! # AES-SIV (RFC 5297) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesSiv.X86

open VG.Proof.AesSiv.X86

def artifactsFor (v : Proof.Aes.X86.Ctr32Impl) : List Artifact := [
  Spec.Siv.initApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2580 3 (Impl.AesSiv.X86.initCore v.expand v.callee v.suffix)
    stack := 2632
    verified := init_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (init_spSafe v)
    features := v.features },
  Spec.Siv.encryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2612 7 (Impl.AesSiv.X86.encrypt v.callee v.suffix)
    stack := 2672
    verified := Proof.AesSiv.encrypt_keyed (encrypt_framed v)
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (encrypt_spSafe v)
    features := v.features },
  Spec.Siv.decryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2612 7 (Impl.AesSiv.X86.decrypt v.callee v.suffix)
    stack := 2672
    verified := Proof.AesSiv.decrypt_keyed (decrypt_framed v)
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (decrypt_spSafe v)
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.AesCtr32.X86.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.AesSiv.X86
