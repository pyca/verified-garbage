module

public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
public import VerifiedGarbage.Proof.CmacAes.X86.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.Blocks
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Absorb
public import VerifiedGarbage.Proof.CmacAes.X86.UpdateCT
public import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.Mmx
public import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86

/-! # AES-CMAC (NIST SP 800-38B) on x86 -/

@[expose] public section

namespace VG.Artifacts.CmacAes.X86

open VG.Proof.CmacAes.X86

def artifactsFor (v : Proof.Aes.X86.Ctr32Impl) : List Artifact := [
  Spec.Cmac.aesInitApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2324 3
      (Impl.CmacAes.Stream.X86.init v.expand v.callee v.suffix)
    stack := 2376
    verified := Proof.CmacAes.Stream.X86.init_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe
      (Proof.CmacAes.Stream.X86.init_spSafe v)
    features := v.features },
  Spec.Cmac.aesAbsorbApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2336 6
      (Impl.CmacAes.Stream.X86.absorb v.callee v.suffix)
    stack := 2396
    verified := Proof.CmacAes.Stream.X86.absorb_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe
      (Proof.CmacAes.Stream.X86.absorb_spSafe v)
    features := v.features },
  Spec.Cmac.aesFinishApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2332 5
      (Impl.CmacAes.Stream.X86.finish v.callee v.suffix)
    stack := 2392
    verified := Proof.CmacAes.Stream.X86.finish_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe
      (Proof.CmacAes.Stream.X86.finish_spSafe v)
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.AesCtr32.X86.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.CmacAes.X86
