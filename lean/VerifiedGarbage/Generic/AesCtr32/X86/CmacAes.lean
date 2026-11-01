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
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.Stream.X86.Absorb
import VerifiedGarbage.Proof.CmacAes.X86.UpdateCT
import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Sha256.Stream

/-! # AES-CMAC (NIST SP 800-38B) on x86 -/

@[expose] public section

namespace VG.Generic.AesCtr32.X86.CmacAes

open VG.Proof.CmacAes.X86

def artifacts (v : Proof.Aes.X86.Ctr32Impl) : List Artifact := [
  Spec.Cmac.aesInitApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2324 3
      (Impl.CmacAes.Stream.X86.init v.expand v.callee v.suffix)
    stack := 2372
    verified := Proof.CmacAes.Stream.X86.init_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe
      (Proof.CmacAes.Stream.X86.init_spSafe v)
    features := v.features },
  Spec.Cmac.aesAbsorbApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2336 6
      (Impl.CmacAes.Stream.X86.absorb v.callee v.suffix)
    stack := 2392
    verified := Proof.CmacAes.Stream.X86.absorb_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe
      (Proof.CmacAes.Stream.X86.absorb_spSafe v)
    features := v.features },
  Spec.Cmac.aesFinishApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2332 5
      (Impl.CmacAes.Stream.X86.finish v.callee v.suffix)
    stack := 2388
    verified := Proof.CmacAes.Stream.X86.finish_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe
      (Proof.CmacAes.Stream.X86.finish_spSafe v)
    features := v.features }]

end VG.Generic.AesCtr32.X86.CmacAes
