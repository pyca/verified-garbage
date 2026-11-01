module

public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Copy
import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
import VerifiedGarbage.Proof.CmacAes.X86_64.Finalize
import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.X86_64.Bits
public import VerifiedGarbage.Impl.Gcm.X86_64
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Copy
public import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
public import VerifiedGarbage.Proof.CmacAes.X86_64.Finalize
public import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Gcm.Spec
public import VerifiedGarbage.Proof.Gcm.X86_64.Bits

/-! # AES-CMAC (NIST SP 800-38B) on x86-64 -/

@[expose] public section

namespace VG.Generic.AesCtr32.X86_64.CmacAes

open VG.Proof.CmacAes.X86_64

def artifacts (v : Proof.Aes.X86_64.Ctr32Impl) : List Artifact := [
  Spec.Cmac.aesInitApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2312 .rcx
      (Impl.CmacAes.Stream.X86_64.init v.expand v.callee v.suffix)
    stack := 2328
    verified := Proof.CmacAes.Stream.X86_64.init_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.init_spSafe v)
    features := v.features },
  Spec.Cmac.aesFinishApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2312 .r8
      (Impl.CmacAes.Stream.X86_64.finish v.callee v.suffix)
    stack := 2328
    verified := Proof.CmacAes.Stream.X86_64.finish_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.finish_spSafe v)
    features := v.features }]

end VG.Generic.AesCtr32.X86_64.CmacAes
