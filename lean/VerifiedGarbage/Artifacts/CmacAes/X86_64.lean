module

public import VerifiedGarbage.Proof.CmacAes.X86_64.AesNi
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
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
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86_64

/-! # AES-CMAC's chaining with AES-NI on x86-64 -/

@[expose] public section

namespace VG.Artifacts.CmacAes.X86_64

def direct : List Artifact := [
  ]

end VG.Artifacts.CmacAes.X86_64

-- AES-CMAC (NIST SP 800-38B) on x86-64
namespace VG.Artifacts.CmacAes.X86_64.AesCtr32

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

end VG.Artifacts.CmacAes.X86_64.AesCtr32

namespace VG.Artifacts.CmacAes.X86_64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.AesCtr32.X86_64.variants.flatMap fun v => AesCtr32.artifacts v)

end VG.Artifacts.CmacAes.X86_64
