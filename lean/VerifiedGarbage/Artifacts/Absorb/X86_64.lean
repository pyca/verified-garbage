module

public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
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
public import VerifiedGarbage.Proof.Variants.CmacAesUpdate.X86_64

/-! # Streaming AES-CMAC's `absorb` on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Absorb.X86_64

def artifactsFor (v : Proof.CmacAes.X86_64.UpdateImpl) : List Artifact := [
  Spec.Cmac.aesAbsorbApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2312 .r9 (Impl.CmacAes.Stream.X86_64.absorb v.callee)
    stack := 2328
    verified := Proof.CmacAes.Stream.X86_64.absorb_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.absorb_spSafe v)
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.CmacAesUpdate.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Absorb.X86_64
