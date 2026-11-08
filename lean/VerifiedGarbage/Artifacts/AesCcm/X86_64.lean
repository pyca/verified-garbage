module

public import VerifiedGarbage.Proof.AesCcm.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
public import VerifiedGarbage.Impl.Gcm.X86_64
public import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
public import VerifiedGarbage.Proof.AesCcm.X86_64.Blocks
public import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
public import VerifiedGarbage.Proof.AesCcm.X86_64.Crypt
public import VerifiedGarbage.Proof.AesCcm.X86_64.CryptCT
public import VerifiedGarbage.Proof.AesCcm.X86_64.Ctrs
public import VerifiedGarbage.Proof.AesCcm.X86_64.Header
public import VerifiedGarbage.Proof.AesCcm.X86_64.Mac
public import VerifiedGarbage.Proof.AesCcm.X86_64.OpenCT
public import VerifiedGarbage.Proof.AesCcm.X86_64.Run
public import VerifiedGarbage.Proof.AesCcm.X86_64.Seal
public import VerifiedGarbage.Proof.AesCcm.X86_64.Tag
public import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
public import VerifiedGarbage.Proof.CmacAes.X86_64.Finalize
public import VerifiedGarbage.Proof.CmacAes.X86_64.FinalizeCorrect
public import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Bswap
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Gcm.Spec
public import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.Proof.Gcm.X86_64.Bits
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.CmacAesUpdate.X86_64

/-! # AES-CCM (NIST SP 800-38C) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesCcm.X86_64

open VG.Proof.AesCcm.X86_64

def artifactsFor (v : Proof.CmacAes.X86_64.UpdateImpl) : List Artifact := [
  Spec.Ccm.sealApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (Impl.AesCcm.X86_64.seal v.callee v.ctr.callee)
    stack := 2624
    verified := Proof.AesCcm.seal_keyed (seal_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (seal_spSafe v)
    features := v.ctr.features },
  Spec.Ccm.openApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (Impl.AesCcm.X86_64.open v.callee v.ctr.callee)
    stack := 2624
    verified := Proof.AesCcm.open_keyed (open_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (open_spSafe v)
    features := v.ctr.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.CmacAesUpdate.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.AesCcm.X86_64
