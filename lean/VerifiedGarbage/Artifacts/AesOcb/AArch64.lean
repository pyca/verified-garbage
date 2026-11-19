module

public import VerifiedGarbage.Proof.AesOcb.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
public import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
public import VerifiedGarbage.Proof.AesOcb.AArch64.CTBase
public import VerifiedGarbage.Proof.AesOcb.AArch64.InitCT
public import VerifiedGarbage.Proof.Cmac.Block
public import VerifiedGarbage.Proof.Cmac.Dbl32
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Ocb.Spec
public import VerifiedGarbage.Proof.Ocb.State
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64
public import VerifiedGarbage.Impl.Aes.AArch64.Blocks
public import VerifiedGarbage.Proof.Aes.AArch64.Encrypt
public import VerifiedGarbage.Proof.Aes.InvSboxSpec
public import VerifiedGarbage.Proof.Aes.InvBitsliced

/-! # AES-OCB (RFC 7253) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesOcb.AArch64

open VG.Proof.AesOcb.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.AArch64.variants.flatMap fun (v : Proof.Aes.AArch64.BlocksImpl) => [
    Spec.Ocb.initApi.artifact AArch64.target (initReg v),
    Spec.Ocb.sealApi.artifact AArch64.target (sealReg v),
    Spec.Ocb.openApi.artifact AArch64.target (openReg v)]

end VG.Artifacts.AesOcb.AArch64
