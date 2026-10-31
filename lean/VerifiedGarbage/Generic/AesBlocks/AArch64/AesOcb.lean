module

public import VerifiedGarbage.Proof.AesOcb.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Proof.Aes.AArch64.Decrypt
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
public import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Ocb.Spec
public import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Aes.AArch64.Decrypt
import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.AesOcb.AArch64.CTBase
import VerifiedGarbage.Proof.AesOcb.AArch64.InitCT
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Ocb.State

/-! # AES-OCB (RFC 7253) on AArch64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.AArch64.AesOcb

open VG.Proof.AesOcb.AArch64

def artifacts (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact := [
  Spec.Ocb.initApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x3 (Impl.AesOcb.AArch64.init (callees v))
    stack := 2560
    verified := init_framed v
    features := v.features },
  Spec.Ocb.sealApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (Impl.AesOcb.AArch64.seal (callees v))
    stack := 2592
    verified := seal_framed v
    features := v.features },
  Spec.Ocb.openApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (Impl.AesOcb.AArch64.open (callees v))
    stack := 2592
    verified := open_framed v
    features := v.features }]

end VG.Generic.AesBlocks.AArch64.AesOcb
