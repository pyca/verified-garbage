module

public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Verified
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Instances
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash
public import VerifiedGarbage.Proof.AesGcm.AArch64.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.GhashImpls
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.Init
public import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Crypt
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Derive
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.FnCT
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Keys
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Polyval
public import VerifiedGarbage.Proof.Cmac.Dbl32
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Gcm.Be64
public import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Gcm.Powers
public import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.Init
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Crypt
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Derive
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.FnCT
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Keys
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Polyval
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Powers
import VerifiedGarbage.Proof.Siv.Spec

/-!
# AES-GCM-SIV (RFC 8452) on AArch64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and `vg_ghash`
(those of AES-GCM), are emitted once for each combination
(`Variants/AesGcm/AArch64/`), named with its suffix (e.g.
`vg_aes_gcm_siv_seal_aes`), and need the CPU features of the three. **Review
note**: `sig` and `doc` are trusted, as they tie the Rust caller to the
contract; these artifacts are made from each function's `Api` (in `Spec/`,
reviewed with the contract).

Each keeps its working space in a frame of 3824 bytes on the stack
(`Proof/AesGcmSiv/AArch64/Verified.lean`); their calls (`bl`) keep the return
address in `x30`, which they save in the working space, with our caller's
registers, so no other stack is used.
-/

@[expose] public section

namespace VG.Generic.AesGcm.AArch64.AesGcmSiv

open VG.Proof.AesGcm.AArch64 (GcmImpl GcmVariant)
open VG.Proof.AesGcmSiv.AArch64

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.GcmSiv.sealApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 3824 0 (Stitch.sealCode v)
    stack := 3824
    verified := Stitch.sealCode_framed Proof.Gcm.AArch64.Pmull.prepPow Proof.Gcm.AArch64.Stitch.gh8Ok v
    features := v.stitchFeatures },
  Spec.GcmSiv.openApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 3824 0 (Stitch.openCode v)
    stack := 3824
    verified := Stitch.openCode_framed Proof.Gcm.AArch64.Pmull.prepPow Proof.Gcm.AArch64.Stitch.gh8Ok v
    features := v.stitchFeatures }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf v.impl

end VG.Generic.AesGcm.AArch64.AesGcmSiv
