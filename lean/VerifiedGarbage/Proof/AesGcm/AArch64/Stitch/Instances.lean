module
public import VerifiedGarbage.Impl.AesGcm.AArch64.Stitch
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.AesGcm.AArch64.Verified
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ops

import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenPw
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw

/-!
# AES-GCM on AArch64: the code of each function, with or without the interleaved loops

Untrusted: everything here is checked by Lean. For the implementations `v`,
the code of `seal`, `open` and the functions with the powers: with the loops
that interleave counter mode and GHASH (`Impl/AesGcm/AArch64/Stitch.lean`)
if `v.stitch`, and otherwise as before, each `Verified` against its contract,
for `Generic/AesGcm/AArch64/AesGcm.lean`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull (MulKey PrepPow)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-- The CPU features of the functions that may run the interleaved loops:
`v`'s, and `FEAT_SHA3` for `eor3` with them. -/
def GcmImpl.stitchFeatures (v : GcmImpl) : List String := v.features ++ if v.stitch then ["sha3"] else []

/-- `vg_aes_gcm_seal_with_powers`, calling `g`. -/
def sealPwCode (v : GcmImpl) (g : GhashWithImpl) : Prog isa :=
  if v.stitch then Impl.AesGcm.AArch64.Stitch.sealWithPw v.callees g.fn else Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn

/-- `vg_aes_gcm_open_with_powers`, calling `g`. -/
def openPwCode (v : GcmImpl) (g : GhashWithImpl) : Prog isa :=
  if v.stitch then Impl.AesGcm.AArch64.Stitch.openWithPw v.callees g.fn else Impl.AesGcm.AArch64.Fast.openWithPw v.callees g.fn

/-- `vg_aes_gcm_seal_store_powers`, calling `g`. -/
def sealStCode (v : GcmImpl) (g : GhashStoreImpl) : Prog isa :=
  if v.stitch then Impl.AesGcm.AArch64.Stitch.sealStorePw v.callees g.fn
  else Impl.AesGcm.AArch64.Fast.sealStorePw v.callees g.fn

/-- `vg_aes_gcm_open_store_powers`, calling `g`. -/
def openStCode (v : GcmImpl) (g : GhashStoreImpl) : Prog isa :=
  if v.stitch then Impl.AesGcm.AArch64.Stitch.openStorePw v.callees g.fn
  else Impl.AesGcm.AArch64.Fast.openStorePw v.callees g.fn

section
variable (v : GcmImpl) (hMK : MulKey) (hP : PrepPow) (gh : Gh8Ok)
include hMK hP gh

omit hP in
theorem sealPwCode_framed (g : GhashWithImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (sealPwCode v g))
      (Spec.Gcm.sealWithPowersContract AArch64.abi 2592) := by
  unfold sealPwCode
  split
  · exact Fast.sealPwS_framed v g hMK gh
  · exact Fast.sealPw_framed v g hMK

omit hP in
theorem openPwCode_framed (g : GhashWithImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2592 3 (openPwCode v g))
      (Spec.Gcm.openWithPowersContract AArch64.abi 2592) := by
  unfold openPwCode
  split
  · exact Fast.openPwS_framed v g hMK gh
  · exact Fast.openPw_framed v g hMK

theorem sealStCode_framed (g : GhashStoreImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (sealStCode v g))
      (Spec.Gcm.sealStorePowersContract AArch64.abi 2592) := by
  unfold sealStCode
  split
  · exact Fast.sealStS_framed v g hMK hP gh
  · exact Fast.sealSt_framed v g hMK

theorem openStCode_framed (g : GhashStoreImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2592 3 (openStCode v g))
      (Spec.Gcm.openStorePowersContract AArch64.abi 2592) := by
  unfold openStCode
  split
  · exact Fast.openStS_framed v g hMK hP gh
  · exact Fast.openSt_framed v g hMK

end

end VG.Proof.AesGcm.AArch64
