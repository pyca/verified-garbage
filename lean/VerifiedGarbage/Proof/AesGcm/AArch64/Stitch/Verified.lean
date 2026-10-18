module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Seal
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.CT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenW
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenVerified
import VerifiedGarbage.Spec.Gcm.Contract

/-!
# AES-GCM on AArch64, interleaved: `vg_aes_gcm_seal` and `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. The functions with the
interleaved path for TLS records (`Impl/AesGcm/AArch64/Stitch.lean`) are
`Verified` against `seal`'s and `open`'s contracts, for any `mul` of prepared
powers that is one (`PrepPow`) and any `ghPart` that is GHASH (`Gh8Ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

theorem stitchSealWithS_keepsV (v : GcmImpl) {k : Nat} (hk : k = 8 ∨ k = 16) {tb : List Instr}
    (htb : (Code.block tb : Prog isa).allInstrs keepsV = true) {cl : Prog isa} (hcl : cl.allInstrs keepsV = true) :
    (Impl.AesGcm.AArch64.Stitch.sealWithS v.callees k tb cl).allInstrs keepsV = true := by
  simp only [Code.allInstrs] at htb
  rcases hk with rfl | rfl <;>
  simp only [Impl.AesGcm.AArch64.Stitch.sealWithS, Impl.AesGcm.AArch64.Stitch.runWithS,
    Impl.AesGcm.AArch64.Stitch.stitched, Impl.AesGcm.AArch64.Fast.front, Impl.AesGcm.AArch64.Fast.cond,
    Impl.AesGcm.AArch64.Fast.padMul, cryptAl, crSeg2, crTail, sealRest, j0, j0hash, oneAad, absorbAl, encBody, fo,
    textAbs, finBody, tag, crypt, crSeg1, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy,
    Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, List.nil_append,
    v.ctr.keepsV, v.gh.keepsV, htb, hcl, Bool.and_true, Bool.true_and] <;> decide +kernel

theorem stitchOpenWithS_keepsV (v : GcmImpl) {k : Nat} (hk : k = 16 ∨ k = 24) {tb : List Instr}
    (htb : (Code.block tb : Prog isa).allInstrs keepsV = true) {cl : Prog isa} (hcl : cl.allInstrs keepsV = true) :
    (Impl.AesGcm.AArch64.Stitch.openWithS v.callees k tb cl).allInstrs keepsV = true := by
  simp only [Code.allInstrs] at htb
  rcases hk with rfl | rfl <;>
  simp only [Impl.AesGcm.AArch64.Stitch.openWithS, Impl.AesGcm.AArch64.Stitch.openFastS,
    Impl.AesGcm.AArch64.Stitch.openRunWithS, Impl.AesGcm.AArch64.Stitch.stitched, Impl.AesGcm.AArch64.Fast.front,
    Impl.AesGcm.AArch64.Fast.cond, Impl.AesGcm.AArch64.Fast.padMul, openRest, openMain, oneCrypt, cryptAl, crArgs,
    tagLenOk, tlTest, tagIn, cmpSeg, cmp, cmp16, j0, j0hash, oneAad, absorbAl, decAbs, fo, textAbs, finBody, tag,
    crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, Impl.AesGcm.AArch64.xor,
    padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, List.nil_append, v.ctr.keepsV,
    v.gh.keepsV, htb, hcl, Bool.and_true, Bool.true_and] <;> decide +kernel

theorem powTbl_keepsV : (Code.block Impl.AesGcm.AArch64.Stitch.powTbl : Prog isa).allInstrs keepsV = true := by
  decide +kernel

theorem pwTbl_keepsV {k : Nat} (hk : k = 8 ∨ k = 16) :
    (Code.block (Impl.AesGcm.AArch64.Stitch.pwTbl k) : Prog isa).allInstrs keepsV = true := by
  rcases hk with rfl | rfl <;> decide +kernel

theorem stitchSeal_keepsV (v : GcmImpl) :
    (Impl.AesGcm.AArch64.Stitch.«seal» v.callees).allInstrs keepsV = true :=
  stitchSealWithS_keepsV v (.inl rfl) powTbl_keepsV (by simp only [Code.allInstrs, GcmImpl.callees, v.gh.keepsV])

theorem stitchOpen_keepsV (v : GcmImpl) :
    (Impl.AesGcm.AArch64.Stitch.«open» v.callees).allInstrs keepsV = true :=
  stitchOpenWithS_keepsV v (.inl rfl) powTbl_keepsV (by simp only [Code.allInstrs, GcmImpl.callees, v.gh.keepsV])

theorem stitchSeal_verified (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
    (hP : Proof.Gcm.AArch64.Pmull.PrepPow) (gh : Gh8Ok) :
    Verified AArch64.target (Impl.AesGcm.AArch64.Stitch.«seal» v.callees)
      (Proof.AesGcm.sealScratchContract AArch64.abi) :=
  Verified.of_correct (fun s hs => WP.withPreservedV (Fast.sealS_wp v hMK hP gh hs) (stitchSeal_keepsV v))
    (Fast.sealS_ct v hMK hP gh) (by
    sig_implies [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
      Spec.Gcm.sealPost, sealAArch64, sealPre, sealPreX, List.append_nil, onePub, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem stitchOpen_verified (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
    (hP : Proof.Gcm.AArch64.Pmull.PrepPow) (gh : Gh8Ok) :
    Verified AArch64.target (Impl.AesGcm.AArch64.Stitch.«open» v.callees)
      (Proof.AesGcm.openScratchContract AArch64.abi) :=
  Verified.of_correct (fun s hs => WP.withPreservedV (Fast.openS_wp v hMK hP gh hs) (stitchOpen_keepsV v))
    (Fast.openS_ct v hMK hP gh) (by
    sig_implies [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
      Spec.Gcm.openPost, Spec.Gcm.openLeak, openAArch64, openPre, openPreX, List.append_nil, onePub, openRes,
      openLeakOf, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD,
      List.range, List.range.loop]
      [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat)

end VG.Proof.AesGcm.AArch64
