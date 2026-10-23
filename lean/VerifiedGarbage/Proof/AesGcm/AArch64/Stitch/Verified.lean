module
public import VerifiedGarbage.Impl.AesGcm.AArch64.Stitch
public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Weave
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ops


/-!
# AES-GCM on AArch64, interleaved: what `Verified` needs of `sealWithS` and `openWithS`

Untrusted: everything here is checked by Lean. `sealWithS` and `openWithS`
(`Impl/AesGcm/AArch64/Stitch.lean`) keep `v8`–`v15` (`keepsV`), for any table
code and call that do; the functions with the powers (`SealPw.lean`,
`OpenPw.lean`) are `Verified` from it.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

theorem stitchSealWithS_keepsV (v : GcmImpl) {k : Nat} (hk : k = 8 ∨ k = 16) {tb : List Instr}
    (htb : (Code.block tb : Prog isa).allInstrs keepsV = true) {cl : Prog isa} (hcl : cl.allInstrs keepsV = true)
    {sh : Bool} : (Impl.AesGcm.AArch64.Stitch.sealWithS v.callees k tb cl sh).allInstrs keepsV = true := by
  simp only [Code.allInstrs] at htb
  rcases hk with rfl | rfl <;> cases sh <;>
  simp only [Impl.AesGcm.AArch64.Stitch.sealWithS, Impl.AesGcm.AArch64.Stitch.runWithS,
    Impl.AesGcm.AArch64.Stitch.thr, Impl.AesGcm.AArch64.Fast.runWithP,
    Impl.AesGcm.AArch64.Stitch.sealShort, Impl.AesGcm.AArch64.Stitch.textOut, Impl.AesGcm.AArch64.Stitch.shortThr, Impl.AesGcm.AArch64.Stitch.shortMin,
    Impl.AesGcm.AArch64.Stitch.shortPre, Impl.AesGcm.AArch64.Stitch.textIn, Impl.AesGcm.AArch64.Stitch.copyQ,
    Impl.AesGcm.AArch64.Stitch.ctToB2, Impl.AesGcm.AArch64.Stitch.aadIn, Impl.AesGcm.AArch64.Stitch.shortAes,
    Impl.AesGcm.AArch64.SealGather.copyBlocks, Impl.Gcm.AArch64.Stitch.byRounds, Bool.false_eq_true, ite_true, ite_false,
    Impl.AesGcm.AArch64.Stitch.stitched, Impl.AesGcm.AArch64.Fast.front, Impl.AesGcm.AArch64.Fast.cond,
    Impl.AesGcm.AArch64.Fast.padMul, Impl.AesGcm.AArch64.Fast.padMulT, Impl.AesGcm.AArch64.Tail.cryptAlT,
    Impl.AesGcm.AArch64.Tail.crSeg2T, Impl.AesGcm.AArch64.Tail.crTailT, crSeg2, crTail, sealRest, j0, j0hash, oneAad, absorbAl, encBody, fo,
    textAbs, finBody, tag, crypt, crSeg1, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy,
    Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, List.nil_append,
    v.ctr.keepsV, v.gh.keepsV, htb, hcl, Bool.and_true, Bool.true_and] <;> decide +kernel

theorem stitchOpenWithS_keepsV (v : GcmImpl) {k : Nat} (hk : k = 16 ∨ k = 24) {tb : List Instr}
    (htb : (Code.block tb : Prog isa).allInstrs keepsV = true) {cl : Prog isa} (hcl : cl.allInstrs keepsV = true)
    {sh : Bool} : (Impl.AesGcm.AArch64.Stitch.openWithS v.callees k tb cl sh).allInstrs keepsV = true := by
  simp only [Code.allInstrs] at htb
  rcases hk with rfl | rfl <;> cases sh <;>
  simp only [Impl.AesGcm.AArch64.Stitch.openWithS, Impl.AesGcm.AArch64.Stitch.openFastS,
    Impl.AesGcm.AArch64.Stitch.thr, Impl.AesGcm.AArch64.Fast.openFastP, Impl.AesGcm.AArch64.Fast.openRunWithP,
    Impl.AesGcm.AArch64.Stitch.openShortF, Impl.AesGcm.AArch64.Stitch.openShort, Impl.AesGcm.AArch64.Stitch.plainOut, Impl.AesGcm.AArch64.Stitch.shortThr, Impl.AesGcm.AArch64.Stitch.shortMin,
    Impl.AesGcm.AArch64.Stitch.shortPre, Impl.AesGcm.AArch64.Stitch.textIn, Impl.AesGcm.AArch64.Stitch.copyQ,
    Impl.AesGcm.AArch64.Stitch.ctToB2, Impl.AesGcm.AArch64.Stitch.aadIn, Impl.AesGcm.AArch64.Stitch.shortAes,
    Impl.AesGcm.AArch64.SealGather.copyBlocks, Impl.Gcm.AArch64.Stitch.byRounds, Bool.false_eq_true, ite_true, ite_false,
    Impl.AesGcm.AArch64.Stitch.openRunWithS, Impl.AesGcm.AArch64.Stitch.stitched, Impl.AesGcm.AArch64.Fast.front,
    Impl.AesGcm.AArch64.Fast.cond, Impl.AesGcm.AArch64.Fast.padMul, Impl.AesGcm.AArch64.Fast.padMulT,
    Impl.AesGcm.AArch64.Fast.oneCryptT, Impl.AesGcm.AArch64.Tail.cryptAlT, Impl.AesGcm.AArch64.Tail.crSeg2T,
    Impl.AesGcm.AArch64.Tail.crTailT, openRest, openMain, oneCrypt, cryptAl, crArgs,
    tagLenOk, tagIn, cmpSeg, cmp, cmp16, j0, j0hash, oneAad, absorbAl, decAbs, fo, textAbs, finBody, tag,
    crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, Impl.AesGcm.AArch64.xor,
    padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, List.nil_append, v.ctr.keepsV,
    v.gh.keepsV, htb, hcl, Bool.and_true, Bool.true_and] <;> decide +kernel

theorem powTbl_keepsV : (Code.block Impl.AesGcm.AArch64.Stitch.powTbl : Prog isa).allInstrs keepsV = true := by
  decide +kernel

theorem pwTbl_keepsV {k : Nat} (hk : k = 8 ∨ k = 16) :
    (Code.block (Impl.AesGcm.AArch64.Stitch.pwTbl k) : Prog isa).allInstrs keepsV = true := by
  rcases hk with rfl | rfl <;> decide +kernel

end VG.Proof.AesGcm.AArch64
