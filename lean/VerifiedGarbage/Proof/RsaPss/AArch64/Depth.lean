module

public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Core

/-!
# EMSA-PSS's encoding and its check on AArch64: their frames

`encode` and `checkEncoding` push their frame (21 units of 16 bytes) and call
only the hash function's `init` (one frame) and compression function (none):
their depth is at most 22 (`encode_depth`, `chk_depth`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK fdepth_of_noFrames)

variable {H : Hash} (hH : HashOK H)
include hH

theorem encode_depth : (encode H).aarch64Depth ≤ 22 := by
  have hi := hH.stream.initDepth
  have hc := fdepth_of_noFrames hH.comp.noFrames
  simp [encode, encBody, encMain, ret0, copyOut, signEnc, Code.aarch64Depth, seqs, clearY, copyDigest, copySaltY,
    ctHash, ctHashWith, clearEm, putSalt, putH, mgfXor, Impl.RsaPkcs1Sig.AArch64.copyLoop, Instr.frameUnits,
    frameBytes, ctInit, compLoop, mgfHash, xorOut, nextCtr, clearBlock, copyH, counter, fixedPad80, pad80, lenField,
    lenLoop, digestOut, Impl.MdStream.AArch64.compressAt, Impl.MdStream.AArch64.compressWith, hc, select,
    Impl.RsaPkcs1Sig.AArch64.psLoop]
  exact hi

theorem chk_depth : (checkEncoding H).aarch64Depth ≤ 22 := by
  have hi := hH.stream.initDepth
  have hc := fdepth_of_noFrames hH.comp.noFrames
  simp [checkEncoding, chkBody, chkMain, ret0, copyIn, expLen, Code.aarch64Depth, seqs, mgfXor,
    Impl.RsaPkcs1Sig.AArch64.copyLoop, Instr.frameUnits, frameBytes, ctInit, mgfHash, xorOut, nextCtr, clearBlock,
    copyH, counter, fixedPad80, pad80, lenField, lenLoop, digestOut, Impl.MdStream.AArch64.compressAt,
    Impl.MdStream.AArch64.compressWith, hc, select, compLoop, ctHash, ctHashWith, posScan, posCheck, FixedSalt.select,
    FixedSalt.finish, FixedSalt.copySalt, clearY, copyDigest, copyDb, shift, shiftPass, nextPass, cmpH]
  exact hi

end VG.Proof.RsaPss.AArch64
