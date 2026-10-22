module

import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Init
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.InitCT
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.StreamCryptCT
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.FinCT
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.SealCT
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.OpenCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Callee
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Contract
public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.StreamCrypt
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Seal
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Open
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.StreamFinish

/-!
# SM4-GCM on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementation `v` of `vg_ghash`), a state satisfying each
precondition, and the shared contracts of `Spec/Sm4/Gcm/Contract.lean` with
the working space as a last argument (`Sig.scratchContract`) and the 3264
bytes of stack `vg_sm4_ctr32` and `vg_sm4_expand_key` use below the stack
pointer.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (minK copy copyB xorB tagLenOk tagIn cmpSeg cmp cmp16 fo textArgs tagOut restore)

/-- The CPU features of the functions calling `vg_ghash`: its implementation's. -/
def GcmImpl.features (v : GcmImpl) : List String := v.gh.features

/-! ## v8–v15 -/

theorem init_keepsV : init.allInstrs keepsV = true := by
  simp only [init, ctrCall, Code.allInstrs, ctrCode_keepsV, keyCode_keepsV]; decide +kernel

theorem streamEncrypt_keepsV (v : GcmImpl) : (streamEncrypt v.callees).allInstrs keepsV = true := by
  simp only [streamEncrypt, encBody, fo, textAbs, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall, absorb,
    absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees,
    Code.allInstrs, ctrCode_keepsV, v.gh.keepsV]; decide +kernel

theorem streamDecrypt_keepsV (v : GcmImpl) : (streamDecrypt v.callees).allInstrs keepsV = true := by
  simp only [streamDecrypt, decBody, decAbs, fo, textAbs, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall,
    absorb, absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens,
    GcmImpl.callees, Code.allInstrs, ctrCode_keepsV, v.gh.keepsV]; decide +kernel

theorem streamFinish_keepsV (v : GcmImpl) : (streamFinish v.callees).allInstrs keepsV = true := by
  simp only [streamFinish, finBody, tag, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, xorB,
    Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, ctrCode_keepsV,
    v.gh.keepsV]; decide +kernel

theorem streamVerify_keepsV (v : GcmImpl) : (streamVerify v.callees).allInstrs keepsV = true := by
  simp only [streamVerify, tagLenOk, tagIn, cmpSeg, cmp, cmp16, finBody, tag, ctrCall, ghCall, absorb,
    absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees,
    Code.allInstrs, ctrCode_keepsV, v.gh.keepsV]; decide +kernel

theorem seal_keepsV (v : GcmImpl) : («seal» v.callees).allInstrs keepsV = true := by
  simp only [«seal», sealRest, j0, j0hash, oneAad, absorbAl, encBody, fo, textAbs, finBody, tag, crypt, crSeg1,
    crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor,
    padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, ctrCode_keepsV, v.gh.keepsV]; decide +kernel

theorem open_keepsV (v : GcmImpl) : («open» v.callees).allInstrs keepsV = true := by
  simp only [«open», openEntry, openRest, openMain, oneCrypt, cryptAl, crArgs, tagLenOk, tagIn, cmpSeg, cmp,
    cmp16, j0, j0hash, oneAad, absorbAl, decAbs, fo, textAbs, finBody, tag, crypt, crSeg1, crSeg2, crTail,
    ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush,
    lens, GcmImpl.callees, Code.allInstrs, ctrCode_keepsV, v.gh.keepsV]
  decide +kernel

/-! ## Correctness -/

theorem init_correct (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  WP.withPreservedV (init_wp hs) init_keepsV

theorem streamEncrypt_correct (v : GcmImpl) (s : State) (hs : streamEncryptAArch64.pre s) :
    ∃ t s', Exec isa (streamEncrypt v.callees) s t s' ∧ abiPreserved s s' ∧ streamEncryptAArch64.post s s' :=
  WP.withPreservedV (streamEncrypt_wp v hs) (streamEncrypt_keepsV v)

theorem streamDecrypt_correct (v : GcmImpl) (s : State) (hs : streamDecryptAArch64.pre s) :
    ∃ t s', Exec isa (streamDecrypt v.callees) s t s' ∧ abiPreserved s s' ∧ streamDecryptAArch64.post s s' :=
  WP.withPreservedV (streamDecrypt_wp v hs) (streamDecrypt_keepsV v)

theorem streamFinish_correct (v : GcmImpl) (s : State) (hs : streamFinishAArch64.pre s) :
    ∃ t s', Exec isa (streamFinish v.callees) s t s' ∧ abiPreserved s s' ∧ streamFinishAArch64.post s s' :=
  WP.withPreservedV (streamFinish_wp v hs) (streamFinish_keepsV v)

theorem streamVerify_correct (v : GcmImpl) (s : State) (hs : streamVerifyAArch64.pre s) :
    ∃ t s', Exec isa (streamVerify v.callees) s t s' ∧ abiPreserved s s' ∧ streamVerifyAArch64.post s s' :=
  WP.withPreservedV (streamVerify_wp v hs) (streamVerify_keepsV v)

theorem seal_correct (v : GcmImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa («seal» v.callees) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (seal_wp v hs) (seal_keepsV v)

theorem open_correct (v : GcmImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa («open» v.callees) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (open_wp v hs) (open_keepsV v)

/-! ## States satisfying the preconditions (with empty buffers)

The stack pointer is `0x8000`, and the 3264 bytes below it are apart from
every buffer. -/

def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 768⟩]

def streamCryptSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x4 => 0x2000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 768⟩]

def finSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x4 => 0x5000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 768⟩]

def verSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x4 => 0x5000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 768⟩]

/-- `tag` at `0x6000` and `work` at `0x5000` (`[sp]`). -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | .x7 => 0x6000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8001 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x6000, 16⟩, ⟨0x5000, 768⟩]

/-- `tag` at `0x6000`, `tag_len` 0 (`[sp]`) and `work` at `0x5000` (`[sp + 8]`). -/
def openSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | .x7 => 0x6000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8009 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x6000, 0⟩, ⟨0x8000, 16⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 768⟩]

/-! ## The shared contracts -/

theorem init_verified :
    Verified AArch64.target init (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.initSig "scratch" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.initPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.initSig,
      Spec.Sm4.Gcm.initPost, initAArch64, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow]
      [initSat] using initSat)

theorem streamEncrypt_verified (v : GcmImpl) :
    Verified AArch64.target (streamEncrypt v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.streamCryptSig "scratch" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamEncryptPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (streamEncrypt_correct v) (streamEncrypt_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamEncryptPost, streamEncryptAArch64, streamCryptPre, streamCryptPub]
      [streamCryptSat] using streamCryptSat)

theorem streamDecrypt_verified (v : GcmImpl) :
    Verified AArch64.target (streamDecrypt v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.streamCryptSig "scratch" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamDecryptPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (streamDecrypt_correct v) (streamDecrypt_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamDecryptPost, streamDecryptAArch64, streamCryptPre, streamCryptPub]
      [streamCryptSat] using streamCryptSat)

theorem streamFinish_verified (v : GcmImpl) :
    Verified AArch64.target (streamFinish v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.streamFinishSig "work" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamFinishPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (streamFinish_correct v) (streamFinish_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.streamFinishSig, Spec.Sm4.Gcm.streamFinishPost, streamFinishAArch64, finPre]
      [finSat] using finSat)

theorem streamVerify_verified (v : GcmImpl) :
    Verified AArch64.target (streamVerify v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.streamVerifySig "work" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamVerifyPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (streamVerify_correct v) (streamVerify_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.streamVerifySig, Spec.Sm4.Gcm.streamVerifyPost, streamVerifyAArch64, verPre]
      [verSat] using verSat)

theorem seal_verified (v : GcmImpl) :
    Verified AArch64.target («seal» v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.sealSig "work" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.sealPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost, sealAArch64, sealPre, onePub]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem open_verified (v : GcmImpl) :
    Verified AArch64.target («open» v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.openSig "work" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.openPost AArch64.abi.ptrBits) true 3264 (some (Spec.Sm4.Gcm.openLeak AArch64.abi.ptrBits))) :=
  Verified.of_correct (open_correct v) (open_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost, openAArch64, openPre, onePub, openRes, openLeakOf, Spec.Sm4.Gcm.openLeak, stackArg, stackArgAddr, Curry.app, Option.map]
      [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat)

end VG.Proof.Sm4Gcm.AArch64
