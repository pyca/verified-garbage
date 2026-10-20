module
public import Mathlib.Data.List.Dedup
public import VerifiedGarbage.Impl.AesGcm.X86_64.SealFin
public import VerifiedGarbage.Impl.AesGcm.X86_64.FastSeal
public import VerifiedGarbage.Impl.AesGcm.X86_64.FastOpen
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Tab

import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.PowP
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.OpenSel
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.SealSel
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Mid
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.SealFin
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.KsA
import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP

/-!
# AES-GCM's short path on x86-64 with a prepared key context: the functions verified

Untrusted: everything here is checked by Lean. With a prepared key context,
`seal` and `open` take their powers from it (`Short.powersP`, `Short.ghashP`):
`sealMP_correct`, `openMP_correct`, as `sealM_correct` and `openM_correct`
for `powers`, and the code of the instances with the short path
(`GcmImpl.sealCodeP`, `GcmImpl.openCodeP`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

theorem sealShortP_xdepth :
    (Impl.AesGcm.X86_64.Short.sealShort Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP).x86_64Depth = 0 := by decide +kernel
theorem finishK_xdepth : (Impl.AesGcm.X86_64.Short.finishWith Impl.AesGcm.X86_64.Short.finKs).x86_64Depth = 0 :=
  finish_xdepth

theorem openShortP_xdepth :
    (Impl.AesGcm.X86_64.Short.openShort Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP).x86_64Depth = 0 := by decide +kernel

variable (v : GcmImpl) {M : CtxMode} (B : BlkFn M)

theorem sealMP_mx : (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.sealLong (v.withBlk B)))).allInstrs
    (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.Short.«seal», Impl.AesGcm.X86_64.Short.sealLong, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_mx, Fast.fastAad_mx, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealMP_spSafe : (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.sealLong (v.withBlk B)))).all
    (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.Short.«seal», Impl.AesGcm.X86_64.Short.sealLong, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_spSafe, Fast.fastAad_spSafe, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealMP_xdepth :
    (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.sealLong (v.withBlk B)))).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.Short.«seal», Impl.AesGcm.X86_64.Short.sealLong, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_xdepth, Fast.fastAad_xdepth, cond_xdepth, sealShortP_xdepth, finish_xdepth, finishK_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

theorem openMP_mx : (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B))) Impl.AesGcm.X86_64.Short.ghashP).allInstrs
    (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.Short.«open», Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Fast.fastCond_mx, Fast.fastAad_mx, FastOpen.tagP_mx, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openMP_spSafe : (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B))) Impl.AesGcm.X86_64.Short.ghashP).all
    (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.Short.«open», Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Fast.fastCond_spSafe, Fast.fastAad_spSafe, FastOpen.tagP_spSafe, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openMP_xdepth :
    (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B))) Impl.AesGcm.X86_64.Short.ghashP).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.Short.«open», Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Fast.fastCond_xdepth,
    Fast.fastAad_xdepth, FastOpen.tagP_xdepth, cond_xdepth, openShortP_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte,
    Bool.false_eq_true]
  omega

theorem sealFinP_mx : (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.SealFin.mid (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).allInstrs
    (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.SealFin.«seal», Impl.AesGcm.X86_64.SealFin.mid, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_mx, Fast.fastAad_mx, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealFinP_spSafe : (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.SealFin.mid (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).all
    (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.SealFin.«seal», Impl.AesGcm.X86_64.SealFin.mid, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_spSafe, Fast.fastAad_spSafe, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealFinP_xdepth : (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.SealFin.mid (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.SealFin.«seal», Impl.AesGcm.X86_64.SealFin.mid, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_xdepth, Fast.fastAad_xdepth, SealFin.finishA_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

theorem openFinP_mx : (Impl.AesGcm.X86_64.FastOpen.openFin
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).allInstrs
    (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.FastOpen.openFin, Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Fast.fastCond_mx, Fast.fastAad_mx, FastOpen.tagPA_mx, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openFinP_spSafe : (Impl.AesGcm.X86_64.FastOpen.openFin
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).all
    (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.FastOpen.openFin, Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Fast.fastCond_spSafe, Fast.fastAad_spSafe, FastOpen.tagPA_spSafe, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openFinP_xdepth : (Impl.AesGcm.X86_64.FastOpen.openFin
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.FastOpen.openFin, Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Fast.fastCond_xdepth, Fast.fastAad_xdepth, FastOpen.tagPA_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

section
variable (B : BlkFn CtxMode.prepared)

theorem sealMP_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.sealX86_64M CtxMode.prepared).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.sealLong (v.withBlk B)))) s t s' ∧
      abiPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sealMW_wp hF v B powOk_powersP
    (FastSeal.sealSel_ok hF v B finKs_ksOk (sealLongOk_sealLong hF v B)) hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealMP_mx v B) he hg, hp⟩

theorem sealFinP_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.sealX86_64M CtxMode.prepared).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.SealFin.mid (v.withBlk B))
        Impl.AesGcm.X86_64.Short.finKsA true)) s t s' ∧
      abiPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := SealFin.sealFMW_wp v B
    (FastSeal.sealSel_ok hF v B finKsA_ksOk (SealFin.sealLongOk_mid v B hF)) hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealFinP_mx v B) he hg, hp⟩

theorem openFinP_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.openX86_64M CtxMode.prepared).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.FastOpen.openFin
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B))
        Impl.AesGcm.X86_64.Short.finKsA true)) s t s' ∧
      abiPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := FastOpen.openFinW_wp (FastOpen.openSel_ok hF v B finKsA_ksOk (longOk_openLong v B)) hs
  exact ⟨t, s', he, abiPreserved_of_exec (openFinP_mx v B) he hg, hp⟩

theorem openMP_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.openX86_64M CtxMode.prepared).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B))) Impl.AesGcm.X86_64.Short.ghashP) s t s' ∧
      abiPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := openMW_wp hF v B powOk_powersP
    (FastOpen.openSel_ok hF v B finKs_ksOk (longOk_openLong v B)) hs
  exact ⟨t, s', he, abiPreserved_of_exec (openMP_mx v B) he hg, hp⟩

end

end VG.Proof.AesGcm.X86_64.Short

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

namespace GcmImpl

/-- `vg_aes_gcm_seal_prepared`'s code calling `c`: `sealCode`, with the short
path's table of powers from the prepared key context, and the path for TLS
records (`FastSeal.sel`) when the short path does not apply, or, ending
without calls, before `SealFin.mid`, at every length (`any`), since there
it is faster than `SealFin.mid` at every length. -/
def sealCodeP (v : GcmImpl) (c : Callees) : Prog isa :=
  if v.short then
    Impl.AesGcm.X86_64.Short.«seal» c Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP
      (Impl.AesGcm.X86_64.FastSeal.sel c (Impl.AesGcm.X86_64.Short.sealLong c))
  else if v.fin then
    Impl.AesGcm.X86_64.SealFin.«seal» c
      (Impl.AesGcm.X86_64.FastSeal.sel c (Impl.AesGcm.X86_64.SealFin.mid c) Impl.AesGcm.X86_64.Short.finKsA true)
  else «seal» c

/-- `vg_aes_gcm_open_prepared`'s code calling `c`: `openCode`, with the short
path's table of powers from the prepared key context, and the path for TLS
records (`FastOpen.sel`) when the short path does not apply; without the
short path, at every length (`any`), since it is faster there than the other
instances' body at every length. -/
def openCodeP (v : GcmImpl) (c : Callees) : Prog isa :=
  if v.short then
    Impl.AesGcm.X86_64.Short.«open» c Impl.AesGcm.X86_64.Short.powersP
      (Impl.AesGcm.X86_64.FastOpen.sel c (Impl.AesGcm.X86_64.Short.openLong c)) Impl.AesGcm.X86_64.Short.ghashP
  else
    Impl.AesGcm.X86_64.FastOpen.openFin
      (Impl.AesGcm.X86_64.FastOpen.sel c (Impl.AesGcm.X86_64.Short.openLong c) Impl.AesGcm.X86_64.Short.finKsA true)

end GcmImpl

variable (v : GcmImpl)

theorem sealCodeP_spSafe {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.sealCodeP (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.sealCodeP; split
  · exact Short.sealMP_spSafe v B
  · split
    · exact Short.sealFinP_spSafe v B
    · exact sealM_spSafe v B

theorem openCodeP_spSafe {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.openCodeP (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.openCodeP; split
  · exact Short.openMP_spSafe v B
  · exact Short.openFinP_spSafe v B

end VG.Proof.AesGcm.X86_64
