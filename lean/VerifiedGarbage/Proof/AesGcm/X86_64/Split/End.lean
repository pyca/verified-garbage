module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.FinCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Fin
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.SealFin
import Mathlib.Data.List.Dedup
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.KsA

/-!
# AES-GCM `seal_split` on x86-64: the end of each instance

Untrusted: everything here is checked by Lean. `seal_split` ends as its
instance's `seal` does (`GcmImpl.splitFin`): with the keystream in `zmm5`
for the instances with the short path (`Short.finish`), in `xmm` registers
for those ending without calls (`Short.finishWith Short.finKsA`), and
otherwise with `oneCrypt` and `oneTag 0` (`SealSplit.finCalls`); and what
correctness (`splitFin_ok`), constant time (`splitFin_rel`) and the static
facts need of it.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts finKs_ksOk finKs_rel finKsA_ksOk finKsA_rel)

/-- The end of `seal_split` of the implementations `v`, as their `seal`'s. -/
def _root_.VG.Proof.AesGcm.X86_64.GcmImpl.splitFin (v : GcmImpl) : Prog isa :=
  if v.short then Short.finish else if v.fin then Short.finishWith Short.finKsA else SealSplit.finCalls v.callees

variable (v : GcmImpl)

theorem splitFin_ok (hF : ShortFacts) {M : CtxMode} : FinOk M v.splitFin := by
  unfold GcmImpl.splitFin; split
  · exact finOk_finishWith hF finKs_ksOk
  · split
    · exact finOk_finishWith hF finKsA_ksOk
    · exact finCalls_ok v

theorem splitFin_rel (hF : ShortFacts) {M : CtxMode} : FinRel M v.splitFin := by
  unfold GcmImpl.splitFin; split
  · exact finRel_finishWith hF finKs_ksOk finKs_rel
  · split
    · exact finRel_finishWith hF finKsA_ksOk finKsA_rel
    · exact finRel_calls v

theorem finCalls_mx : (SealSplit.finCalls v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [SealSplit.finCalls, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo,
    Code.allInstrs, GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem finCalls_spSafe : (SealSplit.finCalls v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [SealSplit.finCalls, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo,
    Code.all, GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem finCalls_xdepth : (SealSplit.finCalls v.callees).x86_64Depth ≤ 24 := by
  simp only [SealSplit.finCalls, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, tagLenOk, recv,
    Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

theorem finish_mx : (Short.finish : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel
theorem finish_spSafe : (Short.finish : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by decide +kernel
theorem finish_xdepth : (Short.finish : Prog isa).x86_64Depth = 0 := by decide +kernel
theorem finishA_mx : (Short.finishWith Short.finKsA : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel
theorem finishA_spSafe : (Short.finishWith Short.finKsA : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel

theorem splitFin_mx : v.splitFin.allInstrs (fun i => !loadsMxcsr i) = true := by
  unfold GcmImpl.splitFin; split
  · exact finish_mx
  · split
    · exact finishA_mx
    · exact finCalls_mx v

theorem splitFin_spSafe : v.splitFin.all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.splitFin; split
  · exact finish_spSafe
  · split
    · exact finishA_spSafe
    · exact finCalls_spSafe v

theorem splitFin_xdepth : v.splitFin.x86_64Depth ≤ 24 := by
  unfold GcmImpl.splitFin; split
  · rw [finish_xdepth]; decide
  · split
    · rw [SealFin.finishA_xdepth]; decide
    · exact finCalls_xdepth v

end VG.Proof.AesGcm.X86_64.Split
