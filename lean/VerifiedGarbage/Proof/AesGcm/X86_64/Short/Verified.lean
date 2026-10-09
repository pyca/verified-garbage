import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP

/-!
# AES-GCM's short path on x86-64: the functions verified

Untrusted: everything here is checked by Lean. `seal` and `open` with the
short path load no `mxcsr`, never write `rsp` and use as much stack as the
other instances (the short path's code and the end of the long `seal` use none: `cond_xdepth`,
`sealShort_xdepth`, `openShort_xdepth`, `finish_xdepth`), and so they preserve what the ABI
says (`sealM_correct`, `openM_correct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

theorem cond_xdepth : Impl.AesGcm.X86_64.Short.cond.x86_64Depth = 0 := by decide +kernel
theorem sealShort_xdepth : Impl.AesGcm.X86_64.Short.sealShort.x86_64Depth = 0 := by decide +kernel
theorem openShort_xdepth : Impl.AesGcm.X86_64.Short.openShort.x86_64Depth = 0 := by decide +kernel
theorem finish_xdepth : Impl.AesGcm.X86_64.Short.finish.x86_64Depth = 0 := by decide +kernel

variable (v : GcmImpl) {M : CtxMode} (B : BlkFn M)

theorem sealM_mx : (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.Short.«seal», init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealM_spSafe : (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.Short.«seal», init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealM_xdepth : (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.Short.«seal», cond_xdepth, sealShort_xdepth, finish_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyLoop, xorLoop, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

theorem sealM_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.sealX86_64M M).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sealM_wp hF v B hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealM_mx v B) he hg, hp⟩

theorem openM_mx : (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.Short.«open», init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openM_spSafe : (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.Short.«open», init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openM_xdepth : (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.Short.«open», cond_xdepth, openShort_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyLoop, xorLoop, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte,
    Bool.false_eq_true]
  omega

theorem openM_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.openX86_64M M).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := openM_wp hF v B hs
  exact ⟨t, s', he, abiPreserved_of_exec (openM_mx v B) he hg, hp⟩

end VG.Proof.AesGcm.X86_64.Short

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

namespace GcmImpl

/-- `vg_aes_gcm_seal`'s code calling `c`, with the short path if `v` has it. -/
def sealCode (v : GcmImpl) (c : Callees) : Prog isa :=
  if v.short then Impl.AesGcm.X86_64.Short.«seal» c else «seal» c

/-- `vg_aes_gcm_open`'s code calling `c`, with the short path if `v` has it. -/
def openCode (v : GcmImpl) (c : Callees) : Prog isa :=
  if v.short then Impl.AesGcm.X86_64.Short.«open» c else «open» c

end GcmImpl

variable (v : GcmImpl)

theorem sealCode_spSafe {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.sealCode (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.sealCode; split
  · exact Short.sealM_spSafe v B
  · exact sealM_spSafe v B

theorem openCode_spSafe {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.openCode (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.openCode; split
  · exact Short.openM_spSafe v B
  · exact openM_spSafe v B

/-- `vg_aes_gcm_seal`, with the short path if `v` has it. -/
theorem sealSel_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode v.callees))
      (Spec.Gcm.sealContract X86_64.abi 2624) := by
  unfold GcmImpl.sealCode; split
  · exact sealCode_framed (sealCode_verified (fun s hs => Short.sealM_correct v v.blkB hF s ⟨hs, trivial⟩)
      (ct_of_rel fun _ _ hp hp' hq => Short.sealM_rel hF v v.blkB ⟨hp, trivial⟩ ⟨hp', trivial⟩ hq))
      (Short.sealM_spSafe v v.blkB) (Short.sealM_xdepth v v.blkB)
  · exact seal_framed v

/-- `vg_aes_gcm_open`, with the short path if `v` has it. -/
theorem openSel_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCode v.callees))
      (Spec.Gcm.openContract X86_64.abi 2632) := by
  unfold GcmImpl.openCode; split
  · exact openCode_framed (openCode_verified (fun s hs => Short.openM_correct v v.blkB hF s ⟨hs, trivial⟩)
      (ct_of_rel fun _ _ hp hp' hq => Short.openM_rel hF v v.blkB ⟨hp, trivial⟩ ⟨hp', trivial⟩ hq))
      (Short.openM_spSafe v v.blkB) (Short.openM_xdepth v v.blkB)
  · exact open_framed v

/-- `vg_aes_gcm_seal_precomputed`, with the short path if `v` has it. -/
theorem sealSelP_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode (v.withBlk v.blkP)))
      (Spec.Gcm.sealPrecomputedContract X86_64.abi 2624) := by
  unfold GcmImpl.sealCode; split
  · exact sealPCode_framed (sealPCode_verified (Short.sealM_correct v v.blkP hF) (Short.sealM_ct hF v v.blkP))
      (Short.sealM_spSafe v v.blkP) (Short.sealM_xdepth v v.blkP)
  · exact sealP_framed v

/-- `vg_aes_gcm_open_precomputed`, with the short path if `v` has it. -/
theorem openSelP_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCode (v.withBlk v.blkP)))
      (Spec.Gcm.openPrecomputedContract X86_64.abi 2632) := by
  unfold GcmImpl.openCode; split
  · exact openPCode_framed (openPCode_verified (Short.openM_correct v v.blkP hF) (Short.openM_ct hF v v.blkP))
      (Short.openM_spSafe v v.blkP) (Short.openM_xdepth v v.blkP)
  · exact openP_framed v

end VG.Proof.AesGcm.X86_64
