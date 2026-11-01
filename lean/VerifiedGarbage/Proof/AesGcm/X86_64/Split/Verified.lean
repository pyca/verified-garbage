module

import VerifiedGarbage.Proof.AesGcm.X86_64.Split.ShortCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.End
public import VerifiedGarbage.Proof.Gcm.PreparedContract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
public import VerifiedGarbage.Proof.AesGcm.ScratchSplit
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
import Mathlib.Data.List.Dedup
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.ShortRun
import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/-!
# AES-GCM `seal_split` on x86-64: `Verified`

Untrusted: everything here is checked by Lean. `seal_split` calling any
`vg_aes_gcm_encrypt_blocks_to` `T` (`BlkToFn`) loads no `mxcsr`, writes
`rsp` only in its frames and uses 56 bytes of stack (the call's arguments,
its return address and its stack), so it preserves what the ABI says; it
meets the shared contracts with a `work` buffer appended
(`sealSplitScratchContract`, …), and the shared contracts of
`Spec/Gcm/OutOfPlace.lean` and `Spec/Gcm/Prepared.lean` in a frame of 2616
bytes holding the working space (`Verified.stackArgScratch`): its 2560
bytes, a copy of the five other stack arguments, and 16 more, for 2672 bytes
of stack in all; for the key contexts of `vg_aes_gcm_init`,
`vg_aes_gcm_init_precomputed` and `vg_aes_gcm_prepare`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts)

/-- `seal_split`'s code after the entry for the implementations `v`: with
`seal`'s short path if they have it. -/
def _root_.VG.Proof.AesGcm.X86_64.GcmImpl.splitMid (v : GcmImpl) (c : Callees) (fTo : Fn) : Prog isa :=
  if v.short then SealSplit.runShort c fTo v.splitFin else SealSplit.run c fTo v.splitFin

theorem cond_mx : (Short.cond : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel
theorem cond_spSafe : (Short.cond : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by decide +kernel
theorem cond_xdepth : (Short.cond : Prog isa).x86_64Depth = 0 := by decide +kernel
theorem copySrc_mx : (SealSplit.copySrc : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel
theorem copySrc_spSafe : (SealSplit.copySrc : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel
theorem copySrc_xdepth : (SealSplit.copySrc : Prog isa).x86_64Depth = 0 := by decide +kernel
theorem sealShort_mx : (Short.sealShort : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel
theorem sealShort_spSafe : (Short.sealShort : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel
theorem sealShort_xdepth : (Short.sealShort : Prog isa).x86_64Depth = 0 := by decide +kernel

section
variable (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToFn M)

theorem run_mx :
    (SealSplit.run (v.withBlk B) T.fn v.splitFin).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  have f := splitFin_mx v
  simp only [e, d, f, T.mx, SealSplit.run, SealSplit.«prefix», SealSplit.body, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem run_spSafe :
    (SealSplit.run (v.withBlk B) T.fn v.splitFin).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  have f := splitFin_spSafe v
  simp only [e, d, f, T.spAll, SealSplit.run, SealSplit.«prefix», SealSplit.body, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem run_xdepth : (SealSplit.run (v.withBlk B) T.fn v.splitFin).x86_64Depth ≤ 56 := by
  have e := B.encXd
  have d := B.decXd
  have t := T.xd
  have f := splitFin_xdepth v
  simp only [SealSplit.run, SealSplit.«prefix», SealSplit.body, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp,
    tagOut, copyTag, copyLoop, xorLoop, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes,
    List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees, v.ctr.noStack, v.key.noStack,
    v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

theorem splitMid_mx : (v.splitMid (v.withBlk B) T.fn).allInstrs (fun i => !loadsMxcsr i) = true := by
  unfold GcmImpl.splitMid; split
  · simp only [SealSplit.runShort, Code.allInstrs]
    rw [cond_mx, run_mx v B T, copySrc_mx, sealShort_mx]; rfl
  · exact run_mx v B T

theorem splitMid_spSafe : (v.splitMid (v.withBlk B) T.fn).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.splitMid; split
  · simp only [SealSplit.runShort, Code.all]
    rw [cond_spSafe, run_spSafe v B T, copySrc_spSafe, sealShort_spSafe]; rfl
  · exact run_spSafe v B T

theorem splitMid_xdepth : (v.splitMid (v.withBlk B) T.fn).x86_64Depth ≤ 56 := by
  unfold GcmImpl.splitMid; split
  · have := run_xdepth v B T
    simp only [SealSplit.runShort, Code.x86_64Depth, cond_xdepth, copySrc_xdepth, sealShort_xdepth, Nat.max_le]
    omega
  · exact run_xdepth v B T

theorem splitMid_ok (hF : ShortFacts) : MidOk M (v.splitMid (v.withBlk B) T.fn) := by
  unfold GcmImpl.splitMid; split
  · exact runShort_ok hF v B T (splitFin_ok v hF)
  · exact splitRun_ok v B T (splitFin_ok v hF)

theorem splitMid_rel (hF : ShortFacts) : MidRel M (v.splitMid (v.withBlk B) T.fn) := by
  unfold GcmImpl.splitMid; split
  · exact runShort_rel hF v B T (splitFin_rel v hF)
  · exact splitRun_rel v B T (splitFin_rel v hF)

theorem sealSplit_mx :
    (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [SealSplit.«seal», Code.allInstrs]
  rw [splitMid_mx v B T]; rfl

theorem sealSplit_spSafe :
    (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn)).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [SealSplit.«seal», Code.all]
  rw [splitMid_spSafe v B T]; rfl

theorem sealSplit_xdepth : (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn)).x86_64Depth ≤ 56 := by
  have := splitMid_xdepth v B T
  simp only [SealSplit.«seal», Code.x86_64Depth, tagOut, Nat.max_le]
  omega

theorem sealSplit_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.sealSplitX86_64M M).pre s) :
    ∃ t s', Exec isa (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn)) s t s' ∧ abiPreserved s s' ∧
      (Proof.AesGcm.sealSplitX86_64M M).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sealSplitM_wp (splitMid_ok v B T hF) hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealSplit_mx v B T) he hg, hp⟩

end

/-! ## The contracts -/

/-- A state satisfying the precondition of `vg_aes_gcm_seal_split` with its
working space (with no data and empty `src`, and `dst` and `work` at 0). -/
def splitSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8029 then 0x30 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 48⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0, 2560⟩]

/-- `splitSat`, with a key context of 1024 bytes. -/
def splitSatP : State := { splitSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 48⟩] }

theorem split_implies : (Proof.AesGcm.sealSplitX86_64M CtxMode.base).Implies
    (Proof.AesGcm.sealSplitScratchContract X86_64.abi 56) := by
  sig_implies [Proof.AesGcm.sealSplitScratchContract, Proof.AesGcm.sealSplitScratchSig, Proof.Gcm.sealSplitPre,
      Proof.Gcm.sealSplitPost, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.base] [splitSat] using splitSat

theorem splitP_implies : (Proof.AesGcm.sealSplitX86_64M CtxMode.powers).Implies
    (Proof.AesGcm.sealSplitPrecomputedScratchContract X86_64.abi 56) := by
  exact { pre := by sig_implies_pre [Proof.AesGcm.sealSplitPrecomputedScratchContract, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPrecomputedPre,
      Proof.Gcm.sealSplitPost, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.powers]
          post := by sig_implies_post [Proof.AesGcm.sealSplitPrecomputedScratchContract, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPrecomputedPre,
      Proof.Gcm.sealSplitPost, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.powers]
          pub := by sig_implies_pub [Proof.AesGcm.sealSplitPrecomputedScratchContract, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPrecomputedPre,
      Proof.Gcm.sealSplitPost, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.powers]
          sat := ⟨splitSatP, by
            sig_pre [Proof.AesGcm.sealSplitPrecomputedScratchContract, Proof.AesGcm.sealSplitPrecomputedScratchSig,
              Proof.Gcm.sealSplitPrecomputedPre, X86_64.abi, X86_64.argRegs, splitSatP, splitSat]
            sig_and_intros
            all_goals first
              | rfl
              | decide
              | (refine powersRepr_of_zero fun i hi => ?_
                 split
                 · next h => exfalso; bv_omega
                 · rfl)
              | exact Region.disjoint_of_sep (by decide)⟩ }

theorem splitPrepared_implies : (Proof.AesGcm.sealSplitX86_64M CtxMode.prepared).Implies
    (Proof.AesGcm.sealSplitPreparedScratchContract X86_64.abi 56) := by
  exact { pre := by sig_implies_pre [Proof.AesGcm.sealSplitPreparedScratchContract, Proof.AesGcm.sealSplitPreparedScratchSig, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPreparedPre,
      Proof.Gcm.sealSplitPost, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr]
          post := by sig_implies_post [Proof.AesGcm.sealSplitPreparedScratchContract, Proof.AesGcm.sealSplitPreparedScratchSig, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPreparedPre,
      Proof.Gcm.sealSplitPost, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr]
          pub := by sig_implies_pub [Proof.AesGcm.sealSplitPreparedScratchContract, Proof.AesGcm.sealSplitPreparedScratchSig, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPreparedPre,
      Proof.Gcm.sealSplitPost, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr]
          sat := ⟨splitSatP, by
            sig_pre [Proof.AesGcm.sealSplitPreparedScratchContract, Proof.AesGcm.sealSplitPreparedScratchSig,
              Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPreparedPre, X86_64.abi,
              X86_64.argRegs, splitSatP, splitSat]
            sig_and_intros
            all_goals first
              | rfl
              | decide
              | (refine preparedPowersRepr_of_zero fun i hi => ?_
                 split
                 · next h => exfalso; bv_omega
                 · rfl)
              | exact Region.disjoint_of_sep (by decide)⟩ }

section
variable (v : GcmImpl) (hF : ShortFacts)
include hF

theorem sealSplit_core (B : BlkFn CtxMode.base) (T : BlkToFn CtxMode.base) :
    Verified X86_64.target (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn)) (Proof.AesGcm.sealSplitScratchContract X86_64.abi 56) :=
  Verified.of_correct (k := Proof.AesGcm.sealSplitX86_64M CtxMode.base) (sealSplit_correct v B T hF)
    (sealSplitM_ct (splitMid_ok v B T hF) (splitMid_rel v B T hF)) split_implies

theorem sealSplitP_core (B : BlkFn CtxMode.powers) (T : BlkToFn CtxMode.powers) :
    Verified X86_64.target (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn))
      (Proof.AesGcm.sealSplitPrecomputedScratchContract X86_64.abi 56) :=
  Verified.of_correct (k := Proof.AesGcm.sealSplitX86_64M CtxMode.powers) (sealSplit_correct v B T hF)
    (sealSplitM_ct (splitMid_ok v B T hF) (splitMid_rel v B T hF)) splitP_implies

end

/-! ## In its frame -/

/-- A state satisfying the precondition of `vg_aes_gcm_seal_split`, without
the working space. -/
def splitFrameSat : State :=
  { splitSat with
    rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 40⟩], wr := [⟨0, 0⟩, ⟨0x3000, 16⟩] }

/-- `splitFrameSat`, with a key context of 1024 bytes. -/
def splitFrameSatP : State :=
  { splitFrameSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 40⟩] }

theorem splitFrameSat_pre : ∃ s, (Proof.Gcm.sealSplitContract X86_64.abi 2672).pre s := by
  implies_sat [Proof.Gcm.sealSplitContract, Proof.Gcm.sealSplitSig, Proof.Gcm.sealSplitPre, Proof.Gcm.sealSplitPost,
    X86_64.abi, X86_64.argRegs] [splitFrameSat, splitSat] using splitFrameSat

theorem splitFrameSatP_pre : ∃ s, (Proof.Gcm.sealSplitPrecomputedContract X86_64.abi 2672).pre s := by
  refine ⟨splitFrameSatP, ?_⟩
  sig_pre [Proof.Gcm.sealSplitPrecomputedContract, Proof.Gcm.sealSplitPrecomputedSig, Proof.Gcm.sealSplitPrecomputedPre,
    Proof.Gcm.sealSplitPost, X86_64.abi, X86_64.argRegs, splitFrameSatP, splitFrameSat, splitSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine powersRepr_of_zero fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)

theorem splitFrameSatPrepared_pre : ∃ s, (Proof.Gcm.sealSplitPreparedContract X86_64.abi 2672).pre s := by
  refine ⟨splitFrameSatP, ?_⟩
  sig_pre [Proof.Gcm.sealSplitPreparedContract, Proof.Gcm.sealSplitPreparedSig, Proof.Gcm.sealSplitPrecomputedSig,
    Proof.Gcm.sealSplitPreparedPre, Proof.Gcm.sealSplitPost, X86_64.abi, X86_64.argRegs, splitFrameSatP,
    splitFrameSat, splitSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowersRepr_of_zero fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)

section
variable (v : GcmImpl) (hF : ShortFacts)
include hF

theorem sealSplit_framed (B : BlkFn CtxMode.base) (T : BlkToFn CtxMode.base) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2616 5 (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn)))
      (Proof.Gcm.sealSplitContract X86_64.abi 2672) :=
  X86_64.Verified.stackArgScratch (sig := Proof.Gcm.sealSplitSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.Gcm.sealSplitPre X86_64.abi.ptrBits)
    (post := Proof.Gcm.sealSplitPost X86_64.abi.ptrBits) (wa := true) (stack := 56)
    (bytes := 2616) (sealSplit_core v hF B T) (by decide) (by decide) (by decide)
    (sealSplit_spSafe v B T) (sealSplit_xdepth v B T) (Proof.AesGcm.sealSplitPre_local _)
    (Proof.AesGcm.sealSplitPost_local _) splitFrameSat_pre

theorem sealSplitP_framed (B : BlkFn CtxMode.powers) (T : BlkToFn CtxMode.powers) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2616 5 (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn)))
      (Proof.Gcm.sealSplitPrecomputedContract X86_64.abi 2672) :=
  X86_64.Verified.stackArgScratch (sig := Proof.Gcm.sealSplitPrecomputedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.Gcm.sealSplitPrecomputedPre X86_64.abi.ptrBits)
    (post := Proof.Gcm.sealSplitPost X86_64.abi.ptrBits) (wa := true) (stack := 56)
    (bytes := 2616) (sealSplitP_core v hF B T) (by decide) (by decide) (by decide)
    (sealSplit_spSafe v B T) (sealSplit_xdepth v B T) (Proof.AesGcm.sealSplitPrecomputedPre_local _)
    (Proof.AesGcm.sealSplitPrecomputedPost_local _) splitFrameSatP_pre

end

end VG.Proof.AesGcm.X86_64.Split
