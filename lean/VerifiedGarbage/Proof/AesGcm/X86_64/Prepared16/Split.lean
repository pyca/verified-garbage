module

public import VerifiedGarbage.Spec.Gcm.Prepared16
public import VerifiedGarbage.Proof.Gcm.Prepared16Contract
public import VerifiedGarbage.Proof.Gcm.PreparedContract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Verified
public import VerifiedGarbage.Proof.AesGcm.ScratchSplit16
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/-! # Sixteen prepared powers: `seal_split` for a key context of `vg_aes_gcm_prepare16`

`sealSplitPrepared16_framed`: `Fast/Verified.lean`'s `sealSplitPrepared_framed`
for `Proof.Gcm.sealSplitPrepared16Contract`, the loops proven for the first
eight pairs (`CtxMode.prepared16`), with a one-pass loop that reads no
other (`hz`: not `StitchZHTo.encN`, which reads all 48 powers). -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts)

theorem splitPrepared16_implies : (Proof.AesGcm.sealSplitX86_64M CtxMode.prepared16).Implies
    (Proof.AesGcm.sealSplitPrepared16ScratchContract X86_64.abi 56) := by
  exact { pre := by sig_implies_pre [Proof.AesGcm.sealSplitPrepared16ScratchContract, Proof.AesGcm.sealSplitPreparedScratchSig, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPrepared16Pre,
      Proof.Gcm.sealSplitPost, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr]
          post := by sig_implies_post [Proof.AesGcm.sealSplitPrepared16ScratchContract, Proof.AesGcm.sealSplitPreparedScratchSig, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPrepared16Pre,
      Proof.Gcm.sealSplitPost, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr]
          pub := by sig_implies_pub [Proof.AesGcm.sealSplitPrepared16ScratchContract, Proof.AesGcm.sealSplitPreparedScratchSig, Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPrepared16Pre,
      Proof.Gcm.sealSplitPost, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.splitPre, Proof.AesGcm.onePub,
      X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk56, Proof.AesGcm.ret,
      Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
      VG.X86_64.below, X86_64.argRegs, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr]
          sat := ⟨splitSatP, by
            sig_pre [Proof.AesGcm.sealSplitPrepared16ScratchContract, Proof.AesGcm.sealSplitPreparedScratchSig,
              Proof.AesGcm.sealSplitPrecomputedScratchSig, Proof.Gcm.sealSplitPrepared16Pre, X86_64.abi,
              X86_64.argRegs, splitSatP, splitSat]
            sig_and_intros
            all_goals first
              | rfl
              | decide
              | (refine preparedPowers16Repr_of_zero fun i hi => ?_
                 split
                 · next h => exfalso; bv_omega
                 · rfl)
              | exact Region.disjoint_of_sep (by decide)⟩ }

theorem splitFrameSatPrepared16_pre : ∃ s, (Proof.Gcm.sealSplitPrepared16Contract X86_64.abi 2672).pre s := by
  refine ⟨splitFrameSatP, ?_⟩
  sig_pre [Proof.Gcm.sealSplitPrepared16Contract, Proof.Gcm.sealSplitPreparedSig, Proof.Gcm.sealSplitPrecomputedSig,
    Proof.Gcm.sealSplitPrepared16Pre, Proof.Gcm.sealSplitPost, X86_64.abi, X86_64.argRegs, splitFrameSatP,
    splitFrameSat, splitSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowers16Repr_of_zero fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)


section
variable (v : GcmImpl) (B : BlkFn CtxMode.prepared16) (T : BlkToFn CtxMode.prepared16)

theorem sealSplitPrepared16_core (hF : ShortFacts) (hz : ∀ n, v.onePass = some n → n ≠ .z) :
    Verified X86_64.target (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn))
      (Proof.AesGcm.sealSplitPrepared16ScratchContract X86_64.abi 56) :=
  Verified.of_correct (k := Proof.AesGcm.sealSplitX86_64M CtxMode.prepared16) (sealSplitR_correct v B T hF (fun n h hzn => absurd hzn (hz n h)))
    (sealSplitM_ct (splitMidR_ok v B T hF (fun n h hzn => absurd hzn (hz n h))) (splitMidR_rel v B T hF (fun n h hzn => absurd hzn (hz n h))))
    splitPrepared16_implies

/-- `vg_aes_gcm_seal_split_prepared`, in its frame. -/
theorem sealSplitPrepared16_framed (hF : ShortFacts) (hz : ∀ n, v.onePass = some n → n ≠ .z) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2616 5 (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn)))
      (Proof.Gcm.sealSplitPrepared16Contract X86_64.abi 2672) :=
  X86_64.Verified.stackArgScratch (sig := Proof.Gcm.sealSplitPreparedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.Gcm.sealSplitPrepared16Pre X86_64.abi.ptrBits)
    (post := Proof.Gcm.sealSplitPost X86_64.abi.ptrBits) (wa := true) (stack := 56)
    (bytes := 2616) (sealSplitPrepared16_core v B T hF hz) (by decide) (by decide) (by decide)
    (sealSplitR_spSafe v B T) (sealSplitR_xdepth v B T) (Proof.AesGcm.sealSplitPrepared16Pre_local _)
    (Proof.AesGcm.sealSplitPrecomputedPost_local _) splitFrameSatPrepared16_pre

end

end VG.Proof.AesGcm.X86_64.Split
