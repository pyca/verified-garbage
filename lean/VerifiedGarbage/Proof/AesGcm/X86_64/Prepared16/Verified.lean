module

public import VerifiedGarbage.Spec.Gcm.Prepared16

import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP
public import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
public import VerifiedGarbage.Proof.AesGcm.ScratchPrepared16
public import Mathlib.Data.List.Dedup
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.BlocksVerified
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.BlocksVerified
import VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCryptCT
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT

/-! # Sixteen prepared powers: Prepared-context sealing and streaming contracts -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

theorem preparedPowers16Repr_of_zero {m : Mem} {p : Addr} (h : ∀ i < 128 * 8, m (p + BitVec.ofNat 64 i) = 0) :
    Spec.Gcm.PreparedPowers16Repr m p :=
  Proof.AesGcm.preparedPowers16Repr_congr (m₁ := fun _ => 0) h (preparedPowers16Repr_zero p)

theorem sealPrepared16Code_verified {c : Prog isa}
    (hc : ∀ s, (Proof.AesGcm.sealX86_64M (CtxMode.preparedN 8)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s')
    (hct : ConstantTime isa (Proof.AesGcm.sealX86_64M (CtxMode.preparedN 8)).pre Proof.AesGcm.sealX86_64.pub c) :
    Verified X86_64.target c (Proof.AesGcm.sealPrepared16ScratchContract X86_64.abi 24) :=
  Verified.of_correct hc hct
    { pre := by
        sig_implies_pre [Proof.AesGcm.sealPrepared16ScratchContract, Proof.AesGcm.sealPreparedScratchSig, Proof.AesGcm.sealPrecomputedScratchSig,
          Spec.Gcm.sealPrepared16Pre, Spec.Gcm.sealPost, Proof.AesGcm.sealX86_64M, Proof.AesGcm.sealX86_64,
          Proof.AesGcm.sealPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr, X86_64.abi,
          Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by
        sig_implies_post [Proof.AesGcm.sealPrepared16ScratchContract, Proof.AesGcm.sealPreparedScratchSig, Proof.AesGcm.sealPrecomputedScratchSig,
          Spec.Gcm.sealPrepared16Pre, Spec.Gcm.sealPost, Proof.AesGcm.sealX86_64M, Proof.AesGcm.sealX86_64,
          Proof.AesGcm.sealPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr, X86_64.abi,
          Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by
        sig_implies_pub [Proof.AesGcm.sealPrepared16ScratchContract, Proof.AesGcm.sealPreparedScratchSig, Proof.AesGcm.sealPrecomputedScratchSig,
          Spec.Gcm.sealPrepared16Pre, Spec.Gcm.sealPost, Proof.AesGcm.sealX86_64M, Proof.AesGcm.sealX86_64,
          Proof.AesGcm.sealPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr, X86_64.abi,
          Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      sat := ⟨sealSatP, by
        sig_pre [Proof.AesGcm.sealPrepared16ScratchContract, Proof.AesGcm.sealPreparedScratchSig, Proof.AesGcm.sealPrecomputedScratchSig,
          Spec.Gcm.sealPrepared16Pre, X86_64.abi, X86_64.argRegs, sealSatP, sealSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | (refine preparedPowers16Repr_of_zero fun i hi => ?_
             split
             · next h => exfalso; bv_omega
             · rfl)⟩ }

theorem sealPrepared16_verified (v : GcmImpl) (B : BlkFn (CtxMode.preparedN 8)) :
    Verified X86_64.target («seal» (v.withBlk B)) (Proof.AesGcm.sealPrepared16ScratchContract X86_64.abi 24) :=
  sealPrepared16Code_verified (sealM_correct v B) (sealM_ct v B)

theorem openPrepared16Code_verified {c : Prog isa}
    (hc : ∀ s, (Proof.AesGcm.openX86_64M (CtxMode.preparedN 8)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s')
    (hct : ConstantTime isa (Proof.AesGcm.openX86_64M (CtxMode.preparedN 8)).pre Proof.AesGcm.openX86_64.pub c) :
    Verified X86_64.target c (Proof.AesGcm.openPrepared16ScratchContract X86_64.abi 24) :=
  Verified.of_correct hc hct
    { pre := by sig_implies_pre [Proof.AesGcm.openPrepared16ScratchContract, Proof.AesGcm.openPreparedScratchSig, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPrepared16Pre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.openPrepared16ScratchContract, Proof.AesGcm.openPreparedScratchSig, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPrepared16Pre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcm.openPrepared16ScratchContract, Proof.AesGcm.openPreparedScratchSig, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPrepared16Pre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesGcm.openPrepared16ScratchContract, Proof.AesGcm.openPreparedScratchSig, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPrepared16Pre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
        sig_simp [Proof.AesGcm.openPrepared16ScratchContract, Proof.AesGcm.openPreparedScratchSig, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPrepared16Pre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := ⟨openSatP, by
        sig_pre [Proof.AesGcm.openPrepared16ScratchContract, Proof.AesGcm.openPreparedScratchSig, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPrepared16Pre, X86_64.abi, X86_64.argRegs, openSatP, openSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact preparedPowers16Repr_of_zero fun _ _ => rfl⟩ }

theorem openPrepared16_verified (v : GcmImpl) (B : BlkFn (CtxMode.preparedN 8)) :
    Verified X86_64.target («open» (v.withBlk B)) (Proof.AesGcm.openPrepared16ScratchContract X86_64.abi 24) :=
  openPrepared16Code_verified (openM_correct v B) (openM_ct v B)

theorem streamEncryptPrepared16_verified (v : GcmImpl) (B : BlkFn (CtxMode.preparedN 8)) :
    Verified X86_64.target (streamEncrypt (v.withBlk B))
      (Proof.AesGcm.streamEncryptPrepared16ScratchContract X86_64.abi 24) :=
  Verified.of_correct (streamEncryptM_correct v B) (streamEncryptM_ct v B)
    { pre := by sig_implies_pre [Proof.AesGcm.streamEncryptPrepared16ScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamCryptPrepared16Pre, Spec.Gcm.streamEncryptPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.streamEncryptPrepared16ScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamCryptPrepared16Pre, Spec.Gcm.streamEncryptPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by sig_implies_pub [Proof.AesGcm.streamEncryptPrepared16ScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamCryptPrepared16Pre, Spec.Gcm.streamEncryptPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      sat := ⟨crSatP, by
        sig_pre [Proof.AesGcm.streamEncryptPrepared16ScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamCryptPrepared16Pre, X86_64.abi, X86_64.argRegs, crSatP, crSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact preparedPowers16Repr_of_zero fun _ _ => rfl⟩ }

theorem streamDecryptPrepared16_verified (v : GcmImpl) (B : BlkFn (CtxMode.preparedN 8)) :
    Verified X86_64.target (streamDecrypt (v.withBlk B))
      (Proof.AesGcm.streamDecryptPrepared16ScratchContract X86_64.abi 24) :=
  Verified.of_correct (streamDecryptM_correct v B) (streamDecryptM_ct v B)
    { pre := by sig_implies_pre [Proof.AesGcm.streamDecryptPrepared16ScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamCryptPrepared16Pre, Spec.Gcm.streamDecryptPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.streamDecryptPrepared16ScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamCryptPrepared16Pre, Spec.Gcm.streamDecryptPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by sig_implies_pub [Proof.AesGcm.streamDecryptPrepared16ScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamCryptPrepared16Pre, Spec.Gcm.streamDecryptPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      sat := ⟨crSatP, by
        sig_pre [Proof.AesGcm.streamDecryptPrepared16ScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamCryptPrepared16Pre, X86_64.abi, X86_64.argRegs, crSatP, crSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact preparedPowers16Repr_of_zero fun _ _ => rfl⟩ }

/-! ### With their working space on the stack -/

theorem sealFrameSatPrepared16_pre : ∃ s, (Spec.Gcm.sealPrepared16Contract X86_64.abi 2624).pre s := by
  refine ⟨sealFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.sealPrepared16Contract, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPrecomputedSig, Spec.Gcm.sealPrepared16Pre,
    Spec.Gcm.sealPost, X86_64.abi, X86_64.argRegs, sealFrameSatP, sealFrameSat, sealSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowers16Repr_of_zero fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)

theorem sealPrepared16Code_framed {c : Prog isa}
    (hv : Verified X86_64.target c (Proof.AesGcm.sealPrepared16ScratchContract X86_64.abi 24))
    (hsp : c.all (fun i => !X86_64.isa.writesSp i) = true) (hxd : c.x86_64Depth ≤ 24) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 c)
      (Spec.Gcm.sealPrepared16Contract X86_64.abi 2624) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.sealPreparedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealPrepared16Pre X86_64.abi.ptrBits)
    (post := Spec.Gcm.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2600) hv (by decide) (by decide) (by decide)
    hsp hxd (Proof.AesGcm.sealPrepared16Pre_local _)
    (Proof.AesGcm.sealPrecomputedPost_local _) sealFrameSatPrepared16_pre

theorem sealPrepared16_framed (v : GcmImpl) (B : BlkFn (CtxMode.preparedN 8)) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 («seal» (v.withBlk B)))
      (Spec.Gcm.sealPrepared16Contract X86_64.abi 2624) :=
  sealPrepared16Code_framed (sealPrepared16_verified v B) (sealM_spSafe v B) (sealM_xdepth v B)

theorem openFrameSatPrepared16_pre : ∃ s, (Spec.Gcm.openPrepared16Contract X86_64.abi 2632).pre s := by
  refine ⟨openFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.openPrepared16Contract, Spec.Gcm.openPreparedSig, Spec.Gcm.openPrecomputedSig, Spec.Gcm.openPrepared16Pre,
    Spec.Gcm.openPost, Spec.Gcm.openLeak, X86_64.abi, X86_64.argRegs, openFrameSatP, openFrameSat, openSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact preparedPowers16Repr_of_zero fun _ _ => rfl

theorem openPrepared16Code_framed {c : Prog isa}
    (hv : Verified X86_64.target c (Proof.AesGcm.openPrepared16ScratchContract X86_64.abi 24))
    (hsp : c.all (fun i => !X86_64.isa.writesSp i) = true) (hxd : c.x86_64Depth ≤ 24) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 c)
      (Spec.Gcm.openPrepared16Contract X86_64.abi 2632) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.openPreparedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openPrepared16Pre X86_64.abi.ptrBits)
    (post := Spec.Gcm.openPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (leak := some (Spec.Gcm.openLeak X86_64.abi.ptrBits)) (bytes := 2608) hv
    (by decide) (by decide) (by decide) hsp hxd
    (Proof.AesGcm.openPrepared16Pre_local _) (Proof.AesGcm.openPrecomputedPost_local _) openFrameSatPrepared16_pre
    (hleak := Proof.AesGcm.openPrecomputedLeak_local _)

theorem openPrepared16_framed (v : GcmImpl) (B : BlkFn (CtxMode.preparedN 8)) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («open» (v.withBlk B)))
      (Spec.Gcm.openPrepared16Contract X86_64.abi 2632) :=
  openPrepared16Code_framed (openPrepared16_verified v B) (openM_spSafe v B) (openM_xdepth v B)

theorem streamEncryptFrameSatPrepared16_pre : ∃ s, (Spec.Gcm.streamEncryptPrepared16Contract X86_64.abi 2608).pre s := by
  refine ⟨crFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.streamEncryptPrepared16Contract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrecomputedSig,
    Spec.Gcm.streamCryptPrepared16Pre, Spec.Gcm.streamEncryptPost, X86_64.abi, X86_64.argRegs, crFrameSatP, crFrameSat,
    crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact preparedPowers16Repr_of_zero fun _ _ => rfl

theorem streamEncryptPrepared16_framed (v : GcmImpl) (B : BlkFn (CtxMode.preparedN 8)) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncrypt (v.withBlk B)))
      (Spec.Gcm.streamEncryptPrepared16Contract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamCryptPreparedSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamCryptPrepared16Pre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamEncryptPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamEncryptPrepared16_verified v B) (by decide) (by decide) (by decide)
    (streamEncryptM_spSafe v B) (streamEncryptM_xdepth v B) (Proof.AesGcm.streamCryptPrepared16Pre_local _)
    (Proof.AesGcm.streamEncryptPrecomputedPost_local _) streamEncryptFrameSatPrepared16_pre

theorem streamDecryptFrameSatPrepared16_pre : ∃ s, (Spec.Gcm.streamDecryptPrepared16Contract X86_64.abi 2608).pre s := by
  refine ⟨crFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.streamDecryptPrepared16Contract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrecomputedSig,
    Spec.Gcm.streamCryptPrepared16Pre, Spec.Gcm.streamDecryptPost, X86_64.abi, X86_64.argRegs, crFrameSatP, crFrameSat,
    crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact preparedPowers16Repr_of_zero fun _ _ => rfl

theorem streamDecryptPrepared16_framed (v : GcmImpl) (B : BlkFn (CtxMode.preparedN 8)) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecrypt (v.withBlk B)))
      (Spec.Gcm.streamDecryptPrepared16Contract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamCryptPreparedSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamCryptPrepared16Pre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamDecryptPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamDecryptPrepared16_verified v B) (by decide) (by decide) (by decide)
    (streamDecryptM_spSafe v B) (streamDecryptM_xdepth v B) (Proof.AesGcm.streamCryptPrepared16Pre_local _)
    (Proof.AesGcm.streamDecryptPrecomputedPost_local _) streamDecryptFrameSatPrepared16_pre

end VG.Proof.AesGcm.X86_64
