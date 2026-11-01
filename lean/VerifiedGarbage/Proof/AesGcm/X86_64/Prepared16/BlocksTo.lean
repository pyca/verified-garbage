module

public import VerifiedGarbage.Spec.Gcm.Prepared16
public import VerifiedGarbage.Proof.Gcm.Prepared16Contract
public import VerifiedGarbage.Proof.Gcm.PreparedContract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
import Mathlib.Data.List.Dedup
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call

import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.BlocksVerified
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.CT

/-! # Sixteen prepared powers: Prepared-context BlocksTo contracts -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)

theorem blocksToPrepared16_pre : ∀ s, (Proof.Gcm.encryptBlocksToPrepared16Contract X86_64.abi 24).pre s →
    (Proof.AesGcm.encryptBlocksToX86_64M Gcm.X86_64.Stitch.CtxMode.prepared16).pre s := by
  intro s h
  sig_pre [Proof.Gcm.encryptBlocksToPrepared16Contract, Proof.Gcm.encryptBlocksToPreparedSig, Proof.Gcm.encryptBlocksToPrecomputedSig, Proof.Gcm.encryptBlocksToPrepared16Pre,
      Proof.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.prepared16, Gcm.X86_64.Stitch.CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr] at h
  sig_split h
  sig_reduce [Proof.Gcm.encryptBlocksToPrepared16Contract, Proof.Gcm.encryptBlocksToPreparedSig, Proof.Gcm.encryptBlocksToPrecomputedSig, Proof.Gcm.encryptBlocksToPrepared16Pre,
      Proof.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.prepared16, Gcm.X86_64.Stitch.CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr]
  sig_simp [Proof.Gcm.encryptBlocksToPrepared16Contract, Proof.Gcm.encryptBlocksToPreparedSig, Proof.Gcm.encryptBlocksToPrecomputedSig, Proof.Gcm.encryptBlocksToPrepared16Pre,
      Proof.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.prepared16, Gcm.X86_64.Stitch.CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr] []
  sig_and_intros
  sig_close
  all_goals with_reducible assumption

theorem blocksToPrepared16_implies : (Proof.AesGcm.encryptBlocksToX86_64M Gcm.X86_64.Stitch.CtxMode.prepared16).Implies
    (Proof.Gcm.encryptBlocksToPrepared16Contract X86_64.abi 24) := by
  exact { pre := blocksToPrepared16_pre
          post := by sig_implies_post [Proof.Gcm.encryptBlocksToPrepared16Contract, Proof.Gcm.encryptBlocksToPreparedSig, Proof.Gcm.encryptBlocksToPrecomputedSig, Proof.Gcm.encryptBlocksToPrepared16Pre,
      Proof.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.prepared16, Gcm.X86_64.Stitch.CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr]
          pub := by sig_implies_pub [Proof.Gcm.encryptBlocksToPrepared16Contract, Proof.Gcm.encryptBlocksToPreparedSig, Proof.Gcm.encryptBlocksToPrecomputedSig, Proof.Gcm.encryptBlocksToPrepared16Pre,
      Proof.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.prepared16, Gcm.X86_64.Stitch.CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr]
          sat := ⟨blocksToSatP, by
            sig_pre [Proof.Gcm.encryptBlocksToPrepared16Contract, Proof.Gcm.encryptBlocksToPreparedSig, Proof.Gcm.encryptBlocksToPrecomputedSig,
              Proof.Gcm.encryptBlocksToPrepared16Pre, X86_64.abi, X86_64.argRegs, blocksToSatP, blocksToSat]
            sig_and_intros
            all_goals first
              | rfl
              | decide
              | exact preparedPowers16Repr_zero _
              | exact Region.disjoint_of_sep (by decide)⟩ }

theorem encryptBlocksToPrepared16_verified (B : BlkFn CtxMode.prepared16) (st : Option (StitchToCode CtxMode.prepared16 true)) :
    Verified X86_64.target (BlocksTo.encrypt B.enc (st.map (·.enc)) true (encFullTo st))
      (Proof.Gcm.encryptBlocksToPrepared16Contract X86_64.abi 24) :=
  Verified.of_correct (k := Proof.AesGcm.encryptBlocksToX86_64M CtxMode.prepared16) (encryptToM_correct st B)
    (BlocksTo.encrypt_ct B st) blocksToPrepared16_implies

end VG.Proof.AesGcm.X86_64
