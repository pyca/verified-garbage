module
import Mathlib.Data.List.Dedup
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
public import VerifiedGarbage.Proof.Gcm.PreparedContract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call

import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.BlocksVerified
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.CT

/-! # Prepared-context BlocksTo contracts -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)

theorem blocksToPrepared_pre : ∀ s, (Proof.Gcm.encryptBlocksToPreparedContract X86_64.abi 24).pre s →
    (Proof.AesGcm.encryptBlocksToX86_64M Gcm.X86_64.Stitch.CtxMode.prepared).pre s := by
  intro s h
  sig_pre [Proof.Gcm.encryptBlocksToPreparedContract, Proof.Gcm.encryptBlocksToPreparedSig, Proof.Gcm.encryptBlocksToPrecomputedSig, Proof.Gcm.encryptBlocksToPreparedPre,
      Proof.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr] at h
  sig_split h
  sig_reduce [Proof.Gcm.encryptBlocksToPreparedContract, Proof.Gcm.encryptBlocksToPreparedSig, Proof.Gcm.encryptBlocksToPrecomputedSig, Proof.Gcm.encryptBlocksToPreparedPre,
      Proof.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr]
  sig_simp [Proof.Gcm.encryptBlocksToPreparedContract, Proof.Gcm.encryptBlocksToPreparedSig, Proof.Gcm.encryptBlocksToPrecomputedSig, Proof.Gcm.encryptBlocksToPreparedPre,
      Proof.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr] []
  sig_and_intros
  sig_close
  all_goals with_reducible assumption

theorem blocksToPrepared_implies : (Proof.AesGcm.encryptBlocksToX86_64M Gcm.X86_64.Stitch.CtxMode.prepared).Implies
    (Proof.Gcm.encryptBlocksToPreparedContract X86_64.abi 24) := by
  exact { pre := blocksToPrepared_pre
          post := by sig_implies_post [Proof.Gcm.encryptBlocksToPreparedContract, Proof.Gcm.encryptBlocksToPreparedSig, Proof.Gcm.encryptBlocksToPrecomputedSig, Proof.Gcm.encryptBlocksToPreparedPre,
      Proof.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr]
          pub := by sig_implies_pub [Proof.Gcm.encryptBlocksToPreparedContract, Proof.Gcm.encryptBlocksToPreparedSig, Proof.Gcm.encryptBlocksToPrecomputedSig, Proof.Gcm.encryptBlocksToPreparedPre,
      Proof.Gcm.encryptBlocksToPost, Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost,
      Proof.AesGcm.blocksToPreM, Proof.AesGcm.blocksToPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs,
      Gcm.X86_64.Stitch.CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr]
          sat := ⟨blocksToSatP, by
            sig_pre [Proof.Gcm.encryptBlocksToPreparedContract, Proof.Gcm.encryptBlocksToPreparedSig, Proof.Gcm.encryptBlocksToPrecomputedSig,
              Proof.Gcm.encryptBlocksToPreparedPre, X86_64.abi, X86_64.argRegs, blocksToSatP, blocksToSat]
            sig_and_intros
            all_goals first
              | rfl
              | decide
              | exact preparedPowersRepr_zero _
              | exact Region.disjoint_of_sep (by decide)⟩ }

theorem encryptBlocksToPrepared_verified (B : BlkFn CtxMode.prepared) (st : Option (StitchToCode CtxMode.prepared true)) :
    Verified X86_64.target (BlocksTo.encrypt B.enc (st.map (·.enc)) true (encFullTo st))
      (Proof.Gcm.encryptBlocksToPreparedContract X86_64.abi 24) :=
  Verified.of_correct (k := Proof.AesGcm.encryptBlocksToX86_64M CtxMode.prepared) (encryptToM_correct st B)
    (BlocksTo.encrypt_ct B st) blocksToPrepared_implies

end VG.Proof.AesGcm.X86_64
