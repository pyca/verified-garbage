module

public import VerifiedGarbage.Spec.Gcm.Prepared16
public import VerifiedGarbage.Proof.Gcm.Prepared16Contract
public import VerifiedGarbage.Proof.Gcm.PreparedContract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract

import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Verified
import VerifiedGarbage.Proof.AesGcm.ScratchPreparedTo
public import VerifiedGarbage.Proof.AesGcm.ScratchPrepared16To
public import VerifiedGarbage.Impl.AesGcm.X86_64.StreamTo
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Callee
import Mathlib.Data.List.Dedup
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.AesGcm.ScratchTo
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Contract

/-! # Sixteen prepared powers: Prepared-context StreamTo contracts -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.StreamTo
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)
open VG.Impl.AesGcm.X86_64.StreamTo

theorem streamToPrepared16_implies : (Proof.AesGcm.streamEncryptToX86_64M CtxMode.prepared16).Implies
    (Proof.AesGcm.streamEncryptToPrepared16ScratchContract X86_64.abi 2624) := by
  exact { pre := by sig_implies_pre [Proof.AesGcm.streamEncryptToPrepared16ScratchContract,
      Proof.AesGcm.streamEncryptToPreparedScratchSig, Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Proof.Gcm.streamEncryptToPrepared16Pre,
      Proof.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr]
          post := by sig_implies_post [Proof.AesGcm.streamEncryptToPrepared16ScratchContract,
      Proof.AesGcm.streamEncryptToPreparedScratchSig, Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Proof.Gcm.streamEncryptToPrepared16Pre,
      Proof.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr]
          pub := by sig_implies_pub [Proof.AesGcm.streamEncryptToPrepared16ScratchContract,
      Proof.AesGcm.streamEncryptToPreparedScratchSig, Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Proof.Gcm.streamEncryptToPrepared16Pre,
      Proof.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr]
          sat := ⟨streamToSatP, by
            sig_pre [Proof.AesGcm.streamEncryptToPrepared16ScratchContract,
              Proof.AesGcm.streamEncryptToPreparedScratchSig, Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Proof.Gcm.streamEncryptToPrepared16Pre,
              X86_64.abi, X86_64.argRegs, streamToSatP, streamToSat]
            sig_and_intros
            all_goals first
              | rfl
              | decide
              | exact preparedPowers16Repr_of_zero fun _ _ => rfl
              | exact Region.disjoint_of_sep (by decide)⟩ }

theorem streamEncryptToPrepared16_core (T : BlkToFn CtxMode.prepared16) (E : EncFn CtxMode.prepared16) :
    Verified X86_64.target (encrypt T.fn E.fn)
      (Proof.AesGcm.streamEncryptToPrepared16ScratchContract X86_64.abi 2624) :=
  Verified.of_correct (k := Proof.AesGcm.streamEncryptToX86_64M CtxMode.prepared16) (encrypt_correct T E)
    (encrypt_ct T E) streamToPrepared16_implies

theorem streamToFrameSatPrepared16_pre : ∃ s, (Proof.Gcm.streamEncryptToPrepared16Contract X86_64.abi 4856).pre s := by
  refine ⟨streamToFrameSatP, ?_⟩
  sig_pre [Proof.Gcm.streamEncryptToPrepared16Contract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig,
    Proof.Gcm.streamEncryptToPrepared16Pre, Proof.Gcm.streamEncryptToPost, X86_64.abi, X86_64.argRegs,
    streamToFrameSatP, streamToFrameSat, streamToSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact preparedPowers16Repr_of_zero fun _ _ => rfl

theorem streamEncryptToPrepared16_framed (T : BlkToFn CtxMode.prepared16) (E : EncFn CtxMode.prepared16) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2232 3 (encrypt T.fn E.fn))
      (Proof.Gcm.streamEncryptToPrepared16Contract X86_64.abi 4856) :=
  X86_64.Verified.stackArgScratch (sig := Proof.Gcm.streamEncryptToPreparedSig) (nm := "scratch")
    (e := .u64) (n := 274) (pre := Proof.Gcm.streamEncryptToPrepared16Pre X86_64.abi.ptrBits)
    (post := Proof.Gcm.streamEncryptToPost X86_64.abi.ptrBits) (wa := true) (stack := 2624)
    (bytes := 2232) (streamEncryptToPrepared16_core T E) (by decide) (by decide) (by decide)
    (encrypt_spAll T E) (encrypt_xdepth T E) (Proof.AesGcm.streamEncryptToPrepared16Pre_local _)
    (Proof.AesGcm.streamEncryptToPrecomputedPost_local _) streamToFrameSatPrepared16_pre

end VG.Proof.AesGcm.X86_64.StreamTo
