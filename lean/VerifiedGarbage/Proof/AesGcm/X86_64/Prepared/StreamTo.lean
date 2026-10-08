import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
import VerifiedGarbage.Proof.AesGcm.ScratchPreparedTo

/-! # Prepared-context StreamTo contracts -/
set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.StreamTo
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)
open VG.Impl.AesGcm.X86_64.StreamTo

theorem streamToPrepared_implies : (Proof.AesGcm.streamEncryptToX86_64M CtxMode.prepared).Implies
    (Proof.AesGcm.streamEncryptToPreparedScratchContract X86_64.abi 2624) := by
  exact { pre := by sig_implies_pre [Proof.AesGcm.streamEncryptToPreparedScratchContract,
      Proof.AesGcm.streamEncryptToPreparedScratchSig, Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Spec.Gcm.streamEncryptToPreparedPre,
      Spec.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.prepared]
          post := by sig_implies_post [Proof.AesGcm.streamEncryptToPreparedScratchContract,
      Proof.AesGcm.streamEncryptToPreparedScratchSig, Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Spec.Gcm.streamEncryptToPreparedPre,
      Spec.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.prepared]
          pub := by sig_implies_pub [Proof.AesGcm.streamEncryptToPreparedScratchContract,
      Proof.AesGcm.streamEncryptToPreparedScratchSig, Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Spec.Gcm.streamEncryptToPreparedPre,
      Spec.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.prepared]
          sat := ⟨streamToSatP, by
            sig_pre [Proof.AesGcm.streamEncryptToPreparedScratchContract,
              Proof.AesGcm.streamEncryptToPreparedScratchSig, Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Spec.Gcm.streamEncryptToPreparedPre,
              X86_64.abi, X86_64.argRegs, streamToSatP, streamToSat]
            sig_and_intros
            all_goals first
              | rfl
              | decide
              | exact preparedPowersRepr_of_zero fun _ _ => rfl
              | exact Region.disjoint_of_sep (by decide)⟩ }

theorem streamEncryptToPrepared_core (T : BlkToFn CtxMode.prepared) (E : EncFn CtxMode.prepared) :
    Verified X86_64.target (encrypt T.fn E.fn)
      (Proof.AesGcm.streamEncryptToPreparedScratchContract X86_64.abi 2624) :=
  Verified.of_correct (k := Proof.AesGcm.streamEncryptToX86_64M CtxMode.prepared) (encrypt_correct T E)
    (encrypt_ct T E) streamToPrepared_implies

theorem streamToFrameSatPrepared_pre : ∃ s, (Spec.Gcm.streamEncryptToPreparedContract X86_64.abi 4856).pre s := by
  refine ⟨streamToFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.streamEncryptToPreparedContract, Spec.Gcm.streamEncryptToPreparedSig, Spec.Gcm.streamEncryptToPrecomputedSig,
    Spec.Gcm.streamEncryptToPreparedPre, Spec.Gcm.streamEncryptToPost, X86_64.abi, X86_64.argRegs,
    streamToFrameSatP, streamToFrameSat, streamToSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact preparedPowersRepr_of_zero fun _ _ => rfl

theorem streamEncryptToPrepared_framed (T : BlkToFn CtxMode.prepared) (E : EncFn CtxMode.prepared) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2232 3 (encrypt T.fn E.fn))
      (Spec.Gcm.streamEncryptToPreparedContract X86_64.abi 4856) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamEncryptToPreparedSig) (nm := "scratch")
    (e := .u64) (n := 274) (pre := Spec.Gcm.streamEncryptToPreparedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamEncryptToPost X86_64.abi.ptrBits) (wa := true) (stack := 2624)
    (bytes := 2232) (streamEncryptToPrepared_core T E) (by decide) (by decide) (by decide)
    (encrypt_spAll T E) (encrypt_xdepth T E) (Proof.AesGcm.streamEncryptToPreparedPre_local _)
    (Proof.AesGcm.streamEncryptToPrecomputedPost_local _) streamToFrameSatPrepared_pre

end VG.Proof.AesGcm.X86_64.StreamTo
