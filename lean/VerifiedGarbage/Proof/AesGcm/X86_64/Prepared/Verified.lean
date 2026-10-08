import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.BlocksVerified

/-! # Prepared-context sealing and streaming contracts -/
set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

theorem preparedPowersRepr_of_zero {m : Mem} {p : Addr} (h : ∀ i < 128 * 8, m (p + BitVec.ofNat 64 i) = 0) :
    Spec.Gcm.PreparedPowersRepr m p :=
  Proof.AesGcm.preparedPowersRepr_congr (m₁ := fun _ => 0) h (preparedPowersRepr_zero p)

theorem sealPreparedCode_verified {c : Prog isa}
    (hc : ∀ s, (Proof.AesGcm.sealX86_64M CtxMode.prepared).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s')
    (hct : ConstantTime isa (Proof.AesGcm.sealX86_64M CtxMode.prepared).pre Proof.AesGcm.sealX86_64.pub c) :
    Verified X86_64.target c (Proof.AesGcm.sealPreparedScratchContract X86_64.abi 24) :=
  Verified.of_correct hc hct
    { pre := by
        sig_implies_pre [Proof.AesGcm.sealPreparedScratchContract, Proof.AesGcm.sealPreparedScratchSig, Proof.AesGcm.sealPrecomputedScratchSig,
          Spec.Gcm.sealPreparedPre, Spec.Gcm.sealPost, Proof.AesGcm.sealX86_64M, Proof.AesGcm.sealX86_64,
          Proof.AesGcm.sealPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, CtxMode.prepared, X86_64.abi,
          Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by
        sig_implies_post [Proof.AesGcm.sealPreparedScratchContract, Proof.AesGcm.sealPreparedScratchSig, Proof.AesGcm.sealPrecomputedScratchSig,
          Spec.Gcm.sealPreparedPre, Spec.Gcm.sealPost, Proof.AesGcm.sealX86_64M, Proof.AesGcm.sealX86_64,
          Proof.AesGcm.sealPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, CtxMode.prepared, X86_64.abi,
          Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by
        sig_implies_pub [Proof.AesGcm.sealPreparedScratchContract, Proof.AesGcm.sealPreparedScratchSig, Proof.AesGcm.sealPrecomputedScratchSig,
          Spec.Gcm.sealPreparedPre, Spec.Gcm.sealPost, Proof.AesGcm.sealX86_64M, Proof.AesGcm.sealX86_64,
          Proof.AesGcm.sealPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, CtxMode.prepared, X86_64.abi,
          Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      sat := ⟨sealSatP, by
        sig_pre [Proof.AesGcm.sealPreparedScratchContract, Proof.AesGcm.sealPreparedScratchSig, Proof.AesGcm.sealPrecomputedScratchSig,
          Spec.Gcm.sealPreparedPre, X86_64.abi, X86_64.argRegs, sealSatP, sealSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | (refine preparedPowersRepr_of_zero fun i hi => ?_
             split
             · next h => exfalso; bv_omega
             · rfl)⟩ }

theorem sealPrepared_verified (v : GcmImpl) (B : BlkFn CtxMode.prepared) :
    Verified X86_64.target («seal» (v.withBlk B)) (Proof.AesGcm.sealPreparedScratchContract X86_64.abi 24) :=
  sealPreparedCode_verified (sealM_correct v B) (sealM_ct v B)

theorem openPreparedCode_verified {c : Prog isa}
    (hc : ∀ s, (Proof.AesGcm.openX86_64M CtxMode.prepared).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s')
    (hct : ConstantTime isa (Proof.AesGcm.openX86_64M CtxMode.prepared).pre Proof.AesGcm.openX86_64.pub c) :
    Verified X86_64.target c (Proof.AesGcm.openPreparedScratchContract X86_64.abi 24) :=
  Verified.of_correct hc hct
    { pre := by sig_implies_pre [Proof.AesGcm.openPreparedScratchContract, Proof.AesGcm.openPreparedScratchSig, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPreparedPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.prepared, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.openPreparedScratchContract, Proof.AesGcm.openPreparedScratchSig, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPreparedPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.prepared, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcm.openPreparedScratchContract, Proof.AesGcm.openPreparedScratchSig, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPreparedPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.prepared, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesGcm.openPreparedScratchContract, Proof.AesGcm.openPreparedScratchSig, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPreparedPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.prepared, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
        sig_simp [Proof.AesGcm.openPreparedScratchContract, Proof.AesGcm.openPreparedScratchSig, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPreparedPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.prepared, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := ⟨openSatP, by
        sig_pre [Proof.AesGcm.openPreparedScratchContract, Proof.AesGcm.openPreparedScratchSig, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPreparedPre, X86_64.abi, X86_64.argRegs, openSatP, openSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact preparedPowersRepr_of_zero fun _ _ => rfl⟩ }

theorem openPrepared_verified (v : GcmImpl) (B : BlkFn CtxMode.prepared) :
    Verified X86_64.target («open» (v.withBlk B)) (Proof.AesGcm.openPreparedScratchContract X86_64.abi 24) :=
  openPreparedCode_verified (openM_correct v B) (openM_ct v B)

theorem streamEncryptPrepared_verified (v : GcmImpl) (B : BlkFn CtxMode.prepared) :
    Verified X86_64.target (streamEncrypt (v.withBlk B))
      (Proof.AesGcm.streamEncryptPreparedScratchContract X86_64.abi 24) :=
  Verified.of_correct (streamEncryptM_correct v B) (streamEncryptM_ct v B)
    { pre := by sig_implies_pre [Proof.AesGcm.streamEncryptPreparedScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamCryptPreparedPre, Spec.Gcm.streamEncryptPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.streamEncryptPreparedScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamCryptPreparedPre, Spec.Gcm.streamEncryptPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by sig_implies_pub [Proof.AesGcm.streamEncryptPreparedScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamCryptPreparedPre, Spec.Gcm.streamEncryptPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      sat := ⟨crSatP, by
        sig_pre [Proof.AesGcm.streamEncryptPreparedScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamCryptPreparedPre, X86_64.abi, X86_64.argRegs, crSatP, crSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact preparedPowersRepr_of_zero fun _ _ => rfl⟩ }

theorem streamDecryptPrepared_verified (v : GcmImpl) (B : BlkFn CtxMode.prepared) :
    Verified X86_64.target (streamDecrypt (v.withBlk B))
      (Proof.AesGcm.streamDecryptPreparedScratchContract X86_64.abi 24) :=
  Verified.of_correct (streamDecryptM_correct v B) (streamDecryptM_ct v B)
    { pre := by sig_implies_pre [Proof.AesGcm.streamDecryptPreparedScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamCryptPreparedPre, Spec.Gcm.streamDecryptPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.streamDecryptPreparedScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamCryptPreparedPre, Spec.Gcm.streamDecryptPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by sig_implies_pub [Proof.AesGcm.streamDecryptPreparedScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamCryptPreparedPre, Spec.Gcm.streamDecryptPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      sat := ⟨crSatP, by
        sig_pre [Proof.AesGcm.streamDecryptPreparedScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamCryptPreparedPre, X86_64.abi, X86_64.argRegs, crSatP, crSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact preparedPowersRepr_of_zero fun _ _ => rfl⟩ }

/-! ### With their working space on the stack -/

theorem sealFrameSatPrepared_pre : ∃ s, (Spec.Gcm.sealPreparedContract X86_64.abi 2624).pre s := by
  refine ⟨sealFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.sealPreparedContract, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPrecomputedSig, Spec.Gcm.sealPreparedPre,
    Spec.Gcm.sealPost, X86_64.abi, X86_64.argRegs, sealFrameSatP, sealFrameSat, sealSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowersRepr_of_zero fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)

theorem sealPreparedCode_framed {c : Prog isa}
    (hv : Verified X86_64.target c (Proof.AesGcm.sealPreparedScratchContract X86_64.abi 24))
    (hsp : c.all (fun i => !X86_64.isa.writesSp i) = true) (hxd : c.x86_64Depth ≤ 24) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 c)
      (Spec.Gcm.sealPreparedContract X86_64.abi 2624) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.sealPreparedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealPreparedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2600) hv (by decide) (by decide) (by decide)
    hsp hxd (Proof.AesGcm.sealPreparedPre_local _)
    (Proof.AesGcm.sealPrecomputedPost_local _) sealFrameSatPrepared_pre

theorem sealPrepared_framed (v : GcmImpl) (B : BlkFn CtxMode.prepared) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 («seal» (v.withBlk B)))
      (Spec.Gcm.sealPreparedContract X86_64.abi 2624) :=
  sealPreparedCode_framed (sealPrepared_verified v B) (sealM_spSafe v B) (sealM_xdepth v B)

theorem openFrameSatPrepared_pre : ∃ s, (Spec.Gcm.openPreparedContract X86_64.abi 2632).pre s := by
  refine ⟨openFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.openPreparedContract, Spec.Gcm.openPreparedSig, Spec.Gcm.openPrecomputedSig, Spec.Gcm.openPreparedPre,
    Spec.Gcm.openPost, Spec.Gcm.openLeak, X86_64.abi, X86_64.argRegs, openFrameSatP, openFrameSat, openSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact preparedPowersRepr_of_zero fun _ _ => rfl

theorem openPreparedCode_framed {c : Prog isa}
    (hv : Verified X86_64.target c (Proof.AesGcm.openPreparedScratchContract X86_64.abi 24))
    (hsp : c.all (fun i => !X86_64.isa.writesSp i) = true) (hxd : c.x86_64Depth ≤ 24) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 c)
      (Spec.Gcm.openPreparedContract X86_64.abi 2632) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.openPreparedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openPreparedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.openPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (leak := some (Spec.Gcm.openLeak X86_64.abi.ptrBits)) (bytes := 2608) hv
    (by decide) (by decide) (by decide) hsp hxd
    (Proof.AesGcm.openPreparedPre_local _) (Proof.AesGcm.openPrecomputedPost_local _) openFrameSatPrepared_pre
    (hleak := Proof.AesGcm.openPrecomputedLeak_local _)

theorem openPrepared_framed (v : GcmImpl) (B : BlkFn CtxMode.prepared) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («open» (v.withBlk B)))
      (Spec.Gcm.openPreparedContract X86_64.abi 2632) :=
  openPreparedCode_framed (openPrepared_verified v B) (openM_spSafe v B) (openM_xdepth v B)

theorem streamEncryptFrameSatPrepared_pre : ∃ s, (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s := by
  refine ⟨crFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.streamEncryptPreparedContract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrecomputedSig,
    Spec.Gcm.streamCryptPreparedPre, Spec.Gcm.streamEncryptPost, X86_64.abi, X86_64.argRegs, crFrameSatP, crFrameSat,
    crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact preparedPowersRepr_of_zero fun _ _ => rfl

theorem streamEncryptPrepared_framed (v : GcmImpl) (B : BlkFn CtxMode.prepared) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncrypt (v.withBlk B)))
      (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamCryptPreparedSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamCryptPreparedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamEncryptPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamEncryptPrepared_verified v B) (by decide) (by decide) (by decide)
    (streamEncryptM_spSafe v B) (streamEncryptM_xdepth v B) (Proof.AesGcm.streamCryptPreparedPre_local _)
    (Proof.AesGcm.streamEncryptPrecomputedPost_local _) streamEncryptFrameSatPrepared_pre

theorem streamDecryptFrameSatPrepared_pre : ∃ s, (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608).pre s := by
  refine ⟨crFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.streamDecryptPreparedContract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrecomputedSig,
    Spec.Gcm.streamCryptPreparedPre, Spec.Gcm.streamDecryptPost, X86_64.abi, X86_64.argRegs, crFrameSatP, crFrameSat,
    crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact preparedPowersRepr_of_zero fun _ _ => rfl

theorem streamDecryptPrepared_framed (v : GcmImpl) (B : BlkFn CtxMode.prepared) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecrypt (v.withBlk B)))
      (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamCryptPreparedSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamCryptPreparedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamDecryptPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamDecryptPrepared_verified v B) (by decide) (by decide) (by decide)
    (streamDecryptM_spSafe v B) (streamDecryptM_xdepth v B) (Proof.AesGcm.streamCryptPreparedPre_local _)
    (Proof.AesGcm.streamDecryptPrecomputedPost_local _) streamDecryptFrameSatPrepared_pre

end VG.Proof.AesGcm.X86_64
