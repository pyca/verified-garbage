import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerifiedP
import VerifiedGarbage.Proof.AesGcm.ScratchP
import VerifiedGarbage.Proof.AesGcm.X86_64.InitPCT

/-!
# AES-GCM on x86-64, for a key context of either kind

Untrusted: everything here is checked by Lean. `seal`, `open`,
`stream_encrypt` and `stream_decrypt` calling the whole-blocks functions `B`
for a key context of kind `M` (`GcmImpl.withBlk`): their code loads no
`mxcsr`, keeps `rsp` and uses 24 bytes of stack, as for
`vg_aes_gcm_init`'s (`Verified.lean`, `Frame.lean`), and so they preserve
what the ABI says (`sealM_correct`, …).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

variable (v : GcmImpl) {M : CtxMode} (B : BlkFn M)

theorem sealM_mx : («seal» (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.allInstrs, GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem sealM_spSafe : («seal» (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.all, GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem sealM_xdepth : («seal» (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, tagLenOk, recv, cmp, tagOut, copyLoop, xorLoop, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

theorem sealM_correct (s : State) (hs : (Proof.AesGcm.sealX86_64M M).pre s) :
    ∃ t s', Exec isa («seal» (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sealM_wp v B hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealM_mx v B) he hg, hp⟩

theorem openM_mx : («open» (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.allInstrs, GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem openM_spSafe : («open» (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.all, GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem openM_xdepth : («open» (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, tagLenOk, recv, cmp, tagOut, copyLoop, xorLoop, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

theorem openM_correct (s : State) (hs : (Proof.AesGcm.openX86_64M M).pre s) :
    ∃ t s', Exec isa («open» (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := openM_wp v B hs
  exact ⟨t, s', he, abiPreserved_of_exec (openM_mx v B) he hg, hp⟩

theorem streamEncryptM_mx : (streamEncrypt (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.allInstrs, GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamEncryptM_spSafe : (streamEncrypt (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.all, GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamEncryptM_xdepth : (streamEncrypt (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, oneAad, copyLoop, xorLoop, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

theorem streamEncryptM_correct (s : State) (hs : (Proof.AesGcm.streamEncryptX86_64M M).pre s) :
    ∃ t s', Exec isa (streamEncrypt (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamEncryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamEncryptM_wp v B hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamEncryptM_mx v B) he hg, hp⟩

theorem streamDecryptM_mx : (streamDecrypt (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.allInstrs, GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamDecryptM_spSafe : (streamDecrypt (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, Code.all, GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamDecryptM_xdepth : (streamDecrypt (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, oneAad, copyLoop, xorLoop, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

theorem streamDecryptM_correct (s : State) (hs : (Proof.AesGcm.streamDecryptX86_64M M).pre s) :
    ∃ t s', Exec isa (streamDecrypt (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamDecryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamDecryptM_wp v B hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamDecryptM_mx v B) he hg, hp⟩

omit v B in
/-- Memory of zeros on a key context's 1024 bytes holds the powers of its
hash subkey. -/
theorem powersRepr_of_zero {m : Mem} {p : Addr} (h : ∀ i < 128 * 8, m (p + BitVec.ofNat 64 i) = 0) :
    Spec.Gcm.PowersRepr m p :=
  Proof.AesGcm.powersRepr_congr (m₁ := fun _ => 0) h (powersRepr_zero p)

/-- A state satisfying `vg_aes_gcm_seal_precomputed`'s precondition:
`sealSat`, with a key context of 1024 bytes. -/
def sealSatP : State :=
  { sealSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 32⟩] }

theorem sealP_verified :
    Verified X86_64.target («seal» (v.withBlk v.blkP)) (Proof.AesGcm.sealPrecomputedScratchContract X86_64.abi 24) :=
  Verified.of_correct (sealM_correct v v.blkP) (sealM_ct v v.blkP)
    { pre := by
        sig_implies_pre [Proof.AesGcm.sealPrecomputedScratchContract, Proof.AesGcm.sealPrecomputedScratchSig,
          Spec.Gcm.sealPrecomputedPre, Spec.Gcm.sealPost, Proof.AesGcm.sealX86_64M, Proof.AesGcm.sealX86_64,
          Proof.AesGcm.sealPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, CtxMode.powers, X86_64.abi,
          Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by
        sig_implies_post [Proof.AesGcm.sealPrecomputedScratchContract, Proof.AesGcm.sealPrecomputedScratchSig,
          Spec.Gcm.sealPrecomputedPre, Spec.Gcm.sealPost, Proof.AesGcm.sealX86_64M, Proof.AesGcm.sealX86_64,
          Proof.AesGcm.sealPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, CtxMode.powers, X86_64.abi,
          Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by
        sig_implies_pub [Proof.AesGcm.sealPrecomputedScratchContract, Proof.AesGcm.sealPrecomputedScratchSig,
          Spec.Gcm.sealPrecomputedPre, Spec.Gcm.sealPost, Proof.AesGcm.sealX86_64M, Proof.AesGcm.sealX86_64,
          Proof.AesGcm.sealPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, CtxMode.powers, X86_64.abi,
          Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      sat := ⟨sealSatP, by
        sig_pre [Proof.AesGcm.sealPrecomputedScratchContract, Proof.AesGcm.sealPrecomputedScratchSig,
          Spec.Gcm.sealPrecomputedPre, X86_64.abi, X86_64.argRegs, sealSatP, sealSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | (refine powersRepr_of_zero fun i hi => ?_
             split
             · next h => exfalso; bv_omega
             · rfl)⟩ }


/-- A state satisfying `vg_aes_gcm_open_precomputed`'s precondition:
`openSat`, with a key context of 1024 bytes. -/
def openSatP : State :=
  { openSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 40⟩] }

theorem openP_verified :
    Verified X86_64.target («open» (v.withBlk v.blkP)) (Proof.AesGcm.openPrecomputedScratchContract X86_64.abi 24) :=
  Verified.of_correct (openM_correct v v.blkP) (openM_ct v v.blkP)
    { pre := by sig_implies_pre [Proof.AesGcm.openPrecomputedScratchContract, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPrecomputedPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.powers, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.openPrecomputedScratchContract, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPrecomputedPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.powers, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcm.openPrecomputedScratchContract, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPrecomputedPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.powers, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesGcm.openPrecomputedScratchContract, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPrecomputedPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.powers, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
        sig_simp [Proof.AesGcm.openPrecomputedScratchContract, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPrecomputedPre, Spec.Gcm.openPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.powers, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := ⟨openSatP, by
        sig_pre [Proof.AesGcm.openPrecomputedScratchContract, Proof.AesGcm.openPrecomputedScratchSig,
          Spec.Gcm.openPrecomputedPre, X86_64.abi, X86_64.argRegs, openSatP, openSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact powersRepr_of_zero fun _ _ => rfl⟩ }

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt_precomputed`
and `_decrypt_precomputed`: `crSat`, with a key context of 1024 bytes. -/
def crSatP : State := { crSat with rd := [⟨0x1000, 1024⟩, ⟨0x8008, 16⟩] }

theorem streamEncryptP_verified :
    Verified X86_64.target (streamEncrypt (v.withBlk v.blkP))
      (Proof.AesGcm.streamEncryptPrecomputedScratchContract X86_64.abi 24) :=
  Verified.of_correct (streamEncryptM_correct v v.blkP) (streamEncryptM_ct v v.blkP)
    { pre := by sig_implies_pre [Proof.AesGcm.streamEncryptPrecomputedScratchContract, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamTextPrecomputedPre, Spec.Gcm.streamEncryptPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.powers,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.streamEncryptPrecomputedScratchContract, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamTextPrecomputedPre, Spec.Gcm.streamEncryptPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.powers,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by sig_implies_pub [Proof.AesGcm.streamEncryptPrecomputedScratchContract, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamTextPrecomputedPre, Spec.Gcm.streamEncryptPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.powers,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      sat := ⟨crSatP, by
        sig_pre [Proof.AesGcm.streamEncryptPrecomputedScratchContract, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamTextPrecomputedPre, X86_64.abi, X86_64.argRegs, crSatP, crSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact powersRepr_of_zero fun _ _ => rfl⟩ }

theorem streamDecryptP_verified :
    Verified X86_64.target (streamDecrypt (v.withBlk v.blkP))
      (Proof.AesGcm.streamDecryptPrecomputedScratchContract X86_64.abi 24) :=
  Verified.of_correct (streamDecryptM_correct v v.blkP) (streamDecryptM_ct v v.blkP)
    { pre := by sig_implies_pre [Proof.AesGcm.streamDecryptPrecomputedScratchContract, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamTextPrecomputedPre, Spec.Gcm.streamDecryptPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.powers,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.streamDecryptPrecomputedScratchContract, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamTextPrecomputedPre, Spec.Gcm.streamDecryptPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.powers,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by sig_implies_pub [Proof.AesGcm.streamDecryptPrecomputedScratchContract, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamTextPrecomputedPre, Spec.Gcm.streamDecryptPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.powers,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      sat := ⟨crSatP, by
        sig_pre [Proof.AesGcm.streamDecryptPrecomputedScratchContract, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Spec.Gcm.streamTextPrecomputedPre, X86_64.abi, X86_64.argRegs, crSatP, crSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact powersRepr_of_zero fun _ _ => rfl⟩ }


/-! ### With their working space on the stack -/

/-- A state satisfying `vg_aes_gcm_seal_precomputed`'s precondition, without
the working space. -/
def sealFrameSatP : State := { sealFrameSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 24⟩] }

theorem sealFrameSatP_pre : ∃ s, (Spec.Gcm.sealPrecomputedContract X86_64.abi 2624).pre s := by
  refine ⟨sealFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.sealPrecomputedContract, Spec.Gcm.sealPrecomputedSig, Spec.Gcm.sealPrecomputedPre,
    Spec.Gcm.sealPost, X86_64.abi, X86_64.argRegs, sealFrameSatP, sealFrameSat, sealSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine powersRepr_of_zero fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)

theorem sealP_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 («seal» (v.withBlk v.blkP)))
      (Spec.Gcm.sealPrecomputedContract X86_64.abi 2624) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.sealPrecomputedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealPrecomputedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2600) (sealP_verified v) (by decide) (by decide) (by decide)
    (sealM_spSafe v v.blkP) (sealM_xdepth v v.blkP) (Proof.AesGcm.sealPrecomputedPre_local _)
    (Proof.AesGcm.sealPrecomputedPost_local _) sealFrameSatP_pre

/-- A state satisfying `vg_aes_gcm_open_precomputed`'s precondition, without
the working space. -/
def openFrameSatP : State :=
  { openFrameSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 32⟩] }

theorem openFrameSatP_pre : ∃ s, (Spec.Gcm.openPrecomputedContract X86_64.abi 2632).pre s := by
  refine ⟨openFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.openPrecomputedContract, Spec.Gcm.openPrecomputedSig, Spec.Gcm.openPrecomputedPre,
    Spec.Gcm.openPost, Spec.Gcm.openLeak, X86_64.abi, X86_64.argRegs, openFrameSatP, openFrameSat, openSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact powersRepr_of_zero fun _ _ => rfl

theorem openP_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («open» (v.withBlk v.blkP)))
      (Spec.Gcm.openPrecomputedContract X86_64.abi 2632) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.openPrecomputedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openPrecomputedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.openPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (leak := some (Spec.Gcm.openLeak X86_64.abi.ptrBits)) (bytes := 2608) (openP_verified v)
    (by decide) (by decide) (by decide) (openM_spSafe v v.blkP) (openM_xdepth v v.blkP)
    (Proof.AesGcm.openPrecomputedPre_local _) (Proof.AesGcm.openPrecomputedPost_local _) openFrameSatP_pre
    (hleak := Proof.AesGcm.openPrecomputedLeak_local _)

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt_precomputed`
and `_decrypt_precomputed`, without the working space. -/
def crFrameSatP : State := { crFrameSat with rd := [⟨0x1000, 1024⟩, ⟨0x8008, 8⟩] }

theorem streamEncryptFrameSatP_pre : ∃ s, (Spec.Gcm.streamEncryptPrecomputedContract X86_64.abi 2608).pre s := by
  refine ⟨crFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.streamEncryptPrecomputedContract, Spec.Gcm.streamCryptPrecomputedSig,
    Spec.Gcm.streamTextPrecomputedPre, Spec.Gcm.streamEncryptPost, X86_64.abi, X86_64.argRegs, crFrameSatP, crFrameSat,
    crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact powersRepr_of_zero fun _ _ => rfl

theorem streamEncryptP_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncrypt (v.withBlk v.blkP)))
      (Spec.Gcm.streamEncryptPrecomputedContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPrecomputedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamEncryptPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamEncryptP_verified v) (by decide) (by decide) (by decide)
    (streamEncryptM_spSafe v v.blkP) (streamEncryptM_xdepth v v.blkP) (Proof.AesGcm.streamTextPrecomputedPre_local _)
    (Proof.AesGcm.streamEncryptPrecomputedPost_local _) streamEncryptFrameSatP_pre

theorem streamDecryptFrameSatP_pre : ∃ s, (Spec.Gcm.streamDecryptPrecomputedContract X86_64.abi 2608).pre s := by
  refine ⟨crFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.streamDecryptPrecomputedContract, Spec.Gcm.streamCryptPrecomputedSig,
    Spec.Gcm.streamTextPrecomputedPre, Spec.Gcm.streamDecryptPost, X86_64.abi, X86_64.argRegs, crFrameSatP, crFrameSat,
    crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact powersRepr_of_zero fun _ _ => rfl

theorem streamDecryptP_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecrypt (v.withBlk v.blkP)))
      (Spec.Gcm.streamDecryptPrecomputedContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPrecomputedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamDecryptPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamDecryptP_verified v) (by decide) (by decide) (by decide)
    (streamDecryptM_spSafe v v.blkP) (streamDecryptM_xdepth v v.blkP) (Proof.AesGcm.streamTextPrecomputedPre_local _)
    (Proof.AesGcm.streamDecryptPrecomputedPost_local _) streamDecryptFrameSatP_pre


/-! ### `vg_aes_gcm_init_precomputed` -/

omit B in
theorem powSteps_allInstrs {p : Instr → Bool} (h : (powStep v.callees).allInstrs p = true) :
    ∀ n, (powSteps v.callees n).allInstrs p = true
  | 0 => rfl
  | n + 1 => by simp only [powSteps, Code.allInstrs, powSteps_allInstrs h n, h, Bool.and_self]

omit B in
theorem powSteps_all {p : Instr → Bool} (h : (powStep v.callees).all p = true) :
    ∀ n, (powSteps v.callees n).all p = true
  | 0 => rfl
  | n + 1 => by simp only [powSteps, Code.all, powSteps_all h n, h, Bool.and_self]

omit B in
theorem powSteps_xdepth (h : (powStep v.callees).x86_64Depth ≤ 8) :
    ∀ n, (powSteps v.callees n).x86_64Depth ≤ 8
  | 0 => by show (Code.block ([] : List Instr)).x86_64Depth ≤ 8; decide
  | n + 1 => by simp only [powSteps, Code.x86_64Depth, Nat.max_le]; exact ⟨powSteps_xdepth h n, h⟩

omit B in
theorem initP_mx : (initPrecomputed v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  have hs : (powSteps v.callees 47).allInstrs (fun i => !loadsMxcsr i) = true := powSteps_allInstrs v (by
    simp only [powStep, Code.allInstrs, GcmImpl.callees, v.gh.mxcsr, Bool.true_and, Bool.and_true]
    decide +kernel) 47
  simp only [initPrecomputed, initWith, Code.allInstrs]
  rw [hs]
  simp only [GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

omit B in
theorem initP_spSafe : (initPrecomputed v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  have hs : (powSteps v.callees 47).all (fun i => !X86_64.isa.writesSp i) = true := powSteps_all v (by
    simp only [powStep, Code.all, GcmImpl.callees, v.gh.spSafe, Bool.true_and, Bool.and_true]
    decide +kernel) 47
  simp only [initPrecomputed, initWith, Code.all]
  rw [hs]
  simp only [GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

omit B in
theorem initP_xdepth : (initPrecomputed v.callees).x86_64Depth ≤ 8 := by
  have hs : (powSteps v.callees 47).x86_64Depth ≤ 8 := powSteps_xdepth v (by
    simp only [powStep, Code.x86_64Depth, GcmImpl.callees, v.gh.noStack, Nat.max_le]
    decide +kernel) 47
  simp only [initPrecomputed, initWith, Code.x86_64Depth, Nat.max_le]
  refine ⟨?_, ?_, ?_, ?_, ?_, hs, ?_⟩
  all_goals first | decide +kernel | (simp only [GcmImpl.callees, v.ctr.noStack, v.key.noStack]; decide +kernel)

omit B in
theorem initP_correct (s : State) (hs : Proof.AesGcm.initPrecomputedX86_64.pre s) :
    ∃ t s', Exec isa (initPrecomputed v.callees) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.initPrecomputedX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := initP_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (initP_mx v) he hg, hp⟩

/-- A state satisfying `vg_aes_gcm_init_precomputed`'s precondition: `initSat`,
with a key context of 1024 bytes. -/
def initSatP : State := { initSat with wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2560⟩] }

omit B in
theorem initP_verified :
    Verified X86_64.target (initPrecomputed v.callees) (Proof.AesGcm.initPrecomputedScratchContract X86_64.abi 8) :=
  Verified.of_correct (initP_correct v) (initP_ct v) (by
    sig_implies [Proof.AesGcm.initPrecomputedScratchContract, Proof.AesGcm.initPrecomputedScratchSig,
      Spec.Gcm.initPre, Spec.Gcm.initPrecomputedPost, Proof.AesGcm.initPrecomputedX86_64, Proof.AesGcm.initX86_64,
      Proof.AesGcm.initPreL, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [initSatP, initSat] using initSatP)

/-- A state satisfying `vg_aes_gcm_init_precomputed`'s precondition, without
the working space. -/
def initFrameSatP : State := { initSat with wr := [⟨0x2000, 1024⟩] }

theorem initFrameSatP_pre : ∃ s, (Spec.Gcm.initPrecomputedContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.initPrecomputedContract, Spec.Gcm.initPrecomputedSig, Spec.Gcm.initPre,
    Spec.Gcm.initPrecomputedPost, X86_64.abi, X86_64.argRegs] [initFrameSatP, initSat] using initFrameSatP

omit B in
theorem initP_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (initPrecomputed v.callees))
      (Spec.Gcm.initPrecomputedContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratch (sig := Spec.Gcm.initPrecomputedSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre X86_64.abi.ptrBits) (post := Spec.Gcm.initPrecomputedPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 2568) (initP_verified v) (by decide) (by decide)
    (by decide) (initP_spSafe v) (initP_xdepth v) initFrameSatP_pre

end VG.Proof.AesGcm.X86_64
