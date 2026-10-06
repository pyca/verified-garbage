import VerifiedGarbage.Proof.AesOcb.X86_64.OpenCT
import VerifiedGarbage.Proof.AesOcb.X86_64.InitCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.Proof.AesOcb.Scratch

/-!
# AES-OCB on x86-64: `Verified`

Correctness and constant time (for any implementations `v` of
`vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch`),
a state satisfying each precondition, and the shared contracts of
`Spec/Ocb/Contract.lean` with the working space as a last argument
(`Proof/AesOcb/Scratch.lean`; 3584 bytes for `seal` and `open`, 2560 for
`init`), with 8 bytes of stack: the return address of
the calls, whose callees use no stack. `Frame.lean` allocates the working
space.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem seal_mx (v : BlocksImpl) : («seal» (callees v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«seal», front, tagOut, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, body,
    whole, pass, nextOffset, rest, padCk, xorPad, tag, callBlocks, callees, Code.allInstrs, v.encMxcsr, v.decMxcsr,
    Bool.true_and, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem open_mx (v : BlocksImpl) : («open» (callees v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«open», front, recv, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, body,
    whole, pass, nextOffset, rest, padCk, xorPad, tag, cmp, mask, callBlocks, callees, Code.allInstrs, v.encMxcsr,
    v.decMxcsr, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_mx (v : BlocksImpl) : (init (callees v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, callees, Code.allInstrs, v.encMxcsr, v.expandMxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem seal_spSafe (v : BlocksImpl) : («seal» (callees v)).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«seal», front, tagOut, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, body,
    whole, pass, nextOffset, rest, padCk, xorPad, tag, callBlocks, callees, Code.all, v.encSpSafe, v.decSpSafe,
    Bool.true_and, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem open_spSafe (v : BlocksImpl) : («open» (callees v)).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«open», front, recv, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, body,
    whole, pass, nextOffset, rest, padCk, xorPad, tag, cmp, mask, callBlocks, callees, Code.all, v.encSpSafe,
    v.decSpSafe, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_spSafe (v : BlocksImpl) : (init (callees v)).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, callees, Code.all, v.encSpSafe, v.expandSpSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem seal_correct (v : BlocksImpl) (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» (callees v)) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := seal_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (seal_mx v) he hg, hp⟩

theorem open_correct (v : BlocksImpl) (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa («open» (callees v)) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := open_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (open_mx v) he hg, hp⟩

theorem init_correct (v : BlocksImpl) (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa (init (callees v)) s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (init_mx v) he hg, hp⟩

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: a 1-byte nonce,
no associated data, no data, a 4-byte tag at `0x3000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 1 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8020 then 4 else if a = 0x8019 then 0x30 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x8008, 40⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0, 3584⟩]

/-- A state satisfying the precondition of `vg_aes_ocb_init`: a 16-byte key. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

theorem seal_verified (v : BlocksImpl) :
    Verified X86_64.target («seal» (callees v)) (Proof.AesOcb.sealWorkContract X86_64.abi 448 8) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Proof.AesOcb.sealWorkContract, Proof.AesOcb.sealWorkSig, Spec.Ocb.sealPre,
      Spec.Ocb.sealPost, Proof.AesOcb.sealX86_64, Proof.AesOcb.sealPreX, Proof.AesOcb.oneFacts,
      Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad, Proof.AesOcb.aData, Proof.AesOcb.aTag,
      Proof.AesOcb.aWork, Proof.AesOcb.onePub, X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8,
      Proof.AesOcb.ret, Proof.AesOcb.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [sealSat] using sealSat)

theorem init_verified (v : BlocksImpl) :
    Verified X86_64.target (init (callees v)) (Proof.AesOcb.initScratchContract X86_64.abi 8) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Proof.AesOcb.initScratchContract, Proof.AesOcb.initScratchSig, Spec.Ocb.initPre,
      Spec.Ocb.initPost, Proof.AesOcb.initX86_64, Proof.AesOcb.stk8, Proof.AesOcb.ret, X86_64.abi, X86_64.argRegs,
      VG.X86_64.below] [initSat] using initSat)

/-- A state satisfying the precondition of `vg_aes_ocb_open`: as `sealSat`,
with the tag read only. -/
def openSat : State := { sealSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x3000, 4⟩, ⟨0x8008, 40⟩]
  wr := [⟨0, 0⟩, ⟨0, 3584⟩] }

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (v : BlocksImpl) :
    Verified X86_64.target («open» (callees v)) (Proof.AesOcb.openWorkContract X86_64.abi 448 8) :=
  Verified.of_correct (open_correct v) (open_ct v)
    { pre := by sig_implies_pre [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
      post := by sig_implies_post [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
        sig_simp [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] [openSat, sealSat] using openSat }

end VG.Proof.AesOcb.X86_64
