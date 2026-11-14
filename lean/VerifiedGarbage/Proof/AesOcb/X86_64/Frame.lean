module

public import VerifiedGarbage.Proof.AesOcb.Rounds
import VerifiedGarbage.Proof.AesOcb.X86_64.OpenCT
import VerifiedGarbage.Proof.AesOcb.X86_64.InitCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesOcb.Scratch
public import VerifiedGarbage.Proof.AesOcb.X86_64.Contract
public import VerifiedGarbage.Proof.AesOcb.X86_64.Nonce
import VerifiedGarbage.Proof.AesOcb.X86_64.Open
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/-! ### `AesOcb.X86_64.Verified`, which only this module used -/

section

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

@[expose] public section

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
      Proof.AesOcb.sealRoundsPost, Proof.AesOcb.sealX86_64, Proof.AesOcb.sealPreX, Proof.AesOcb.oneFacts,
      Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad, Proof.AesOcb.aData, Proof.AesOcb.aTag,
      Proof.AesOcb.aWork, Proof.AesOcb.onePub, X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8,
      Proof.AesOcb.ret, Proof.AesOcb.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [sealSat] using sealSat)

theorem initF_correct (v : BlocksImpl) (f : Proof.Aes.X86_64.BlocksFree v.enc v.expand) (s : State)
    (hs : initX86_64F.pre s) :
    ∃ t s', Exec isa (init (callees v)) s t s' ∧ abiPreserved s s' ∧ initX86_64F.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := initF_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (init_mx v) he hg, hp⟩

/-- A state satisfying the precondition of `vg_aes_ocb_init` with 24 bytes of
working space. -/
def initSatF : State := { initSat with wr := [⟨0x2000, 256⟩, ⟨0x4000, 24⟩] }

theorem initF_verified (v : BlocksImpl) (f : Proof.Aes.X86_64.BlocksFree v.enc v.expand) :
    Verified X86_64.target (init (callees v)) (Proof.AesOcb.initScratchContractF X86_64.abi 8) :=
  Verified.of_correct (initF_correct v f) (initF_ct v f) (by
    sig_implies [Proof.AesOcb.initScratchContractF, Proof.AesOcb.initScratchSigF, Spec.Ocb.initPre,
      Spec.Ocb.initPost, Proof.AesOcb.initX86_64F, Proof.AesOcb.initX86_64, Proof.AesOcb.stk8, Proof.AesOcb.ret,
      X86_64.abi, X86_64.argRegs, VG.X86_64.below] [initSatF, initSat] using initSatF)

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
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
      post := by sig_implies_post [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
        sig_simp [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] [openSat, sealSat] using openSat }

end VG.Proof.AesOcb.X86_64

end

end


/-!
# AES-OCB on x86-64, with its working space on the stack

Every function runs its code, proved with the working space as its last
argument (`Verified.lean`), in a frame that allocates it. `init`'s working
space is in a register (`rcx`): its frame of 2568 bytes holds the 2560
bytes and 8 more to keep `rsp` aligned (`Verified.stackScratch`). The
working space of `seal` and `open` is passed on the stack after the six
argument registers and four other stack arguments (`data`, `len`, `tag` and
`tag_len`), so their frame of 3632 bytes holds the 3584 bytes of working
space, a copy of those four arguments, the word that stands for the return
address and the address of the working space (`Verified.stackArgScratch`).
The code's own calls use 8 bytes below the frame, the return address, as
`vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch` use
no stack. `open`'s leak, whether it succeeds, reads only its buffers
(`openLeak_local`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

variable (v : BlocksImpl)

theorem init_xdepth : (init (callees v)).x86_64Depth ≤ 8 := by
  simp only [init, callees, Code.x86_64Depth, v.encNoStack, v.expandNoStack]
  decide +kernel

theorem seal_xdepth : («seal» (callees v)).x86_64Depth ≤ 8 := by
  simp only [«seal», front, tagOut, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill,
    hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest, padCk, xorPad, tag, callBlocks, callees,
    Code.x86_64Depth, v.encNoStack, v.decNoStack, ↓reduceIte]
  decide +kernel

theorem open_xdepth : («open» (callees v)).x86_64Depth ≤ 8 := by
  simp only [«open», front, recv, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill,
    hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest, padCk, xorPad, tag, cmp, mask, callBlocks, callees,
    Code.x86_64Depth, v.encNoStack, v.decNoStack, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

/-- A state satisfying `vg_aes_ocb_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Ocb.initContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Ocb.initContract, Spec.Ocb.initSig, Spec.Ocb.initPre, Spec.Ocb.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (init (callees v)))
      (Spec.Ocb.initContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratch (sig := Spec.Ocb.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Ocb.initPre X86_64.abi.ptrBits) (post := Spec.Ocb.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 2568) (init_verified v) (by decide) (by decide)
    (by decide) (init_spSafe v) (init_xdepth v) initFrameSat_pre

theorem initFrameSatF_pre : ∃ s, (Spec.Ocb.initContract X86_64.abi 40).pre s := by
  implies_sat [Spec.Ocb.initContract, Spec.Ocb.initSig, Spec.Ocb.initPre, Spec.Ocb.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- `init_framed`, over functions that need no working space: a frame of the
24 bytes `init` writes itself, after the 8 that stand for the return
address. -/
theorem initF_framed (f : Proof.Aes.X86_64.BlocksFree v.enc v.expand) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 32 .rcx (init (callees v)))
      (Spec.Ocb.initContract X86_64.abi 40) :=
  X86_64.Verified.stackScratch (sig := Spec.Ocb.initSig) (nm := "scratch") (e := .u64) (n := 3)
    (pre := Spec.Ocb.initPre X86_64.abi.ptrBits) (post := Spec.Ocb.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 32) (initF_verified v f) (by decide) (by decide)
    (by decide) (init_spSafe v) (init_xdepth v) initFrameSatF_pre

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩, ⟨0x3000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesOcb.sealRoundsContract X86_64.abi 3640).pre s := by
  implies_sat [Proof.AesOcb.sealRoundsContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Proof.AesOcb.sealRoundsPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using sealFrameSat

theorem seal_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 3632 4 («seal» (callees v)))
      (Proof.AesOcb.sealRoundsContract X86_64.abi 3640) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64)
    (n := 448) (pre := Spec.Ocb.sealPre X86_64.abi.ptrBits)
    (post := Proof.AesOcb.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3632) (seal_verified v) (by decide) (by decide) (by decide)
    (seal_spSafe v) (seal_xdepth v) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x3000, 4⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesOcb.openRoundsContract X86_64.abi 3640).pre s := by
  implies_sat [Proof.AesOcb.openRoundsContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Proof.AesOcb.openRoundsPost,
    Spec.Ocb.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, sealSat] using openFrameSat

theorem open_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 3632 4 («open» (callees v)))
      (Proof.AesOcb.openRoundsContract X86_64.abi 3640) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64)
    (n := 448) (pre := Spec.Ocb.openPre X86_64.abi.ptrBits)
    (post := Proof.AesOcb.openRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.Ocb.openLeak X86_64.abi.ptrBits)) (bytes := 3632) (open_verified v)
    (by decide) (by decide) (by decide) (open_spSafe v) (open_xdepth v) (openPre_local _)
    (openPost_local _) openFrameSat_pre (hleak := openLeak_local _)

end VG.Proof.AesOcb.X86_64
