module

public import VerifiedGarbage.Proof.AesOcb.Rounds
import VerifiedGarbage.Proof.AesOcb.AArch64.OpenCT
import VerifiedGarbage.Proof.AesOcb.AArch64.InitCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesOcb.Scratch
public import VerifiedGarbage.Proof.AesOcb.AArch64.Args
public import VerifiedGarbage.Proof.AesOcb.AArch64.Contract
import VerifiedGarbage.Proof.AesOcb.AArch64.Init
import VerifiedGarbage.Proof.AesOcb.AArch64.Open
import VerifiedGarbage.Proof.AesOcb.AArch64.SealCT
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-! ### `AesOcb.AArch64.Verified`, which only this module used -/

section

/-!
# AES-OCB on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_encrypt_blocks`,
`vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch`), a state satisfying each
precondition, and the shared contracts of `Spec/Ocb/Contract.lean` with the
working space as a last argument (`Proof/AesOcb/Scratch.lean`), with no
stack: the calls keep the return address in `x30`, which each function saves
in its working space. `Frame.lean` allocates the working space.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.Impl.AesOcb.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-! ## v8–v15 -/

theorem seal_keepsV (v : BlocksImpl) : («seal» (callees v)).allInstrs keepsV = true := by
  simp only [«seal», front, tagOut, nonce, Impl.AesOcb.AArch64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, lNtz, body,
    whole, passFast, nextOffset, rest, padCk, xorPad, tag, callBlocks, callees, Code.allInstrs, v.encKeepsV,
    v.decKeepsV, Bool.true_and, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem open_keepsV (v : BlocksImpl) : («open» (callees v)).allInstrs keepsV = true := by
  simp only [«open», front, recv, nonce, Impl.AesOcb.AArch64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, lNtz, body,
    whole, passFast, nextOffset, rest, padCk, xorPad, tag, cmp, mask, callBlocks, callees, Code.allInstrs, v.encKeepsV,
    v.decKeepsV, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_keepsV (v : BlocksImpl) : (init (callees v)).allInstrs keepsV = true := by
  simp only [init, callees, Code.allInstrs, v.encKeepsV, v.expandKeepsV, Bool.true_and, Bool.and_true]
  decide +kernel

/-! ## Correctness -/

theorem seal_correct (v : BlocksImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa («seal» (callees v)) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (seal_wp v hs) (seal_keepsV v)

theorem open_correct (v : BlocksImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa («open» (callees v)) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (open_wp v hs) (open_keepsV v)

theorem init_correct (v : BlocksImpl) (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa (init (callees v)) s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  WP.withPreservedV (init_wp v hs) (init_keepsV v)

/-! ## States satisfying the preconditions -/

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: a 1-byte nonce,
no associated data, no data, a 4-byte tag at `0x5000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 1 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8008 then 4 else if a = 0x8001 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x8000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ocb_open`: as `sealSat`,
with the tag read only. -/
def openSat : State := { sealSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0, 2560⟩] }

/-- A state satisfying the precondition of `vg_aes_ocb_init`: a 16-byte key. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

/-! ## The shared contracts -/

theorem seal_verified (v : BlocksImpl) :
    Verified AArch64.target («seal» (callees v)) (Proof.AesOcb.sealScratchContract AArch64.abi) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Proof.AesOcb.sealRoundsPost, sealAArch64, sealPreA, oneFacts, aCtx, aNonce, aAad, aData, aTag, aWork, onePub, args,
      rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
      List.range.loop] [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem init_verified (v : BlocksImpl) :
    Verified AArch64.target (init (callees v)) (Proof.AesOcb.initScratchContract AArch64.abi) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Proof.AesOcb.initScratchContract, Proof.AesOcb.initScratchSig, Spec.Ocb.initPre,
      Spec.Ocb.initPost, initAArch64, AArch64.abi, AArch64.argRegs] [initSat] using initSat)

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (v : BlocksImpl) :
    Verified AArch64.target («open» (callees v)) (Proof.AesOcb.openScratchContract AArch64.abi) :=
  Verified.of_correct (open_correct v) (open_ct v)
    { pre := by sig_implies_pre [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openAArch64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      post := by sig_implies_post [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openAArch64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openAArch64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop] at h
        sig_split h
        sig_reduce [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openAArch64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        sig_simp [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openAArch64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openAArch64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop] [openSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

end VG.Proof.AesOcb.AArch64

end

end


/-!
# AES-OCB on AArch64, with its working space on the stack

Every function runs its code, proved with the working space as its last
argument (`Verified.lean`), in a frame that allocates it. `init`'s working
space is in a register (`x3`): its frame holds the 2560 bytes
(`Verified.stackScratch`). The working space of `seal` and `open` is their
third stack argument, after `tag` and `tag_len`, so their frame of 2592
bytes holds a copy of those two, the address of the working space and the
working space, at the next 16-byte boundary (`Verified.stackArgScratch`).
The code itself uses no stack: its calls keep the return address in `x30`.
`open`'s leak, whether it succeeds, reads only its buffers
(`openLeak_local`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.Impl.AesOcb.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- A state satisfying `vg_aes_ocb_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Ocb.initContract AArch64.abi 2560).pre s := by
  implies_sat [Spec.Ocb.initContract, Spec.Ocb.initSig, Spec.Ocb.initPre, Spec.Ocb.initPost,
    AArch64.abi, AArch64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed (v : BlocksImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 2560 .x3 (init (callees v)))
      (Spec.Ocb.initContract AArch64.abi 2560) :=
  AArch64.Verified.stackScratch (sig := Spec.Ocb.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Ocb.initPre AArch64.abi.ptrBits) (post := Spec.Ocb.initPost AArch64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2560) (init_verified v) (by decide) (by decide)
    initFrameSat_pre

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesOcb.sealRoundsContract AArch64.abi 2592).pre s := by
  implies_sat [Proof.AesOcb.sealRoundsContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Proof.AesOcb.sealRoundsPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed (v : BlocksImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («seal» (callees v)))
      (Proof.AesOcb.sealRoundsContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ocb.sealPre AArch64.abi.ptrBits)
    (post := Proof.AesOcb.sealRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (seal_verified v) (by decide) (by decide) (Proof.AesOcb.sealPre_local _) (Proof.AesOcb.sealPost_local _)
    sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesOcb.openRoundsContract AArch64.abi 2592).pre s := by
  implies_sat [Proof.AesOcb.openRoundsContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Proof.AesOcb.openRoundsPost,
    Spec.Ocb.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
    List.getD, List.range, List.range.loop] [openFrameSat, sealSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed (v : BlocksImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («open» (callees v)))
      (Proof.AesOcb.openRoundsContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ocb.openPre AArch64.abi.ptrBits)
    (post := Proof.AesOcb.openRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (leak := some (Spec.Ocb.openLeak AArch64.abi.ptrBits))
    (open_verified v) (by decide) (by decide) (Proof.AesOcb.openPre_local _)
    (Proof.AesOcb.openPost_local _) openFrameSat_pre (hleak := Proof.AesOcb.openLeak_local _)

end VG.Proof.AesOcb.AArch64
