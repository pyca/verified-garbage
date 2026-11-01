module

public import VerifiedGarbage.Proof.AesOcb.RISCV64.Contract
public import VerifiedGarbage.Proof.AesOcb.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesOcb.RISCV64
import VerifiedGarbage.Proof.AesOcb.RISCV64.Seal
import VerifiedGarbage.Proof.AesOcb.RISCV64.Open
import VerifiedGarbage.Proof.AesOcb.RISCV64.FnCT
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# AES-OCB on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time,
a state satisfying each precondition, and the shared contracts of
`Spec/Ocb/Contract.lean` with the working space as a last argument
(`Proof/AesOcb/Scratch.lean`; with no stack: a call keeps the return address
in `ra`, which each function saves in the working space).
The working space is then allocated on the stack (`seal_framed`,
`open_framed`); `init` is AES-GCM's (`Init.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.Impl.AesOcb.RISCV64

theorem seal_correct (s : State) (hs : sealRISCV64.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealRISCV64.post s s' :=
  seal_wp hs

theorem open_correct (s : State) (hs : openRISCV64.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openRISCV64.post s s' :=
  open_wp hs

/-! ## States satisfying the preconditions -/

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: a 1-byte nonce,
no associated data, no data, a 4-byte tag at `0x5000` and `work` at
`0x6000`, with the stack arguments at `0x9000`. -/
def sealSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a3 => 1 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x50 else bif Nat.beq a.toNat 0x9008 then 4 else
    bif Nat.beq a.toNat 0x9011 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x9000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩, ⟨0x6000, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ocb_open`: as `sealSat`,
with the tag read only. -/
def openSat : State := { sealSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x9000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x6000, 2560⟩] }

/-! ## The shared contracts -/

theorem seal_verified :
    Verified RISCV64.target «seal» (Proof.AesOcb.sealScratchContract RISCV64.abi) :=
  Verified.of_correct seal_correct seal_ct
    { pre := by sig_implies_pre [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Spec.Ocb.sealPost, sealRISCV64, sealPreA, oneFacts, aCtx, aNonce, aAad, aData, aTag, aWork, onePub, args,
      rounds, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range,
      List.range.loop, BitVec.add_zero]
      post := by sig_implies_post [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Spec.Ocb.sealPost, sealRISCV64, sealPreA, oneFacts, aCtx, aNonce, aAad, aData, aTag, aWork, onePub, args,
      rounds, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range,
      List.range.loop]
      pub := by sig_implies_pub [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Spec.Ocb.sealPost, sealRISCV64, sealPreA, oneFacts, aCtx, aNonce, aAad, aData, aTag, aWork, onePub, args,
      rounds, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range,
      List.range.loop]
      sat := by sig_implies_sat [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Spec.Ocb.sealPost, sealRISCV64, sealPreA, oneFacts, aCtx, aNonce, aAad, aData, aTag, aWork, onePub, args,
      rounds, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range,
      List.range.loop] [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat }

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified :
    Verified RISCV64.target «open» (Proof.AesOcb.openScratchContract RISCV64.abi) :=
  Verified.of_correct open_correct open_ct
    { pre := by sig_implies_pre [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
        stackArgAddr, List.getD, List.range, List.range.loop, BitVec.add_zero]
      post := by sig_implies_post [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
        stackArgAddr, List.getD, List.range, List.range.loop]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Spec.Ocb.openPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
          aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop] at h
        sig_split h
        sig_reduce [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Spec.Ocb.openPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
          aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop]
        sig_simp [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Spec.Ocb.openPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
          aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop]
          [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
        stackArgAddr, List.getD, List.range, List.range.loop] [openSat, sealSat, stackArg, stackArgAddr, Mem.readW,
        Mem.read] using openSat }

/-! ## With the working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (above), in a frame that allocates it
(`Verified.stackScratchArgs`): `tag` and `tag_len` arrive on the stack, so
the frame of 2592 bytes copies them, then the working space's address, above
its stack pointer. The copies are read only where the pre- and
postconditions read the buffers, and `open`'s leak, whether it succeeds,
reads only its buffers (`Proof/AesOcb/Scratch.lean`). As AES-GCM's `open`
(`Proof/AesGcm/RISCV64/Verified.lean`).
-/

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space: `tag` and `tag_len` alone on the stack. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x9000, 16⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ocb.sealContract RISCV64.abi 2592).pre s := by
  implies_sat [Spec.Ocb.sealContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Spec.Ocb.sealPost, RISCV64.abi,
    RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealFrameSat

theorem seal_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 «seal»)
      (Spec.Ocb.sealContract RISCV64.abi 2592) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.sealPre RISCV64.abi.ptrBits) (post := Spec.Ocb.sealPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2592) (m := 2) seal_verified (by decide) (by decide)
    (Proof.AesOcb.sealPre_local _) (Proof.AesOcb.sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space: `tag` and `tag_len` alone on the stack. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x9000, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ocb.openContract RISCV64.abi 2592).pre s := by
  implies_sat [Spec.Ocb.openContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Spec.Ocb.openPost, Spec.Ocb.openLeak,
    RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [openFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openFrameSat

theorem open_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 «open»)
      (Spec.Ocb.openContract RISCV64.abi 2592) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.openPre RISCV64.abi.ptrBits) (post := Spec.Ocb.openPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2592) (m := 2) (leak := some (Spec.Ocb.openLeak RISCV64.abi.ptrBits))
    open_verified (by decide) (by decide) (Proof.AesOcb.openPre_local _) (Proof.AesOcb.openPost_local _)
    openFrameSat_pre (hleak := Proof.AesOcb.openLeak_local _)

end VG.Proof.AesOcb.RISCV64
