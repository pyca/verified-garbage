module

public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Seal
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesGcmSiv.Scratch
public import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Contract
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.TopCT
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Open
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs

/-!
# AES-GCM-SIV on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcmSiv/PPC64LE/Verified.lean`): correctness and constant time,
given that the tag input computed with GHASH is the RFC's (`TagInputEq`,
which the registration file binds to
`Proof.GcmSiv.Polyval.tagInput_eq_tagInputG`), a state satisfying each
precondition, and the shared contracts of `Spec/GcmSiv/Contract.lean` with
the working space as a last argument (`Proof/AesGcmSiv/Scratch.lean`, 480
doublewords) and the 2048 bytes of stack `vg_ghash`'s frame takes. Then the
code in a frame that allocates the working space
(`Verified.stackScratchArgs`): it is the one stack argument, so the frame of
3856 bytes holds its address and the working space.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcmSiv.RISCV64
open VG.Proof.AesGcm.RISCV64 (stkOk stkAll)

/-! ## Correctness and constant time -/

theorem seal_correct (hti : TagInputEq) (s : State) (hs : sealRISCV64.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealRISCV64.post s s' :=
  seal_wp hti hs

theorem open_correct (hti : TagInputEq) (s : State) (hs : openRISCV64.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openRISCV64.post s s' :=
  open_wp hti hs

/-- A state satisfying the precondition of `vg_aes_gcm_siv_seal`: no
additional data, no data, the tag at `0x5000` and `work` at `0x6000`, its
address at `sp`. -/
def sealSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a3 => 0x3000 | .a5 => 0x4000 | .a7 => 0x5000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x60 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x9000, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩, ⟨0x6000, 3840⟩]

/-- A state satisfying the precondition of `vg_aes_gcm_siv_open`: as
`sealSat`, with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x9000, 8⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x6000, 3840⟩] }

/-! ## The shared contracts -/

theorem seal_verified (hti : TagInputEq) :
    Verified RISCV64.target «seal» (Proof.AesGcmSiv.sealScratchContract RISCV64.abi 480 2048) :=
  Verified.of_correct (seal_correct hti) seal_ct
      { pre := by
          intro s h
          sig_pre [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
            Spec.GcmSiv.sealPost, sealRISCV64, sealPre, oneLay, onePub, args, rounds, RISCV64.abi,
            RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, stackBelow, stkOk, stkAll, and_true, List.getD, List.range,
            List.range.loop] at h
          sig_split h
          sig_reduce [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
            Spec.GcmSiv.sealPost, sealRISCV64, sealPre, oneLay, onePub, args, rounds, RISCV64.abi,
            RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, stackBelow, stkOk, stkAll, and_true, List.getD, List.range,
            List.range.loop]
          sig_and_intros
          sig_close
          all_goals first
            | with_reducible assumption
            | sig_disjoint_symm
            | omega
            | bv_omega
        post := by
          sig_implies_post [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig,
            Spec.GcmSiv.sealPre, Spec.GcmSiv.sealPost, sealRISCV64, sealPre, oneLay, onePub, args, rounds,
            RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, stackBelow, stkOk, stkAll, and_true, List.getD, List.range,
            List.range.loop]
        pub := by
          sig_implies_pub [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig,
            Spec.GcmSiv.sealPre, Spec.GcmSiv.sealPost, sealRISCV64, sealPre, oneLay, onePub, args, rounds,
            RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, stackBelow, stkOk, stkAll, and_true, List.getD, List.range,
            List.range.loop]
        sat := by
          sig_implies_sat [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig,
            Spec.GcmSiv.sealPre, Spec.GcmSiv.sealPost, sealRISCV64, sealPre, oneLay, onePub, args, rounds,
            RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, stackBelow, stkOk, stkAll, and_true, List.getD, List.range,
            List.range.loop]
            [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat }

theorem open_verified (hti : TagInputEq) :
    Verified RISCV64.target «open» (Proof.AesGcmSiv.openScratchContract RISCV64.abi 480 2048) :=
  Verified.of_correct (open_correct hti) open_ct
      { pre := by
          intro s h
          sig_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
            Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openRISCV64, openPre, oneLay, onePub, openRes, openOut,
            args, rounds, RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, stackBelow, stkOk, stkAll, and_true, List.getD,
            List.range, List.range.loop] at h
          sig_split h
          sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
            Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openRISCV64, openPre, oneLay, onePub, openRes, openOut,
            args, rounds, RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, stackBelow, stkOk, stkAll, and_true, List.getD,
            List.range, List.range.loop]
          sig_and_intros
          sig_close
          all_goals first
            | with_reducible assumption
            | sig_disjoint_symm
            | omega
            | bv_omega
        -- `h` and the goal match on the same outcome of `decryptWith` with
        -- different matchers (`openOut`'s and `openContract`'s): split on it
        -- rather than have `exact h` unfold both to unify them.
        post := by
          intro s s' _ h
          sig_post [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
            Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openRISCV64, openPre, oneLay, onePub, openRes,
            args, rounds, RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, stackBelow, stkOk, stkAll, and_true, List.getD,
            List.range, List.range.loop]
          sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
            Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openRISCV64, openPre, oneLay, onePub, openRes,
            args, rounds, RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, stackBelow, stkOk, stkAll, and_true, List.getD,
            List.range, List.range.loop] at h
          intro _
          unfold openOut at h
          split at h <;> rename_i heq <;> rw [heq] <;> exact h
        pub := by
          sig_implies_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
            Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openRISCV64, openPre, oneLay,
            onePub, openRes, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg,
            RISCV64.stackArgAddr, stackBelow, stkOk, stkAll, and_true, List.getD, List.range, List.range.loop]
        sat := by
          sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
            Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openRISCV64, openPre, oneLay,
            onePub, openRes, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg,
            RISCV64.stackArgAddr, stackBelow, stkOk, stkAll, and_true, List.getD, List.range, List.range.loop]
            [openSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

/-! ## The working space on the stack -/

/-- A state satisfying `vg_aes_gcm_siv_seal`'s precondition, without the
working space: no stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩], wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.GcmSiv.sealContract RISCV64.abi 5904).pre s := by
  implies_sat [Spec.GcmSiv.sealContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, Spec.GcmSiv.sealPost,
    RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, stackBelow, stkOk, stkAll, and_true, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed (hti : TagInputEq) :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 3856 0 «seal»)
      (Spec.GcmSiv.sealContract RISCV64.abi 5904) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
    (n := 480) (pre := Spec.GcmSiv.sealPre RISCV64.abi.ptrBits)
    (post := Spec.GcmSiv.sealPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048) (bytes := 3856) (m := 0)
    (seal_verified hti) (by decide) (by decide) (Proof.AesGcmSiv.sealPre_local _) (Proof.AesGcmSiv.sealPost_local _)
    sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_siv_open`'s precondition, without the
working space: no stack arguments. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x5000, 16⟩], wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.GcmSiv.openContract RISCV64.abi 5904).pre s := by
  implies_sat [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, Spec.GcmSiv.openPost,
    Spec.GcmSiv.openLeak, RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr,
    List.getD, List.range, List.range.loop] [openFrameSat, sealSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed (hti : TagInputEq) :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 3856 0 «open»)
      (Spec.GcmSiv.openContract RISCV64.abi 5904) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
    (n := 480) (pre := Spec.GcmSiv.openPre RISCV64.abi.ptrBits)
    (post := Spec.GcmSiv.openPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048) (bytes := 3856) (m := 0)
    (leak := some (Spec.GcmSiv.openLeak RISCV64.abi.ptrBits))
    (Proof.AesGcmSiv.Verified.of_openScratch (open_verified hti)) (by decide) (by decide)
    (Proof.AesGcmSiv.openPre_local _) (Proof.AesGcmSiv.openPost_local _)
    openFrameSat_pre (hleak := Proof.AesGcmSiv.openLeak_local _)

end VG.Proof.AesGcmSiv.RISCV64
