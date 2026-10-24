module

import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.TopCT
public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Seal
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Open
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesGcmSiv.Scratch
public import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args
public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs

/-!
# AES-GCM-SIV on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, given that the tag input computed with GHASH is the RFC's
(`TagInputEq`, which the registration file binds to
`Proof.GcmSiv.Polyval.tagInput_eq_tagInputG`, so that only that leaf
imports its algebra), a state satisfying each
precondition, and the shared contracts of `Spec/GcmSiv/Contract.lean` with
the working space as a last argument (`Proof/AesGcmSiv/Scratch.lean`, 478
doublewords), with no stack: a call (`bl`) stores nothing in memory, and
each function saves the return address in the working space. Then the code
in a frame that allocates the working space (`Verified.stackScratchArgs`):
it is the first stack argument, so the frame of 3936 bytes holds the
frame's own header and Parameter Save Area, the address of the working
space and the working space.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcmSiv.PPC64LE

/-! ## Correctness and constant time -/

theorem seal_correct (hti : TagInputEq) (s : State) (hs : sealPPC64LE.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealPPC64LE.post s s' :=
  seal_wp hti hs

theorem open_correct (hti : TagInputEq) (s : State) (hs : openPPC64LE.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openPPC64LE.post s s' :=
  open_wp hti hs

/-- A state satisfying the precondition of `vg_aes_gcm_siv_seal`: no
additional data, no data, the tag at `0x4800` and `work` at `0x5000`, its
address at `sp + 96`. -/
def sealSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r6 => 0x3000 | .r8 => 0x4000 | .r10 => 0x4800 | _ => 0
  lr := 0
  sp := 0x8000
  mem a := bif Nat.beq a.toNat 0x8061 then 0x50 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x8060, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x4800, 16⟩, ⟨0x5000, 3824⟩]

/-- A state satisfying the precondition of `vg_aes_gcm_siv_open`: as
`sealSat`, with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x4800, 16⟩, ⟨0x8060, 8⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 3824⟩] }

/-! ## The shared contracts -/

theorem seal_verified (hti : TagInputEq) :
    Verified PPC64LE.target «seal» (Proof.AesGcmSiv.sealScratchContract PPC64LE.abi 478) :=
  Verified.of_correct (seal_correct hti) seal_ct
      { pre := by
          intro s h
          sig_pre [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
            Spec.GcmSiv.sealPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds, PPC64LE.abi,
            PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop] at h
          sig_split h
          sig_reduce [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
            Spec.GcmSiv.sealPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds, PPC64LE.abi,
            PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
          sig_and_intros
          sig_close
          all_goals first
            | with_reducible assumption
            | sig_disjoint_symm
            | omega
            | bv_omega
        post := by
          sig_implies_post [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig,
            Spec.GcmSiv.sealPre, Spec.GcmSiv.sealPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds,
            PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop]
        pub := by
          sig_implies_pub [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig,
            Spec.GcmSiv.sealPre, Spec.GcmSiv.sealPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds,
            PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop]
        sat := by
          sig_implies_sat [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig,
            Spec.GcmSiv.sealPre, Spec.GcmSiv.sealPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds,
            PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop]
            [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat }

theorem open_verified (hti : TagInputEq) :
    Verified PPC64LE.target «open» (Proof.AesGcmSiv.openScratchContract PPC64LE.abi 478) :=
  Verified.of_correct (open_correct hti) open_ct
      { pre := by
          intro s h
          sig_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
            Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes, openOut,
            args, rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD,
            List.range, List.range.loop] at h
          sig_split h
          sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
            Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes, openOut,
            args, rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD,
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
            Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes,
            args, rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD,
            List.range, List.range.loop]
          sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
            Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes,
            args, rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD,
            List.range, List.range.loop] at h
          intro _
          unfold openOut at h
          split at h <;> rename_i heq <;> rw [heq] <;> exact h
        pub := by
          sig_implies_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
            Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openPPC64LE, openPre, oneLay,
            onePub, openRes, openOut, args, rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg,
            PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
        sat := by
          sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
            Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openPPC64LE, openPre, oneLay,
            onePub, openRes, openOut, args, rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg,
            PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
            [openSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

/-! ## The working space on the stack -/

/-- A state satisfying `vg_aes_gcm_siv_seal`'s precondition, without the
working space: no stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩], wr := [⟨0x4000, 0⟩, ⟨0x4800, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.GcmSiv.sealContract PPC64LE.abi 3936).pre s := by
  implies_sat [Spec.GcmSiv.sealContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, Spec.GcmSiv.sealPost,
    PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed (hti : TagInputEq) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 3936 0 «seal»)
      (Spec.GcmSiv.sealContract PPC64LE.abi 3936) :=
  Verified.stackScratchArgs (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
    (n := 478) (pre := Spec.GcmSiv.sealPre PPC64LE.abi.ptrBits)
    (post := Spec.GcmSiv.sealPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0) (bytes := 3936) (m := 0)
    (seal_verified hti) (by decide) (by decide) (Proof.AesGcmSiv.sealPre_local _) (Proof.AesGcmSiv.sealPost_local _)
    sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_siv_open`'s precondition, without the
working space: no stack arguments. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x4800, 16⟩], wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.GcmSiv.openContract PPC64LE.abi 3936).pre s := by
  implies_sat [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, Spec.GcmSiv.openPost,
    Spec.GcmSiv.openLeak, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr,
    List.getD, List.range, List.range.loop] [openFrameSat, sealSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed (hti : TagInputEq) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 3936 0 «open»)
      (Spec.GcmSiv.openContract PPC64LE.abi 3936) :=
  Verified.stackScratchArgs (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
    (n := 478) (pre := Spec.GcmSiv.openPre PPC64LE.abi.ptrBits)
    (post := Spec.GcmSiv.openPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0) (bytes := 3936) (m := 0)
    (leak := some (Spec.GcmSiv.openLeak PPC64LE.abi.ptrBits))
    (Proof.AesGcmSiv.Verified.of_openScratch (open_verified hti)) (by decide) (by decide)
    (Proof.AesGcmSiv.openPre_local _) (Proof.AesGcmSiv.openPost_local _)
    openFrameSat_pre (hleak := Proof.AesGcmSiv.openLeak_local _)

end VG.Proof.AesGcmSiv.PPC64LE
