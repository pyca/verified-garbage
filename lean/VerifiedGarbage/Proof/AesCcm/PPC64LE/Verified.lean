module

import VerifiedGarbage.Proof.AesCcm.PPC64LE.TopCT
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Seal
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Open
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesCcm.Scratch
public import VerifiedGarbage.Impl.AesCcm.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs

/-!
# AES-CCM on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, states satisfying the preconditions, and the shared contracts of
`Spec/Ccm/Contract.lean` with the working space as a last argument
(`Proof/AesCcm/Scratch.lean`), with no stack: a call (`bl`) stores nothing
in memory, and each function saves the return address in the working
space. Then the code in a frame that allocates the working space
(`Verified.stackScratchArgs`): it is the third stack argument, after `tag`
and `tag_len`, so the frame of 2688 bytes holds the frame's own header and
Parameter Save Area, a copy of those two, the address of the working space
and the working space.
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCcm.PPC64LE

/-! ## Correctness and constant time -/

theorem seal_correct (s : State) (hs : sealPPC64LE.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealPPC64LE.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := seal_wp hs
  exact ⟨t, s', he, ha, hp⟩

theorem open_correct (s : State) (hs : openPPC64LE.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openPPC64LE.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := open_wp hs
  exact ⟨t, s', he, ha, hp⟩

/-- A state satisfying the precondition of `vg_aes_ccm_seal`: a 7-byte nonce,
no associated data, no data, a 4-byte tag at `0x5000` and `work` at 0, the
three at `sp + 96`. -/
def sealSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r6 => 7 | .r7 => 0x3000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem a := bif Nat.beq a.toNat 0x8061 then 0x50 else bif Nat.beq a.toNat 0x8068 then 4 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x8060, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ccm_open`: as `sealSat`,
with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8060, 24⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0, 2560⟩] }

/-! ## The shared contracts -/

theorem seal_verified :
    Verified PPC64LE.target «seal» (Proof.AesCcm.sealScratchContract PPC64LE.abi) :=
  Verified.of_correct seal_correct seal_ct
      { pre := by
          intro s h
          sig_pre [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
            Spec.Ccm.sealPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
            PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop] at h
          sig_split h
          sig_reduce [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
            Spec.Ccm.sealPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
            PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
          sig_and_intros
          sig_close
          all_goals first
            | with_reducible assumption
            | sig_disjoint_symm
            | omega
            | bv_omega
        post := by
          sig_implies_post [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
            Spec.Ccm.sealPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
            PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
        pub := by
          sig_implies_pub [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
            Spec.Ccm.sealPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
            PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
        sat := by
          sig_implies_sat [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
            Spec.Ccm.sealPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
            PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
            [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat }

theorem open_verified :
    Verified PPC64LE.target «open» (Proof.AesCcm.openScratchContract PPC64LE.abi) :=
  Verified.of_correct open_correct open_ct
      { pre := by
          intro s h
          sig_pre [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
            Spec.Ccm.openPost, Spec.Ccm.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes, openLeak, args,
            rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop] at h
          sig_split h
          sig_reduce [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
            Spec.Ccm.openPost, Spec.Ccm.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes, openLeak, args,
            rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop]
          sig_and_intros
          sig_close
          all_goals first
            | with_reducible assumption
            | sig_disjoint_symm
            | omega
            | bv_omega
        post := by
          sig_implies_post [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
            Spec.Ccm.openPost, Spec.Ccm.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes, openLeak, args,
            rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop]
        pub := by
          sig_implies_pub [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
            Spec.Ccm.openPost, Spec.Ccm.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes, openLeak, args,
            rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop]
        sat := by
          sig_implies_sat [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
            Spec.Ccm.openPost, Spec.Ccm.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes, openLeak, args,
            rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop]
            [openSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

/-! ## The working space on the stack -/

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x8060, 16⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ccm.sealContract PPC64LE.abi 2688).pre s := by
  implies_sat [Spec.Ccm.sealContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Spec.Ccm.sealPost,
    PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 «seal»)
      (Spec.Ccm.sealContract PPC64LE.abi 2688) :=
  Verified.stackScratchArgs (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.sealPre PPC64LE.abi.ptrBits)
    (post := Spec.Ccm.sealPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2688) (m := 2)
    seal_verified (by decide) (by decide) (Proof.AesCcm.sealPre_local _) (Proof.AesCcm.sealPost_local _)
    sealFrameSat_pre

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8060, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ccm.openContract PPC64LE.abi 2688).pre s := by
  implies_sat [Spec.Ccm.openContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Spec.Ccm.openPost,
    Spec.Ccm.openLeak, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr,
    List.getD, List.range, List.range.loop] [openFrameSat, openSat, sealSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 «open»)
      (Spec.Ccm.openContract PPC64LE.abi 2688) :=
  Verified.stackScratchArgs (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.openPre PPC64LE.abi.ptrBits)
    (post := Spec.Ccm.openPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2688) (m := 2)
    (leak := some (Spec.Ccm.openLeak PPC64LE.abi.ptrBits))
    open_verified (by decide) (by decide) (Proof.AesCcm.openPre_local _) (Proof.AesCcm.openPost_local _)
    openFrameSat_pre (hleak := Proof.AesCcm.openLeak_local _)

end VG.Proof.AesCcm.PPC64LE
