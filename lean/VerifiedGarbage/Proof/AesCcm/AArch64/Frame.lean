module

public import VerifiedGarbage.Proof.AesCcm.Scratch
import VerifiedGarbage.Proof.AesCcm.AArch64.OpenCT
import VerifiedGarbage.Proof.AesCcm.AArch64.SealCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesCcm.AArch64
public import VerifiedGarbage.Proof.AesCcm.AArch64.Contract
public import VerifiedGarbage.Proof.CmacAes.AArch64.Variant
import VerifiedGarbage.Proof.AesCcm.AArch64.Open
import VerifiedGarbage.Proof.AesCcm.AArch64.Seal
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-! ### `AesCcm.AArch64.Verified`, which only this module used -/

section

/-!
# AES-CCM on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementation `v` of `vg_cmac_aes_update`, with the `vg_aes_ctr32`
that goes with it), states satisfying the preconditions, and the shared
contracts of `Spec/Ccm/Contract.lean` with the working space as a last
argument (`Proof/AesCcm/Scratch.lean`), with no stack: the calls keep the
return address in `x30`, which each function saves in the working space.
`Frame.lean` allocates the working space.
-/

@[expose] public section

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.Impl.AesCcm.AArch64

/-! ## v8–v15 -/

theorem seal_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) :
    («seal» v.callee v.ctr.callee).allInstrs keepsV = true := by
  simp only [«seal», mac, b0, flagsSeg, aadHead, header, absorbPad, absTail, updBlock, tag, ctr, ctrChunk,
    ctrTail, ctrs, tagOut, callUpdate, callCtr, Code.allInstrs, v.keepsV, v.ctr.keepsV]
  decide +kernel

theorem open_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) :
    («open» v.callee v.ctr.callee).allInstrs keepsV = true := by
  simp only [«open», mac, b0, flagsSeg, aadHead, header, absorbPad, absTail, updBlock, tag, ctr, ctrChunk,
    ctrTail, ctrs, cmp, mask, callUpdate, callCtr, Code.allInstrs, v.keepsV, v.ctr.keepsV]
  decide +kernel

/-! ## Correctness and constant time -/

theorem seal_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa («seal» v.callee v.ctr.callee) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (seal_wp v hs) (seal_keepsV v)

theorem open_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa («open» v.callee v.ctr.callee) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (open_wp v hs) (open_keepsV v)

/-- A state satisfying the precondition of `vg_aes_ccm_seal`: a 7-byte nonce,
no associated data, no data, a 4-byte tag at `0x5000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 7 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8008 then 4 else if a = 0x8001 then 0x50 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x8000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ccm_open`: as `sealSat`,
with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0, 2560⟩] }

/-! ## The shared contracts -/

theorem seal_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target («seal» v.callee v.ctr.callee) (Proof.AesCcm.sealScratchContract AArch64.abi) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre, Proof.AesCcm.sealRoundsPost,
      sealAArch64, sealPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem open_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target («open» v.callee v.ctr.callee) (Proof.AesCcm.openScratchContract AArch64.abi) :=
  Verified.of_correct (open_correct v) (open_ct v) (by
    sig_implies [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre, Proof.AesCcm.openRoundsPost,
      Spec.Ccm.openLeak, openAArch64, openPre, oneLay, onePub, openRes, openLeak, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [openSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat)

end VG.Proof.AesCcm.AArch64

end

end


/-!
# AES-CCM on AArch64, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackArgScratch`): their working space is their third stack
argument, after `tag` and `tag_len`, so the frame of 2592 bytes holds a copy
of those two, the address of the working space and the working space, at the
next 16-byte boundary. The code itself uses no stack: its calls keep the
return address in `x30`. `open`'s leak, whether it succeeds, reads only its
buffers (`openLeak_local`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.Impl.AesCcm.AArch64

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesCcm.sealRoundsContract AArch64.abi 2592).pre s := by
  implies_sat [Proof.AesCcm.sealRoundsContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Proof.AesCcm.sealRoundsPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («seal» v.callee v.ctr.callee))
      (Proof.AesCcm.sealRoundsContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.sealPre AArch64.abi.ptrBits)
    (post := Proof.AesCcm.sealRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (seal_verified v) (by decide) (by decide) (sealPre_local _) (sealPost_local _)
    (sealPostOut_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesCcm.openRoundsContract AArch64.abi 2592).pre s := by
  implies_sat [Proof.AesCcm.openRoundsContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Proof.AesCcm.openRoundsPost,
    Spec.Ccm.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
    List.getD, List.range, List.range.loop] [openFrameSat, openSat, sealSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («open» v.callee v.ctr.callee))
      (Proof.AesCcm.openRoundsContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.openPre AArch64.abi.ptrBits)
    (post := Proof.AesCcm.openRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (leak := some (Spec.Ccm.openLeak AArch64.abi.ptrBits))
    (open_verified v) (by decide) (by decide) (openPre_local _) (openPost_local _)
    (openPostOut_local _) openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesCcm.AArch64
