module

import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.VerifyMsgCT
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed25519.WholeLocal
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
public import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# `vg_ed25519_verify` on RISC-V, verified

The code meets `verifyContract` with the frame (34 doublewords, so aligned
as the contract's `u64` buffers are) as one more argument
(`Sig.scratchContract`) and 208 bytes of stack for the callees' frames: the
proof against the contract's facts by register (`verC`), which it implies,
and a state satisfying it. In a frame of 272 bytes on the stack
(`Verified.stackScratchL`), it meets the contract itself.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole

/-- A state satisfying the precondition. -/
def verSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | .a4 => 0x4000 | .a5 => 0x8000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 0⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩, ⟨0x8000, 272⟩]

theorem verify_verified :
    Verified RISCV64.target verifyMessage (Sig.scratchContract RISCV64.abi Spec.Ed25519.verifySig "frame" .u64 34
      (Curry.const (fun _ => True) _) (Proof.Ed25519.WholeLocal.verifyPost RISCV64.abi.ptrBits) true 208
      (some (Proof.Ed25519.WholeLocal.verifyLeak RISCV64.abi.ptrBits))) :=
  Verified.of_correct ver_ok ver_ct (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.verifyPost, Proof.Ed25519.WholeLocal.verifyLeak, verC,
      verResult, RISCV64.abi, RISCV64.argRegs] [verSat] using verSat)

/-- A state satisfying `vg_ed25519_verify`'s precondition, without the frame. -/
def verFrameSat : State := { verSat with wr := [⟨0x4000, 8192⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Ed25519.verifyContract RISCV64.abi (208 + 272)).pre s := by
  implies_sat [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig, Spec.Ed25519.scratchWords, RISCV64.abi,
    RISCV64.argRegs] [verFrameSat, verSat] using verFrameSat

/-- In its frame of 272 bytes. -/
theorem verify_framed :
    Verified RISCV64.target verifyCode (Spec.Ed25519.verifyContract RISCV64.abi (208 + 272)) :=
  Verified.stackScratchL (sig := Spec.Ed25519.verifySig) (nm := "frame") (e := .u64) (n := 34)
    (post := Proof.Ed25519.WholeLocal.verifyPost RISCV64.abi.ptrBits) (wa := true) (stack := 208) (bytes := 272)
    (leak := some (Proof.Ed25519.WholeLocal.verifyLeak RISCV64.abi.ptrBits)) verify_verified (by decide)
    (by decide) verFrameSat_pre

end VG.Proof.Ed25519.RISCV64.Whole
