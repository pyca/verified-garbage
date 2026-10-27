module

import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.ByRegister
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.PublicKeyCT
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed25519.WholeLocal
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
public import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# `vg_ed25519_public_key` on RISC-V, verified

The code meets `publicKeyContract` with the frame (18 doublewords, so
aligned as the contract's `u64` buffers are) as one more argument
(`Sig.scratchContract`) and 208 bytes of stack for the callees' frames: the
proof against the contract's facts by register (`pkC`), which it implies,
and a state satisfying it. In a frame of 144 bytes on the stack whose first
136 it zeroes before returning (`Verified.stackScratchWiped`), it meets the
contract itself.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole

/-- A state satisfying the precondition. -/
def pkSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x4000 | .a3 => 0x8000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 144⟩]

theorem publicKey_verified :
    Verified RISCV64.target publicKey (Sig.scratchContract RISCV64.abi Spec.Ed25519.publicKeySig "frame" .u64 18
      (Curry.const (fun _ => True) _) (Proof.Ed25519.WholeLocal.publicKeyPost RISCV64.abi.ptrBits) true 208) :=
  Verified.of_correct pk_ok (publicKey_ct fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed25519.publicKeySig,
      Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.publicKeyPost, pkC, RISCV64.abi, RISCV64.argRegs]
      [pkSat] using pkSat)

/-- A state satisfying `vg_ed25519_public_key`'s precondition, without the frame. -/
def pkFrameSat : State := { pkSat with wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩] }

theorem pkFrameSat_pre : ∃ s, (Spec.Ed25519.publicKeyContract RISCV64.abi (208 + 144)).pre s := by
  implies_sat [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig, Spec.Ed25519.scratchWords, RISCV64.abi,
    RISCV64.argRegs] [pkFrameSat, pkSat] using pkFrameSat

/-- In its frame of 144 bytes, whose first 136 it zeroes before returning. -/
theorem publicKey_framed :
    Verified RISCV64.target publicKeyCode (Spec.Ed25519.publicKeyContract RISCV64.abi (208 + 144)) :=
  Verified.stackScratchWiped (sig := Spec.Ed25519.publicKeySig) (nm := "frame") (e := .u64) (n := 18)
    (post := Proof.Ed25519.WholeLocal.publicKeyPost RISCV64.abi.ptrBits) (wa := true) (stack := 208) (bytes := 144)
    (words := 17) publicKey_verified (by decide) (by decide) (by decide)
    (Proof.Ed25519.WholeLocal.publicKeyPostOut_local _) pkFrameSat_pre

end VG.Proof.Ed25519.RISCV64.Whole
