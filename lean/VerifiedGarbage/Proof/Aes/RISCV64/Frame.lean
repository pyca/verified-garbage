module
public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Target

import VerifiedGarbage.Proof.Aes.RISCV64.ExpandKeyVerified
import VerifiedGarbage.Proof.Aes.Scratch
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Impl.Aes.RISCV64.ExpandKey
import VerifiedGarbage.Proof.Framework.Contract

/-!
# The AES key expansion on RISC-V, with its working space on the stack

`vg_aes_expand_key` runs the code of `vg_aes_expand_key_scratch`, proved with
the working space as an argument, in a frame that allocates it and zeroes it
after the code (`Verified.stackScratchWiped`), since it may hold the key and
its schedule: 512 bytes, all working space. The code uses no other stack.
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64

/-- A state satisfying `vg_aes_expand_key`'s precondition: a 16-byte key at
`0x1000` and the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 240⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Aes.expandKeyContract RISCV64.abi 512).pre s := by
  implies_sat [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig, Spec.Aes.expandKeyPre,
    Spec.Aes.expandKeyPost, RISCV64.abi, RISCV64.argRegs] [expandKeyFrameSat] using expandKeyFrameSat

theorem expandKey_framed :
    Verified RISCV64.target
      (Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a3 64 Impl.Aes.RISCV64.expandKey)
      (Spec.Aes.expandKeyContract RISCV64.abi 512) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Aes.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 64) (pre := Spec.Aes.expandKeyPre RISCV64.abi.ptrBits)
    (post := Spec.Aes.expandKeyPost RISCV64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 512) (words := 64) (Proof.Aes.expandKey_scratch expandKey_verified) (by decide)
    (by decide) (by decide) (Proof.Aes.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Aes.RISCV64
