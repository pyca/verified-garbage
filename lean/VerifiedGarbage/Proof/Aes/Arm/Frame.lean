import VerifiedGarbage.Proof.Aes.Arm.ExpandKey
import VerifiedGarbage.Proof.Aes.Scratch
import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe

/-!
# The AES key expansion on ARMv7, with its working space on the stack

The working space of `vg_aes_expand_key_scratch` is its fourth argument, in
`r3`: `vg_aes_expand_key` runs its code, proved with it as an argument, in a
frame of 512 bytes that is the working space and which it zeroes after the
code, since it may hold the key and its schedule
(`Verified.regScratchWiped`). The code uses no other stack.
-/

namespace VG.Proof.Aes.Arm

open VG VG.Arm

/-- A state satisfying `vg_aes_expand_key`'s precondition: a 16-byte key at
`0x1000` and the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 16 | .r2 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 240⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Aes.expandKeyContract Arm.abi 512).pre s := by
  implies_sat [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig, Spec.Aes.expandKeyPre,
    Spec.Aes.expandKeyPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [expandKeyFrameSat] using expandKeyFrameSat

theorem expandKey_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128 Impl.Aes.Arm.expandKey)
      (Spec.Aes.expandKeyContract Arm.abi 512) :=
  Arm.Verified.regScratchWiped (sig := Spec.Aes.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 64) (pre := Spec.Aes.expandKeyPre Arm.abi.ptrBits)
    (post := Spec.Aes.expandKeyPost Arm.abi.ptrBits) (wa := false) (stack := 0)
    (Proof.Aes.expandKey_scratch expandKey_verified) (by decide) (by decide) (by decide)
    (by decide) (Proof.Aes.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Aes.Arm
