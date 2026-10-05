import VerifiedGarbage.Proof.Aes.AArch64.ExpandKey
import VerifiedGarbage.Proof.Aes.AArch64.Aese.ExpandKey
import VerifiedGarbage.Proof.Aes.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe

/-!
# The AES key expansion on AArch64, with its working space on the stack

`vg_aes_expand_key` and `vg_aes_expand_key_aes` run the code of
`vg_aes_expand_key_scratch` and `vg_aes_expand_key_scratch_aes`, proved
with the working space as an argument, in a frame of 512 bytes that is the
working space and which they zero after the code
(`Verified.stackScratchWiped`), since it may hold the key and its schedule.
The code uses no other stack.
-/

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64

/-- A state satisfying `vg_aes_expand_key`'s precondition: a 16-byte key at
`0x1000` and the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 240⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Aes.expandKeyContract AArch64.abi 512).pre s := by
  implies_sat [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig, Spec.Aes.expandKeyPre,
    Spec.Aes.expandKeyPost, AArch64.abi, AArch64.argRegs] [expandKeyFrameSat] using expandKeyFrameSat

/-- The code `c` of `vg_aes_expand_key_scratch` or of one of its variants,
proved with its working space as an argument and no stack, in its frame. -/
theorem expandKey_framed {c : Prog isa}
    (h : Verified AArch64.target c (Spec.Aes.expandKeyScratchContract AArch64.abi)) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 512 .x3 64 c)
      (Spec.Aes.expandKeyContract AArch64.abi 512) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Aes.expandKeySig) (nm := "scratch")
    (e := .u64) (n := 64) (pre := Spec.Aes.expandKeyPre AArch64.abi.ptrBits)
    (post := Spec.Aes.expandKeyPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 512) (Proof.Aes.expandKey_scratch h) (by decide) (by decide) (by decide)
    (Proof.Aes.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Aes.AArch64
