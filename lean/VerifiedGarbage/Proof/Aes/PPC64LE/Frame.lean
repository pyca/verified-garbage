module
public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Target

import VerifiedGarbage.Proof.Aes.PPC64LE.ExpandKey
import VerifiedGarbage.Proof.Aes.Scratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
public import VerifiedGarbage.Impl.Aes.PPC64LE.ExpandKey
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The AES key expansion on PPC64LE, with its working space on the stack

`vg_aes_expand_key` runs the code of `vg_aes_expand_key_scratch`, proved with
the working space as an argument, in a frame that allocates it and zeroes it
after the code (`Verified.stackScratchWiped`), since it may hold the key and
its schedule: 544 bytes, the frame's 32-byte header and the 512 of working
space. The code uses no other stack.
-/

@[expose] public section

namespace VG.Proof.Aes.PPC64LE

open VG VG.PPC64LE

/-- A state satisfying `vg_aes_expand_key`'s precondition: a 16-byte key at
`0x1000` and the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 240⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Aes.expandKeyContract PPC64LE.abi 544).pre s := by
  implies_sat [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig, Spec.Aes.expandKeyPre,
    Spec.Aes.expandKeyPost, PPC64LE.abi, PPC64LE.argRegs] [expandKeyFrameSat] using expandKeyFrameSat

theorem expandKey_framed :
    Verified PPC64LE.target
      (Impl.StackScratch.PPC64LE.withStackScratchWiped 544 .r6 64 Impl.Aes.PPC64LE.expandKey)
      (Spec.Aes.expandKeyContract PPC64LE.abi 544) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Aes.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 64) (pre := Spec.Aes.expandKeyPre PPC64LE.abi.ptrBits)
    (post := Spec.Aes.expandKeyPost PPC64LE.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 544) (words := 64) (Proof.Aes.expandKey_scratch expandKey_verified) (by decide)
    (by decide) (by decide) (Proof.Aes.expandKeyPre_local _) (Proof.Aes.expandKeyPost_local _)
    (Proof.Aes.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Aes.PPC64LE
