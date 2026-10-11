import VerifiedGarbage.Proof.Blowfish.Arm.Verified
import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe

/-!
# Blowfish on ARMv7, with the working space on the stack

Key expansion and ECB keep our caller's `r4`–`r11` and `lr`, and their
pointer and counter, in working space that was their fourth argument, in
`r3`: they run their code, proved with it as an argument (`Verified.lean`),
in a frame that is the working space (64 bytes for key expansion, 256 for
ECB, of which each uses the first 44) and whose first 48 bytes they zero
after the code (`Verified.regScratchWiped`). The code uses no other stack.
-/

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm

/-- A state satisfying `vg_blowfish_expand_key`'s precondition: a 4-byte key
at `0x1000` and the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 4 | .r2 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 4⟩]
  wr := [⟨0x2000, 4168⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Blowfish.expandKeyContract Arm.abi 64).pre s := by
  implies_sat [Spec.Blowfish.expandKeyContract, Spec.Blowfish.expandKeySig, Spec.Blowfish.expandKeyPre,
    Spec.Blowfish.expandKeyPost, Spec.Blowfish.validKey, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [expandKeyFrameSat] using expandKeyFrameSat

theorem expandKey_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 12 Impl.Blowfish.Arm.expandKey)
      (Spec.Blowfish.expandKeyContract Arm.abi 64) :=
  Arm.Verified.regScratchWiped (sig := Spec.Blowfish.expandKeySig) (nm := "scratch") (e := .u64) (n := 8)
    (pre := Spec.Blowfish.expandKeyPre Arm.abi.ptrBits) (post := Spec.Blowfish.expandKeyPost Arm.abi.ptrBits)
    (wa := false) (stack := 0)
    expandKey_verified (by decide) (by decide) (by decide) (by decide)
    (Proof.Blowfish.expandKeyPostOut_local _) expandKeyFrameSat_pre

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000` and no data at `0x3000`. -/
def ecbFrameSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 0⟩]

theorem ecbFrameSat_pre (d : Spec.Blowfish.Direction) : ∃ s, (Spec.Blowfish.ecbContract Arm.abi d 256).pre s := by
  implies_sat [Spec.Blowfish.ecbContract, Spec.Blowfish.ecbSig, Spec.Blowfish.ecbPost, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [ecbFrameSat] using ecbFrameSat

theorem ecb_framed (up : Bool) :
    Verified Arm.target (Impl.StackScratch.Arm.withRegScratchWiped 256 .r3 12 (Impl.Blowfish.Arm.ecb up))
      (Spec.Blowfish.ecbContract Arm.abi (dir up) 256) :=
  Arm.Verified.regScratchWiped (sig := Spec.Blowfish.ecbSig) (nm := "scratch") (e := .u64) (n := 32)
    (post := Spec.Blowfish.ecbPost (dir up) Arm.abi.ptrBits) (wa := true) (stack := 0)
    (ecb_verified up) (by decide) (by decide) (by decide) (by decide)
    (Proof.Blowfish.ecbPostOut_local _ (dir up)) (ecbFrameSat_pre (dir up))

end VG.Proof.Blowfish.Arm
