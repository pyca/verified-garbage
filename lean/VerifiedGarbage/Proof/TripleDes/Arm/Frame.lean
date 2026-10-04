import VerifiedGarbage.Proof.TripleDes.Arm.Key.Verified
import VerifiedGarbage.Proof.TripleDes.Arm.Ecb.Verified
import VerifiedGarbage.Proof.TripleDes.Scratch
import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe

/-!
# Triple DES key expansion and ECB on ARMv7, with their working space on the stack

Key expansion's and ECB's working space is their fourth argument, in `r3`:
they run their code, proved with it as an argument, in a frame that is the
working space and which they zero after the code, since it may hold the key
schedule and the data (`Verified.regScratchWiped`): 512 bytes for key
expansion and 1024 for ECB.
-/

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm

/-- A state satisfying `vg_triple_des_expand_key`'s precondition: a 16-byte
key at `0x1000` and the schedule at `0x2000`. -/
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
  wr := [⟨0x2000, 384⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.TripleDes.expandKeyContract Arm.abi 512).pre s := by
  implies_sat [Spec.TripleDes.expandKeyContract, Spec.TripleDes.expandKeySig,
    Spec.TripleDes.expandKeyPre, Spec.TripleDes.expandKeyPost, Spec.TripleDes.validKey, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [expandKeyFrameSat] using expandKeyFrameSat

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000` and no blocks at `0x2000`. -/
def ecbFrameSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩]

theorem ecbFrameSat_pre (d : Spec.TripleDes.Direction) :
    ∃ s, (Spec.TripleDes.ecbContract Arm.abi d 1024).pre s := by
  implies_sat [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, Spec.TripleDes.ecbPost, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [ecbFrameSat] using ecbFrameSat

theorem expandKey_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128
      Impl.TripleDes.Arm.Key.expandKey)
      (Spec.TripleDes.expandKeyContract Arm.abi 512) :=
  Arm.Verified.regScratchWiped (sig := Spec.TripleDes.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 64) (pre := Spec.TripleDes.expandKeyPre Arm.abi.ptrBits)
    (post := Spec.TripleDes.expandKeyPost Arm.abi.ptrBits) (wa := false) (stack := 0)
    Key.verified (by decide) (by decide) (by decide) (by decide)
    (Proof.TripleDes.expandKeyPostOut_local _) expandKeyFrameSat_pre

theorem ecb_framed {c : Prog isa} {d : Spec.TripleDes.Direction}
    (h : Verified Arm.target c (Proof.TripleDes.ecbScratchContract Arm.abi d 0)) :
    Verified Arm.target (Impl.StackScratch.Arm.withRegScratchWiped 1024 .r3 256 c)
      (Spec.TripleDes.ecbContract Arm.abi d 1024) :=
  Arm.Verified.regScratchWiped (sig := Spec.TripleDes.ecbSig) (nm := "scratch") (e := .u64)
    (n := 128) (post := Spec.TripleDes.ecbPost d Arm.abi.ptrBits) (wa := true) (stack := 0)
    h (by decide) (by decide) (by decide) (by decide) (Proof.TripleDes.ecbPostOut_local _ d)
    (ecbFrameSat_pre d)

end VG.Proof.TripleDes.Arm
