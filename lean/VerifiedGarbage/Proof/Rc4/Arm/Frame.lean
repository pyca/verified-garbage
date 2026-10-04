import VerifiedGarbage.Proof.Rc4.Arm.Verified
import VerifiedGarbage.Proof.Rc4.Scratch
import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe

/-!
# RC4 on ARMv7, with the working space on the stack

The working space of `vg_rc4_init` and `vg_rc4_apply`, where they keep our
caller's `r4`–`r11`, was their fourth argument, in `r3`: they run their code,
proved with it as an argument (`Verified.lean`), in a frame of 64 bytes that
is the working space and which they zero after the code
(`Verified.regScratchWiped`). The code uses no other stack. The frame passes
`vg_rc4_apply`'s arguments in the same registers and memory, so its leak, the
context's `i`, is the code's.
-/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm

/-- A state satisfying `vg_rc4_init`'s precondition: a 1-byte key at
`0x1000` and the context at `0x2000`. -/
def initFrameSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 258⟩]

theorem initFrameSat_pre : ∃ s, (Spec.Rc4.initContract Arm.abi 64).pre s := by
  implies_sat [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [initFrameSat] using initFrameSat

/-- A state satisfying `vg_rc4_apply`'s precondition: the context at
`0x1000` and 1 byte of data at `0x2000`. -/
def applyFrameSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 258⟩, ⟨0x2000, 1⟩]

theorem applyFrameSat_pre : ∃ s, (Spec.Rc4.applyContract Arm.abi 64).pre s := by
  implies_sat [Spec.Rc4.applyContract, Spec.Rc4.applySig, Spec.Rc4.applyPost,
    Spec.Rc4.applyLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [applyFrameSat] using applyFrameSat

theorem init_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.init)
      (Spec.Rc4.initContract Arm.abi 64) :=
  Arm.Verified.regScratchWiped (sig := Spec.Rc4.initSig) (nm := "scratch") (e := .u64) (n := 8)
    (post := Spec.Rc4.initPost Arm.abi.ptrBits) (wa := true) (stack := 0)
    init_verified (by decide) (by decide) (by decide) (by decide)
    (Proof.Rc4.initPostOut_local _) initFrameSat_pre

theorem apply_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.apply)
      (Spec.Rc4.applyContract Arm.abi 64) :=
  Arm.Verified.regScratchWiped (sig := Spec.Rc4.applySig) (nm := "scratch") (e := .u64) (n := 8)
    (post := Spec.Rc4.applyPost Arm.abi.ptrBits) (wa := true) (stack := 0)
    (leak := some (Spec.Rc4.applyLeak Arm.abi.ptrBits))
    apply_verified (by decide) (by decide) (by decide) (by decide)
    (Proof.Rc4.applyPostOut_local _) applyFrameSat_pre

end VG.Proof.Rc4.Arm
