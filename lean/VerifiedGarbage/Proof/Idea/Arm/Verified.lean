import VerifiedGarbage.Proof.Idea.Arm.Ecb
import VerifiedGarbage.Proof.Idea.Arm.Invert
import VerifiedGarbage.Proof.Framework.Arm.RegScratch
import VerifiedGarbage.Impl.StackScratch.Arm

/-!
# Verified IDEA on ARMv7, with its saved registers on the stack

`vg_idea_ecb` and `vg_idea_invert_key` save the callee-saved registers they
use in a buffer passed in a register (`r3`, `r2`), proved with the buffer as
an argument (`Ecb.lean`, `Invert.lean`); `ecb_framed` and `invertKey_framed`
allocate it in a frame of their own (`Verified.regScratch`). The buffer only
ever holds the caller's registers, so it is not zeroed.
-/

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Impl.Idea.Arm

/-- A state satisfying the ECB precondition without the buffer. -/
def ecbFrameSat : State := { satState with wr := [⟨0x2000, 8⟩] }

theorem ecbFrameSat_pre : ∃ s, (Spec.Idea.ecbContract Arm.abi 32).pre s := by
  implies_sat [Spec.Idea.ecbContract, Spec.Idea.ecbSig, Spec.Idea.ecbPost, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [ecbFrameSat, satState] using ecbFrameSat

theorem ecb_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 32 .r3 ecb)
    (Spec.Idea.ecbContract Arm.abi 32) :=
  Arm.Verified.regScratch (sig := Spec.Idea.ecbSig) (nm := "scratch") (e := .u32) (n := 8)
    (post := Spec.Idea.ecbPost Arm.abi.ptrBits) (wa := false) (stack := 0) ecb_verified
    (by decide) (by decide) (by decide) ecbFrameSat_pre

/-- A state satisfying the inversion's precondition without the buffer. -/
def invertFrameSat : State := { invertSat with wr := [⟨0x2000, 104⟩] }

theorem invertFrameSat_pre : ∃ s, (Spec.Idea.invertKeyContract Arm.abi 24).pre s := by
  implies_sat [Spec.Idea.invertKeyContract, Spec.Idea.invertKeySig, Spec.Idea.invertKeyPost, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [invertFrameSat, invertSat]
    using invertFrameSat

theorem invertKey_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 24 .r2 invertKey)
    (Spec.Idea.invertKeyContract Arm.abi 24) :=
  Arm.Verified.regScratch (sig := Spec.Idea.invertKeySig) (nm := "scratch") (e := .u32) (n := 6)
    (post := Spec.Idea.invertKeyPost Arm.abi.ptrBits) (wa := false) (stack := 0) invertKey_verified
    (by decide) (by decide) (by decide) invertFrameSat_pre

end VG.Proof.Idea.Arm
