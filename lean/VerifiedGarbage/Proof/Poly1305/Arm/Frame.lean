import VerifiedGarbage.Proof.Poly1305.Arm.Update
import VerifiedGarbage.Proof.Poly1305.Arm.Finalize
import VerifiedGarbage.Proof.Poly1305.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# Streaming Poly1305 on ARMv7, with its working space on the stack

`update` and `finalize` run their code, proved with the working space as an
argument, in a frame of 144 bytes that allocates it
(`Verified.stackScratch`): the copies of the arguments passed on the stack
(`update`'s `data` and `len`, `finalize`'s `out`), the buffer's address, the
saved `lr` and the 128 bytes of working space. The copies are read only
where the postconditions read the buffers (`Proof/Poly1305/Scratch.lean`).
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm

/-- A state satisfying `vg_poly1305_update`'s precondition, without the
working space. -/
def updateFrameSat : State :=
  { Update.updateSat with rd := [⟨0, 0⟩, ⟨0x4000, 8⟩], wr := [⟨0x1000, 128⟩] }

theorem updateFrameSat_pre : ∃ s, (Spec.Poly1305.updateContract Arm.abi 144).pre s := by
  implies_sat [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig, Spec.Poly1305.updatePost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [updateFrameSat, Update.updateSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using updateFrameSat

theorem update_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 144 2 Impl.Poly1305.Arm.update)
      (Spec.Poly1305.updateContract Arm.abi 144) :=
  Arm.Verified.stackScratch (sig := Spec.Poly1305.updateSig) (nm := "scratch") (e := .u64)
    (n := 16) (post := Spec.Poly1305.updatePost Arm.abi.ptrBits) (wa := false) (stack := 0)
    (m := 2) Update.update_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (updatePost_local _)
    updateFrameSat_pre

/-- A state satisfying `vg_poly1305_finalize`'s precondition, without the
working space. -/
def finalizeFrameSat : State :=
  { Fin.finalizeSat with rd := [⟨0x5000, 4⟩], wr := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩] }

theorem finalizeFrameSat_pre : ∃ s, (Spec.Poly1305.finalizeContract Arm.abi 144).pre s := by
  implies_sat [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
    Spec.Poly1305.finalizePost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr]
    [finalizeFrameSat, Fin.finalizeSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finalizeFrameSat

theorem finalize_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 144 1 Impl.Poly1305.Arm.finalize)
      (Spec.Poly1305.finalizeContract Arm.abi 144) :=
  Arm.Verified.stackScratch (sig := Spec.Poly1305.finalizeSig) (nm := "scratch") (e := .u64)
    (n := 16) (post := Spec.Poly1305.finalizePost Arm.abi.ptrBits) (wa := false) (stack := 0)
    (m := 1) Fin.finalize_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (finalizePost_local _)
    finalizeFrameSat_pre

end VG.Proof.Poly1305.Arm
