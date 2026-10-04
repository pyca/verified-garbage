import VerifiedGarbage.Proof.Poly1305.X86.Update
import VerifiedGarbage.Proof.Poly1305.X86.Finalize
import VerifiedGarbage.Proof.Poly1305.X86.Lit
import VerifiedGarbage.Proof.Poly1305.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/-!
# Streaming Poly1305 on x86, with its working space on the stack

`update` and `finalize` run their code, proved with the working space as an
argument, in a frame that allocates it and copies the arguments passed on
the stack (`Verified.stackScratch`): the return address, the copied
arguments (five slots for `update`, four for `finalize`) and the 128 bytes
of working space. The copies are read only where the postconditions read
the buffers (`Proof/Poly1305/Scratch.lean`).
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86

/-- A state satisfying `vg_poly1305_update`'s precondition, without the
working space. -/
def updateFrameSat : State :=
  { updateSat with rd := [⟨0x2000, 0⟩, ⟨0x4004, 20⟩], wr := [⟨0x1000, 128⟩] }

theorem updateFrameSat_pre : ∃ s, (Spec.Poly1305.updateContract X86.abi 156).pre s := by
  implies_sat [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig, Spec.Poly1305.updatePost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [updateFrameSat, updateSat, updateSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using updateFrameSat

theorem update_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 156 5 Impl.Poly1305.X86.update)
      (Spec.Poly1305.updateContract X86.abi 156) :=
  X86.Verified.stackScratch (sig := Spec.Poly1305.updateSig) (nm := "scratch") (e := .u64)
    (n := 16) (post := Spec.Poly1305.updatePost X86.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 156) update_verified (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (updatePost_local _)
    updateFrameSat_pre

/-- A state satisfying `vg_poly1305_finalize`'s precondition, without the
working space. -/
def finalizeFrameSat : State :=
  { finalizeSat with rd := [⟨0x4004, 16⟩], wr := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩] }

theorem finalizeFrameSat_pre : ∃ s, (Spec.Poly1305.finalizeContract X86.abi 152).pre s := by
  implies_sat [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
    Spec.Poly1305.finalizePost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finalizeFrameSat, finalizeSat, finalizeSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finalizeFrameSat

theorem finalize_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 152 4 Impl.Poly1305.X86.finalize)
      (Spec.Poly1305.finalizeContract X86.abi 152) :=
  X86.Verified.stackScratch (sig := Spec.Poly1305.finalizeSig) (nm := "scratch") (e := .u64)
    (n := 16) (post := Spec.Poly1305.finalizePost X86.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 152) finalize_verified (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (finalizePost_local _)
    finalizeFrameSat_pre

end VG.Proof.Poly1305.X86
