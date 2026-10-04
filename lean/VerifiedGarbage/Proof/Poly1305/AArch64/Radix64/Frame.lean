import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Update
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Finalize
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/-!
# Streaming Poly1305 on AArch64, with its working space on the stack

`update` and `finalize` run their code, proved with the working space as an
argument, in a frame of 128 bytes that allocates it
(`Verified.stackScratch`).
-/

namespace VG.Proof.Poly1305.AArch64.Radix64

open VG VG.AArch64

/-- A state satisfying `vg_poly1305_update`'s precondition, without the
working space. -/
def updateFrameSat : State := { updateSat with wr := [⟨0x1000, 128⟩] }

theorem updateFrameSat_pre : ∃ s, (Spec.Poly1305.updateContract AArch64.abi 128).pre s := by
  implies_sat [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig, Spec.Poly1305.updatePost,
    AArch64.abi, AArch64.argRegs] [updateFrameSat, updateSat] using updateFrameSat

theorem update_framed :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 128 .x4 Impl.Poly1305.AArch64.Radix64.update)
      (Spec.Poly1305.updateContract AArch64.abi 128) :=
  AArch64.Verified.stackScratch (sig := Spec.Poly1305.updateSig) (nm := "scratch") (e := .u64)
    (n := 16) (post := Spec.Poly1305.updatePost AArch64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 128) update_verified (by decide) (by decide) updateFrameSat_pre

/-- A state satisfying `vg_poly1305_finalize`'s precondition, without the
working space. -/
def finalizeFrameSat : State := { finalizeSat with wr := [⟨0x1000, 128⟩, ⟨0x3000, 16⟩] }

theorem finalizeFrameSat_pre : ∃ s, (Spec.Poly1305.finalizeContract AArch64.abi 128).pre s := by
  implies_sat [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
    Spec.Poly1305.finalizePost, AArch64.abi, AArch64.argRegs] [finalizeFrameSat, finalizeSat]
    using finalizeFrameSat

theorem finalize_framed :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 128 .x3 Impl.Poly1305.AArch64.Radix64.finalize)
      (Spec.Poly1305.finalizeContract AArch64.abi 128) :=
  AArch64.Verified.stackScratch (sig := Spec.Poly1305.finalizeSig) (nm := "scratch") (e := .u64)
    (n := 16) (post := Spec.Poly1305.finalizePost AArch64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 128) finalize_verified (by decide) (by decide) finalizeFrameSat_pre

end VG.Proof.Poly1305.AArch64.Radix64
