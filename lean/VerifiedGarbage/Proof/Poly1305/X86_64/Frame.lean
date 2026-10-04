import VerifiedGarbage.Proof.Poly1305.X86_64.UpdateVerified
import VerifiedGarbage.Proof.Poly1305.X86_64.Finalize
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# Streaming Poly1305 on x86-64, with its working space on the stack

`update` and `finalize` run their code, proved with the working space as an
argument, in a frame of 136 bytes that allocates it (`Verified.stackScratch`):
the 128 bytes of working space, and 8 more to keep `rsp` aligned. `update`'s
call of `vg_poly1305_blocks` uses 24 bytes below it, as before.
-/

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64

theorem fill_xdepth : Impl.Poly1305.X86_64.fill.x86_64Depth = 0 := by decide +kernel
theorem rest_xdepth : Impl.Poly1305.X86_64.rest.x86_64Depth = 0 := by decide +kernel

theorem update_xdepth (v : BlocksImpl) :
    (Impl.Poly1305.X86_64.update v.name v.code).x86_64Depth ≤ 24 := by
  have := v.xdepth
  have := v.stack_le
  simp only [Impl.Poly1305.X86_64.update, Impl.Poly1305.X86_64.updatePre,
    Impl.Poly1305.X86_64.updatePost, Code.x86_64Depth, fill_xdepth, rest_xdepth, Nat.max_le]
  omega

/-- A state satisfying `vg_poly1305_update`'s precondition, without the
working space. -/
def updateFrameSat : State := { updateSat with wr := [⟨0x1000, 128⟩] }

theorem updateFrameSat_pre : ∃ s, (Spec.Poly1305.updateContract X86_64.abi 160).pre s := by
  implies_sat [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig, Spec.Poly1305.updatePost,
    X86_64.abi, X86_64.argRegs] [updateFrameSat, updateSat] using updateFrameSat

theorem update_framed (v : BlocksImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 136 .r8 (Impl.Poly1305.X86_64.update v.name v.code))
      (Spec.Poly1305.updateContract X86_64.abi 160) :=
  X86_64.Verified.stackScratch (sig := Spec.Poly1305.updateSig) (nm := "scratch") (e := .u64)
    (n := 16) (post := Spec.Poly1305.updatePost X86_64.abi.ptrBits) (wa := false) (stack := 24)
    (bytes := 136) (update_verified v) (by decide) (by decide) (by decide) (update_spSafe v)
    (update_xdepth v) updateFrameSat_pre

/-- A state satisfying `vg_poly1305_finalize`'s precondition, without the
working space. -/
def finalizeFrameSat : State := { finalizeSat with wr := [⟨0x1000, 128⟩, ⟨0x3000, 16⟩] }

theorem finalizeFrameSat_pre : ∃ s, (Spec.Poly1305.finalizeContract X86_64.abi 136).pre s := by
  implies_sat [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
    Spec.Poly1305.finalizePost, X86_64.abi, X86_64.argRegs] [finalizeFrameSat, finalizeSat]
    using finalizeFrameSat

theorem finalize_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 136 .rcx Impl.Poly1305.X86_64.finalize)
      (Spec.Poly1305.finalizeContract X86_64.abi 136) :=
  X86_64.Verified.stackScratch (sig := Spec.Poly1305.finalizeSig) (nm := "scratch") (e := .u64)
    (n := 16) (post := Spec.Poly1305.finalizePost X86_64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 136) finalize_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) finalizeFrameSat_pre

end VG.Proof.Poly1305.X86_64
