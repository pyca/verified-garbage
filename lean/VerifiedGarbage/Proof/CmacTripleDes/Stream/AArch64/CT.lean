module

import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Lit
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.AArch64
meta import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Lit
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Impl.CmacTripleDes.Stream.AArch64

/-!
# Streaming TDEA-CMAC on AArch64: constant time

The taint analysis (`Framework/AArch64/Taint.lean`) checks that only the
arguments, which are public, decide branches and addresses, through the code
of `init`, `update` and `finalize` too. Its domain is the registers alone,
so it forgets the registers `update` saves and restores: `absorb` is checked
in three parts (`absorb₁`, `absorb₂`, `absorbPost`), each from the registers
the part before leaves, which `Verified.lean` pins to the public arguments.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.AArch64

open VG VG.AArch64

theorem init_ct : ConstantTime isa initAArch64.pre initAArch64.pub Impl.CmacTripleDes.Stream.AArch64.streamInit := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

theorem finish_ct : ConstantTime isa finishAArch64.pre finishAArch64.pub Impl.CmacTripleDes.Stream.AArch64.finish := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

theorem absorb₁_taint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    Impl.CmacTripleDes.Stream.AArch64.absorb₁ h).isSome = true := ⟨_, by taint_decide⟩

theorem absorb₂_taint : ∃ h, (taint.check (Taint.ofRegs [.x19, .x21, .x22, .x23])
    Impl.CmacTripleDes.Stream.AArch64.absorb₂ h).isSome = true := ⟨_, by taint_decide⟩

theorem absorb₃_taint : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23])
    Impl.CmacTripleDes.Stream.AArch64.absorbPost h).isSome = true := ⟨_, by taint_decide⟩

end VG.Proof.CmacTripleDes.Stream.AArch64
