module

import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.MlKem.Ntt
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# ML-KEM on AArch64: the constants of the 32-bit lanes

`vconsts` leaves `q` and `M` in `x9`, `x10` and the lanes of `v16` and `v17`
(`vconsts_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem

/-- `vconsts`: `q` and `M` in `x9`, `x10` and the lanes of `v16`, `v17`. -/
theorem vconsts_ok (s : State) :
    WP isa (.block vconsts) s fun s' => Keep [.x9, .x10] s s' ∧ s'.mem = s.mem ∧ VConsts s' ∧
      ∀ r, r ≠ .v16 → r ≠ .v17 → s'.v r = s.v r := by
  show WP isa (.block ((.movz .x .x9 3329 0 :: movImm .x10 645083) ++
    ([.vop (.dup .s4 .v16 .x9), .vop (.dup .s4 .v17 .x10)] : List Instr))) s _
  refine wp_scalar (by decide) (P := fun s₂ => Keep [.x9, .x10] s s₂ ∧ s₂.mem = s.mem ∧
      (s₂.gpr .x9).toNat = 3329 ∧ (s₂.gpr .x10).toNat = 645083)
    (wp_movz fun s₁ h₁ e₁ => by
      rw [← List.append_nil (movImm _ _)]
      exact wp_movImm fun s₂ h₂ e₂ => wp_nil ⟨(h₁.keep.trans h₂.keep).mono, by rw [h₂.mem, h₁.mem],
        by rw [h₂.get .x9, e₁]; rfl, by rw [e₂]; rfl⟩) fun s₂ ⟨k₂, m₂, e9, e10⟩ hv₂ => ?_
  refine wp_vop (d := .v16) rfl fun s₃ h₃ => wp_vop (d := .v17) rfl fun s₄ h₄ => wp_nil ?_
  refine ⟨(k₂.trans (h₃.keep.trans h₄.keep)).mono, by rw [h₄.mem, h₃.mem, m₂], ⟨?_, ?_⟩,
    fun r h16 h17 => by rw [h₄.get r h17, h₃.get r h16, hv₂]⟩
  · rw [h₄.get .v16, h₃.v]
    exact lanes_dup.congr fun _ _ => by rw [BitVec.toNat_setWidth, e9]
  · rw [h₄.v, h₃.gpr]
    exact lanes_dup.congr fun _ _ => by rw [BitVec.toNat_setWidth, e10]

end VG.Proof.MlKem.AArch64.Ntt
