module

public import VerifiedGarbage.Proof.MlKem.X86_64.S4Parse
public import VerifiedGarbage.Proof.MlKem.X86_64.S4SqT
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, the table

After the squeezes, the code writes the table of the sampling and the
constants of the vector code above the counts of the seeds, quadword by
quadword (`tab_ok`), apart from the states and the output of the squeezes,
which it keeps (`tabT_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.S4

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.Sha3.X86_64 (wp_movi64 wp_store wp_nil)

/-- During the writes of the table, from `s₀`. -/
structure TabInvW (w16 : Bool) (σ s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep [.rax] s₀ s
  frame : Frame [tabR σ] s₀.mem s.mem
  tab : ∀ i < n, s.mem.readW (at' σ (oTab + 8 * i)) 64 = tabQ i

/-- `TabInvW` with 32-bit coefficients. -/
abbrev TabInv := TabInvW false

theorem tab_step {σ : State} (hp : PreW w16 σ) {s₀ : State} (he : EnvW w16 σ s₀) {i : Nat} (hi : i < 280) {s : State}
    (h : TabInvW w16 σ s₀ i s) :
    WP isa (.block [.movImm64 .rax (tabQ i), .store (at_ .rbx (oTab + 8 * i)) .rax]) s (TabInvW w16 σ s₀ (i + 1)) := by
  have hbx : s.gpr .rbx = scr σ := by rw [h.keep.gpr (by decide), he.rbx]
  refine wp_movi64 fun s₁ u₁ => wp_store (a := at' σ (oTab + 8 * i)) (by rw [ea_at, u₁.other _ (by decide), hbx])
    (by rw [u₁.wr, h.keep.2.2, he.wr]; exact in_scr hp rfl (by simp only [oTab]; omega)) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (at' σ (oTab + 8 * i)) (tabQ i) := by rw [m₂, u₁.mem, u₁.gpr]
  refine ⟨⟨fun g hg => by rw [g₂, u₁.other g (by simpa using hg), h.keep.gpr hg], by rw [r₂, u₁.rd, h.keep.2.1],
    by rw [w₂, u₁.wr, h.keep.2.2]⟩, ?_, fun i' hi' => ?_⟩
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by simp only [oTab]; omega)
      (by simp only [oTab]; omega))
  · rw [hm]
    by_cases e : i' = i
    · subst e; exact Mem.readW_writeW_self64 _ _ _
    · rw [rd64_off (by simp only [oTab]; omega) (by simp only [oTab]; omega) (by omega)]
      exact h.tab i' (by omega)

theorem tabBuild_eq : tabBuild = (List.range 280).flatMap fun i =>
    [.movImm64 .rax (tabQ i), .store (at_ .rbx (oTab + 8 * i)) .rax] := rfl

/-- The table and the constants. -/
theorem tab_ok {σ : State} (hp : PreW w16 σ) {s₀ : State} (he : EnvW w16 σ s₀) :
    WP isa (.block tabBuild) s₀ (TabInvW w16 σ s₀ 280) := by
  rw [tabBuild_eq]
  exact wp_range_flatMap (M := isa) (TabInvW w16 σ s₀) (fun i s hi h => tab_step hp he hi h) 280 (Nat.le_refl _) s₀
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (by omega)⟩

/-- The table, after the squeezes, which it keeps. -/
theorem tabT_ok {σ : State} (hp : PreW w16 σ) {s : State} (h : SqTW w16 σ 0 3 s) :
    WP isa (.block tabBuild) s fun s' => SqTW w16 σ 0 3 s' ∧ TabOK σ s'.mem := by
  refine WP.mono (tab_ok hp h.env) fun s' h' => ⟨h.apart (by decide) h'.frame (fun r hr => ?_) (fun r hr => ?_)
    (fun r hr => ?_) h'.keep.2.1 h'.keep.2.2 fun r hr => h'.keep.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    h'.tab⟩ <;> simp only [List.mem_singleton] at hr <;> subst hr
  · exact Offset.base_disjoint _ (by simp only [oSave, oTab]; omega) (by simp only [oTab]; omega)
  · exact Offset.disjoint _ (.inl (by simp only [oSave, oTab]; omega)) (by simp only [oSave]; omega)
      (by simp only [oTab]; omega)
  · exact ⟨scrR σ, by simp, sub_scr (by simp only [oTab]; omega)⟩

end VG.Proof.MlKem.X86_64.S4
