module

import VerifiedGarbage.Proof.Mont.X86.Rt.Row
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

/-! # Propagating the carry changes only its two product words -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem carryWords_frame {s : State} {W : Addr} {L : Nat} (hw : Ws s W L) {y : Nat}
    (hp : PtrAt s W .ebp y) (hy : y + 8 ≤ L)
    :
    WP isa (.block carryWords) s fun u =>
      Outside W y 8 s.mem u.mem ∧
      Keeps [.eax] s u := by
  have hn := hw.nowrap
  simp only [carryWords]
  refine wp_movS (readSrc_ptr hw hp (d := 0) (by omega)) fun s₁ u₁ _ => ?_
  refine wp_addS rfl fun s₂ u₂ c₂ => ?_
  have k₂ : Keeps [.eax] s s₂ := (u₁.keeps.trans u₂.keeps)
  have hw₂ := hw.of_keeps k₂
  have hp₂ : PtrAt s₂ W .ebp y := by rw [PtrAt, k₂.1 _ (by decide)]; exact hp
  refine wp_storeS (ea_ptr hw₂ hp₂ (d := 0) (by omega)) (ws_write hw₂ (y := y + 0) (n := 4) (by omega))
    fun s₃ m₃ => ?_
  have k₃ : Keeps [.eax] s s₃ := k₂.widen (m₃.keeps [])
  have hw₃ := hw.of_keeps k₃
  have hp₃ : PtrAt s₃ W .ebp y := by rw [PtrAt, k₃.1 _ (by decide)]; exact hp
  refine wp_movS (readSrc_ptr hw₃ hp₃ (d := 4) (by omega)) fun s₄ u₄ cf₄ => ?_
  refine wp_adcS rfl (by rw [cf₄, m₃.cf]; exact c₂) fun s₅ u₅ _ => ?_
  have k₅ : Keeps [.eax] s s₅ := (k₃.trans u₄.keeps).trans u₅.keeps
  have hw₅ := hw.of_keeps k₅
  have hp₅ : PtrAt s₅ W .ebp y := by rw [PtrAt, k₅.1 _ (by decide)]; exact hp
  refine wp_storeS (ea_ptr hw₅ hp₅ (d := 4) (by omega)) (ws_write hw₅ (y := y + 4) (n := 4) (by omega))
    fun s₆ m₆ => WP.block_nil ?_
  rw [Nat.add_zero] at m₃
  have hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have hm₅ : s₅.mem = s₃.mem := by rw [u₅.mem, u₄.mem]
  rw [hm₂] at m₃
  rw [hm₅, m₃.mem] at m₆
  have W₀ := writeW32_outside s.mem W (d := y) (s₂.gpr .eax) (by omega)
  have W₁ := writeW32_outside (s.mem.writeW (off W y) (s₂.gpr .eax)) W (d := y + 4) (s₅.gpr .eax) (by omega)
  rw [← m₆.mem] at W₁
  exact ⟨(W₀.mono (Nat.le_refl _) (by omega)).trans (W₁.mono (by omega) (by omega)),
    k₅.widen (m₆.keeps [])⟩

end VG.Proof.Mont.X86.Compact
