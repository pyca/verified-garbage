import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Stages

/-! # Preserving scratch constants while writing encrypted data -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)

theorem data_read {s₀ : State} {m m' : Mem} (hp : SPre s₀)
    (h : Frame [dR s₀] m m') (d n : Nat) (hn : d + n ≤ 1024) :
    m'.readW (pp s₀ + BitVec.ofNat 64 d) (8 * n) =
      m.readW (pp s₀ + BitVec.ofNat 64 d) (8 * n) := by
  apply h.readW (r := pR s₀)
  · exact Offset.contains_base _ (by omega) (by omega)
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hp.d_p.symm
  · omega

theorem Env.writeData {s₀ s t : State} {P : Nat → Block} (hp : SPre s₀)
    (h : Env s₀ P s) (hg : t.gpr = s.gpr) (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (hm : Frame [dR s₀] s.mem t.mem) : Env s₀ P t := by
  constructor
  · rw [hg]; exact h.rdi
  · rw [hg]; exact h.rsi
  · rw [hg]; exact h.rcx
  · rw [hg]; exact h.r11
  · rw [hg]; exact h.r10
  · intro r h1 h2 h3 h4 h5 h6; rw [hg]; exact h.other r h1 h2 h3 h4 h5 h6
  · exact h.frame.trans (hm.mono (by simp))
  · intro k hk
    exact (data_read hp hm (128 + 16 * k) 16 (by omega)).trans (h.powers k hk)
  · exact (data_read hp hm 768 16 (by decide)).trans h.mask
  · exact (data_read hp hm 784 16 (by decide)).trans h.poly
  · exact (data_read hp hm 800 8 (by decide)).trans h.rounds
  · exact (data_read hp hm 808 8 (by decide)).trans h.data
  · exact hr.trans h.rd
  · exact hw.trans h.wr

/-- Changing loop counters and cursors does not change the environment. -/
theorem Env.move {s₀ s t : State} {P : Nat → Block} (h : Env s₀ P s)
    (hg : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → t.gpr r = s.gpr r)
    (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) : Env s₀ P t := by
  constructor
  · rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.rdi
  · rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.rsi
  · rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.rcx
  · rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.r11
  · rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.r10
  · intro r h1 h2 h3 h4 h5 h6; rw [hg r h1 h2 h3 h4]; exact h.other r h1 h2 h3 h4 h5 h6
  · rw [hm]; exact h.frame
  · rw [hm]; exact h.powers
  · rw [hm]; exact h.mask
  · rw [hm]; exact h.poly
  · rw [hm]; exact h.rounds
  · rw [hm]; exact h.data
  · exact hr.trans h.rd
  · exact hw.trans h.wr

end VG.Proof.Gcm.X86_64.StitchAvx8
