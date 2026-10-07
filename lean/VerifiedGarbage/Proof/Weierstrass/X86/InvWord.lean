import VerifiedGarbage.Proof.Weierstrass.X86.InvMasks

/-! # One complete word divstep on x86 -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

def atWord (m : Mem) (base : Addr) (t i : Nat) : BitVec 32 :=
  m.readW (off base (t + 4 * i)) 32

def wordState (m : Mem) (base : Addr) (t : Nat) : Divstep.W32.WSt :=
  ⟨atWord m base t 0, atWord m base t 1, atWord m base t 2,
   atWord m base t 3, atWord m base t 4, atWord m base t 5, atWord m base t 6⟩

theorem pair_away {base : Addr} {t left right j : Nat} {m m' : Mem}
    (U : Unch base [(t + 4 * left, 4), (t + 4 * right, 4)] m m')
    (h : t + 28 ≤ 2 ^ 64) (hj : j < 7) (hl : j ≠ left) (hr : j ≠ right) :
    atWord m' base t j = atWord m base t j := by
  apply Mem.readW_congr
  intro i hi
  apply U
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rw [ofs_off base (by omega)]
  rcases hw with rfl | rfl <;> omega

theorem mask_away {base : Addr} {t j : Nat} {m m' : Mem}
    (U : Outside base t 4 m m') (h : t + 28 ≤ 2 ^ 64) (hj : j < 7) (h0 : 1 ≤ j) :
    atWord m' base t j = atWord m base t j := by
  apply BitVec.eq_of_toNat_eq
  exact U.w32 (by omega) (by omega)

theorem wordStep_ok {s : State} {base : Addr} {size t : Nat} (hs : Scr s base size)
    (ht : t + 28 ≤ size) :
    WP isa (.block (wordStep t)) s fun u =>
      wordState u.mem base t = Divstep.W32.wstep (wordState s.mem base t) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u ∧ Outside base t 28 s.mem u.mem := by
  have hn := hs.nowrap
  have ht' : t + 28 ≤ 2 ^ 64 := by omega
  unfold wordStep
  refine WP.block_append (WP.block_append (WP.block_append
    (WP.mono (masks_ok hs (by omega)) fun s₁ ⟨C₁, D₁, V₁, K₁, O₁⟩ => ?_)))
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (pair_ok hs₁ (left := t + 4) (right := t + 8)
    (by omega) (by omega) (by omega) false) fun s₂ ⟨F₂, G₂, K₂, U₂⟩ => ?_
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (pair_ok hs₂ (left := t + 12) (right := t + 20)
    (by omega) (by omega) (by omega) true) fun s₃ ⟨U₃, Q₃, K₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  refine WP.mono (pair_ok hs₃ (left := t + 16) (right := t + 24)
    (by omega) (by omega) (by omega) true) fun u ⟨V₄, R₄, K₄, O₄⟩ => ?_
  have E₁ (j : Nat) (hj : j < 7) (h0 : 1 ≤ j) := mask_away O₁ ht' hj h0
  have E₂ (j : Nat) (hj : j < 7) (hl : j ≠ 1) (hr : j ≠ 2) := pair_away U₂ ht' hj hl hr
  have E₃ (j : Nat) (hj : j < 7) (hl : j ≠ 3) (hr : j ≠ 5) := pair_away O₃ ht' hj hl hr
  have E₄ (j : Nat) (hj : j < 7) (hl : j ≠ 4) (hr : j ≠ 6) := pair_away O₄ ht' hj hl hr
  have C₂ : s₂.gpr .ecx = s₁.gpr .ecx := K₂.1 _ (by decide)
  have D₂ : s₂.gpr .edx = s₁.gpr .edx := K₂.1 _ (by decide)
  have C₃ : s₃.gpr .ecx = s₁.gpr .ecx := (K₂.trans K₃).1 _ (by decide)
  have D₃ : s₃.gpr .edx = s₁.gpr .edx := (K₂.trans K₃).1 _ (by decide)
  have E₁' : ∀ j, j < 7 → 1 ≤ j →
      s₁.mem.readW (off base (t + 4 * j)) 32 = s.mem.readW (off base (t + 4 * j)) 32 := E₁
  have EU : s₂.mem.readW (off base (t + 12)) 32 = s.mem.readW (off base (t + 12)) 32 :=
    (E₂ 3 (by decide) (by decide) (by decide)).trans (E₁ 3 (by decide) (by decide))
  have EQ : s₂.mem.readW (off base (t + 20)) 32 = s.mem.readW (off base (t + 20)) 32 :=
    (E₂ 5 (by decide) (by decide) (by decide)).trans (E₁ 5 (by decide) (by decide))
  have EV : s₃.mem.readW (off base (t + 16)) 32 = s.mem.readW (off base (t + 16)) 32 :=
    (E₃ 4 (by decide) (by decide) (by decide)).trans
      ((E₂ 4 (by decide) (by decide) (by decide)).trans (E₁ 4 (by decide) (by decide)))
  have ER : s₃.mem.readW (off base (t + 24)) 32 = s.mem.readW (off base (t + 24)) 32 :=
    (E₃ 6 (by decide) (by decide) (by decide)).trans
      ((E₂ 6 (by decide) (by decide) (by decide)).trans (E₁ 6 (by decide) (by decide)))
  simp only [Bool.false_eq_true, ite_false, ite_true] at F₂ G₂ U₃ Q₃ V₄ R₄
  rw [E₁' 1 (by decide) (by decide), E₁' 2 (by decide) (by decide), C₁, D₁] at F₂ G₂
  rw [EU, EQ, C₂, D₂, C₁, D₁] at U₃ Q₃
  rw [EV, ER, C₃, D₃, C₁, D₁] at V₄ R₄
  refine ⟨?_, (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans
    (K₃.mono (by decide))).trans (K₄.mono (by decide)), ?_⟩
  · simp only [wordState, Divstep.W32.wstep, Divstep.W32.WSt.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change atWord u.mem base t 0 = _
      rw [E₄ 0 (by decide) (by decide) (by decide), E₃ 0 (by decide) (by decide) (by decide),
        E₂ 0 (by decide) (by decide) (by decide)]
      exact V₁
    · change atWord u.mem base t 1 = _
      rw [E₄ 1 (by decide) (by decide) (by decide), E₃ 1 (by decide) (by decide) (by decide)]
      exact F₂
    · change atWord u.mem base t 2 = _
      rw [E₄ 2 (by decide) (by decide) (by decide), E₃ 2 (by decide) (by decide) (by decide)]
      exact G₂
    · change atWord u.mem base t 3 = _
      rw [E₄ 3 (by decide) (by decide) (by decide)]
      simpa only [Divstep.W32.wstep, wordState, atWord, pairRight, oddMask, swapMask,
        Divstep.W32.shl1, Nat.reduceMul, Nat.add_zero] using U₃
    · simpa only [Divstep.W32.wstep, wordState, atWord, pairRight, oddMask, swapMask,
        Divstep.W32.shl1, Nat.reduceMul, Nat.add_zero] using V₄
    · change atWord u.mem base t 5 = _
      rw [E₄ 5 (by decide) (by decide) (by decide)]
      exact Q₃
    · exact R₄
  · intro x hx
    have h (j : Nat) (hj : j < 7) : ofs base x < t + 4 * j ∨ t + 4 * j + 4 ≤ ofs base x := by omega
    rw [O₄ x (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
                 rcases hw with rfl | rfl <;> first | exact h 4 (by decide) | exact h 6 (by decide)),
      O₃ x (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
               rcases hw with rfl | rfl <;> first | exact h 3 (by decide) | exact h 5 (by decide)),
      U₂ x (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
               rcases hw with rfl | rfl <;> first | exact h 1 (by decide) | exact h 2 (by decide)),
      O₁ x (by omega)]

end VG.Proof.Weierstrass.X86.Inv
