import VerifiedGarbage.Proof.Weierstrass.X86.TCombScan

/-! # The comb's selected point at infinity -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont

/-- `ecx` is all ones precisely when the magnitude is zero. -/
theorem isZero_ok (s : State) {a : Nat} (ha : a < 2 ^ 32) (hb : s.gpr .ebx = BitVec.ofNat 32 a) :
    WP isa (.block [.mov .ecx (.reg .ebx), .alu .cmp .ecx (.imm 1), .alu .sbb .ecx (.reg .ecx)]) s
      fun t => t.gpr .ecx = bmask (decide (a = 0)) ∧ CKeeps [.ecx] s t := by
  crun [hb]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h1 : (1 : BitVec 32).toNat = 1 := rfl
    have hx : decide ((BitVec.ofNat 32 a).toNat < 1) = decide (a = 0) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]; exact decide_eq_decide.mpr (by omega)
    rw [BitVec.sub_self, h1, hx]
    cases decide (a = 0) <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- Word selection, viewed as the shared 64-bit-word number. -/
theorem selWords_ok {s : State} {base : Addr} {size n o a b : Nat} (hs : Scr s base size) (c : Bool)
    (hc : s.gpr .ecx = bmask c) (ho : o + 8 * n ≤ size) (ha : a + 8 * n ≤ size)
    (hb : b + 8 * n ≤ size) (hoa : o ≤ a ∨ a + 8 * n ≤ o) (hob : o ≤ b ∨ b + 8 * n ≤ o) :
    WP isa (.block (sel (2 * n) o a b)) s fun t =>
      wordsVal t.mem base o n = (if c then wordsVal s.mem base b n else wordsVal s.mem base a n) ∧
      Keeps [.eax, .edx] s t ∧ Outside base o (8 * n) s.mem t.mem := by
  refine WP.mono (sel_ok c (2 * n) hs hc (by omega) (by omega) (by omega) (by omega) (by omega))
    fun t ⟨v, k, O⟩ => ⟨?_, k, ?_⟩
  · simpa only [wordsVal_eq_val32] using v
  · simpa only [show 4 * (2 * n) = 8 * n by omega] using O

/-- The neutral point's y coordinate is one and z is zero. All other
magnitudes keep the selected y and receive z = one. -/
theorem selOne_ok (K : TCombCfg) {s : State} {base : Addr} {size a : Nat} (hs : Scr s base size)
    (ha : a < 2 ^ 32) (hb : s.gpr .ebx = BitVec.ofNat 32 a)
    (hy : K.E.y + 8 * K.M.n ≤ size) (hz : K.E.z + 8 * K.M.n ≤ size)
    (hzero : K.zero + 8 * K.M.n ≤ size)
    (hyz : K.E.y + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.y)
    (h0y : K.zero + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ K.zero)
    (h0z : K.zero + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.zero)
    (hone : K.one < 2 ^ (64 * K.M.n)) (h0 : wordsVal s.mem base K.zero K.M.n = 0) :
    WP isa (.block K.selOne) s fun t =>
      wordsVal t.mem base K.E.y K.M.n = (if a = 0 then K.one else wordsVal s.mem base K.E.y K.M.n) ∧
      wordsVal t.mem base K.E.z K.M.n = (if a = 0 then 0 else K.one) ∧
      Keeps [.eax, .ecx, .edx] s t ∧
      Unch base [(K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem t.mem := by
  have hn := hs.nowrap
  rw [TCombCfg.selOne, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setConst_ok hs hz hone) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (isZero_ok s₁ ha (by rw [k₁.1 _ (by decide), hb])) fun s₂ ⟨c₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂.keeps (by decide)
  refine WP.mono (selWords_ok hs₂ (decide (a = 0)) c₂ hy hy hz (.inl (Nat.le_refl _)) (by omega))
    fun s₃ ⟨v₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (selWords_ok hs₃ (decide (a = 0)) (by rw [k₃.1 _ (by decide), c₂]) hz hz hzero
    (.inl (Nat.le_refl _)) (by omega)) fun t ⟨v₄, k₄, O₄⟩ => ?_
  have y₂ : wordsVal s₂.mem base K.E.y K.M.n = wordsVal s.mem base K.E.y K.M.n := by
    rw [k₂.2.1, O₁.wordsVal hyz (by omega)]
  have z₂ : wordsVal s₂.mem base K.E.z K.M.n = K.one := by rw [k₂.2.1, v₁]
  have z₃ : wordsVal s₃.mem base K.E.z K.M.n = K.one := by
    rw [O₃.wordsVal hyz.symm (by omega), z₂]
  have zero₃ : wordsVal s₃.mem base K.zero K.M.n = 0 := by
    rw [O₃.wordsVal h0y (by omega), k₂.2.1, O₁.wordsVal h0z (by omega), h0]
  refine ⟨?_, ?_, ((k₁.mono (by decide)).trans (k₂.keeps.mono (by decide))).trans
      ((k₃.mono (by decide)).trans (k₄.mono (by decide))), ?_⟩
  · rw [O₄.wordsVal hyz (by omega), v₃, y₂, z₂]; simp
  · rw [v₄, zero₃, z₃]; simp
  · have U₁ := O₁.unch
    have U₃ := O₃.unch
    have U₄ := O₄.unch
    rw [k₂.2.1] at U₃
    exact ((U₁.trans U₃).trans U₄).mono fun w hw => by
      simp only [List.mem_append, List.mem_singleton] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hw with (rfl | rfl) | rfl <;> simp

end VG.Proof.Weierstrass.X86
