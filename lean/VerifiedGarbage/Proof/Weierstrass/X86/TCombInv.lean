import VerifiedGarbage.Proof.Weierstrass.X86.TCombEntry

/-! # State and memory invariants for the x86 comb -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont
open Spec.Weierstrass

structure TCombFixed (K : TCombCfg) (C : Curve) (base : Addr) (size : Nat) (s₀ : State) (k : Nat)
    (T : Addr) (ws : List (BitVec 64)) : Prop where
  a : tmv C K.M.n base s₀ K.S.a = Fin.ofNat C.p C.a
  b : tmv C K.M.n base s₀ K.S.b3 = Fin.ofNat C.p C.b
  ro_lt : ∀ x ∈ combRo K.toComb, wordsVal s₀.mem base x K.M.n < C.p
  zero : wordsVal s₀.mem base K.zero K.M.n = 0
  bits : ∀ t < K.kbytes, s₀.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0
  k_lt : k < 2 ^ K.kbytes
  tsym : (s₀.mem.readW (off base K.ptr) 32).setWidth 64 = T
  tbl : TblMem s₀ T ws
  out : ∀ i < ws.length, ∀ b < 8, size ≤ ofs base (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)

/-- The loop's invariant at `esi = j`: `A` represents `[combEW w k J j]G`, and
the table of bits (all `w J` bytes) and the tables are where the digits and
the selection read them. -/
structure TCombInv (K : TCombCfg) (C : Curve) (base : Addr) (size k : Nat) (T : Addr)
    (ws : List (BitVec 64)) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  esi : s.gpr .esi = BitVec.ofNat 32 j
  keep : KeepRegs powClob s₀ s
  unch : Unch base (tcombW K) s₀.mem s.mem
  mod : ModOkW K.M size C.p s.mem base
  lt : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y) (tmv C K.M.n base s K.A.z)
    (mul (combEW K.w k K.J j) (G C))
  bits : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0
  tbl : TblMem s T ws
  tsym : (s.mem.readW (off base K.ptr) 32).setWidth 64 = T

/-- What the comb writes is in the working space. -/
theorem tcombW_size {K : TCombCfg} {C : Curve} {size : Nat} {mem : Mem} {base : Addr}
    (hL : TCombLay K size) (hM : ModOkW K.M size C.p mem base) : ∀ w ∈ tcombW K, w.1 + w.2 ≤ size := by
  intro w hw
  simp only [tcombW, combWx, combW, List.mem_append, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at hw
  rcases hw with ((⟨y, hy, rfl⟩ | rfl) | rfl) | rfl
  · exact hL.comb.lay.le y (combWs_slots _ y hy)
  · exact hM.tmp
  · exact hL.wk.le
  · exact hL.bits

theorem tcombW_mo {K : TCombCfg} {size m : Nat} {mem : Mem} {base : Addr} (hL : TCombLay K size)
    (hM : ModOkW K.M size m mem base) : ∀ w ∈ tcombW K, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
  intro w hw
  simp only [tcombW, combWx, combW, List.mem_append, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at hw
  rcases hw with ((⟨y, hy, rfl⟩ | rfl) | rfl) | rfl
  · have := hL.comb.lay.mo y (combWs_slots _ y hy); dsimp only [TCombCfg.toComb] at this ⊢; omega
  · have := hM.sep; dsimp only [TCombCfg.toComb] at this ⊢; omega
  · exact .inl hL.wk.mo
  · have := hL.bits_sl K.M.mo (List.mem_cons_self ..); dsimp only; omega

theorem tcombW_ro {K : TCombCfg} {size : Nat} (hL : TCombLay K size) {x : Nat}
    (hx : x ∈ combRo K.toComb) : ∀ w ∈ tcombW K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  have hxs := combRo_slots x hx
  simp only [tcombW, combWx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with (hw | rfl) | rfl
  · exact combW_ro hL.comb hx w hw
  · exact .inl (hL.wk.sl x hxs)
  · have := hL.bits_sl x (List.mem_cons_of_mem _ hxs); dsimp only; omega

theorem combW_bits {K : TCombCfg} {size : Nat} (hL : TCombLay K size) {t : Nat} (ht : t < K.w * K.J) :
    ∀ w ∈ combWx K, K.bits + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ K.bits + t := by
  have : K.w * K.J ≤ K.kbytes + 4 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · have := hL.bits_w w hw; omega
  · simp only [List.mem_singleton] at hw; subst hw
    have := hL.wk_bits; exact .inl (by omega)

theorem combW_ptr {K : TCombCfg} {size : Nat} (hL : TCombLay K size) :
    ∀ w ∈ combWx K, K.ptr + 4 ≤ w.1 ∨ w.1 + w.2 ≤ K.ptr := by
  intro w hw
  simp only [combWx, combW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with (⟨x, hx, rfl⟩ | rfl) | rfl
  · exact hL.ptr_sl x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (combWs_slots _ x hx)))
  · exact hL.ptr_sl K.M.tmp (by simp)
  · exact .inl hL.ptr_wk

theorem unch_read32 {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    {d : Nat} (hd : d + 4 ≤ 2 ^ 64) (hW : ∀ w ∈ W, d + 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 := by
  apply Mem.readW_congr
  intro i hi
  rw [off, Offset.add_add]
  exact h.byte (fun w hw => by have := hW w hw; omega) (by omega)

theorem copyWords_ok {s : State} {base : Addr} {size n o a : Nat} (hs : Scr s base size)
    (ho : o + 8 * n ≤ size) (ha : a + 8 * n ≤ size) (hsep : o ≤ a ∨ a + 8 * n ≤ o) :
    WP isa (.block (copy (2 * n) o a)) s fun t =>
      wordsVal t.mem base o n = wordsVal s.mem base a n ∧ Keeps [.eax] s t ∧
      Outside base o (8 * n) s.mem t.mem := by
  refine WP.mono (copy_ok (2 * n) hs (by omega) (by omega) (by omega)) fun t ⟨v, k, O⟩ =>
    ⟨by simpa only [wordsVal_eq_val32] using v, k, by simpa only [show 4 * (2 * n) = 8 * n by omega] using O⟩

/-- `o = a`, a point, for `o`'s slots apart from each other and from `a`'s. -/
theorem copyPt_ok {s : State} {base : Addr} {size n : Nat} (hs : Scr s base size) {o a : Pt}
    (hle : ∀ x ∈ [o.x, o.y, o.z, a.x, a.y, a.z], x + 8 * n ≤ size)
    (hap : ∀ x ∈ [o.x, o.y, o.z], ∀ y ∈ [o.x, o.y, o.z, a.x, a.y, a.z], x ≠ y →
      x + 8 * n ≤ y ∨ y + 8 * n ≤ x)
    (hne : ∀ x ∈ [o.x, o.y, o.z], x ∉ [a.x, a.y, a.z]) (ho : o.x ≠ o.y ∧ o.x ≠ o.z ∧ o.y ≠ o.z) :
    WP isa (.block (copyPt n o a)) s fun t =>
      wordsVal t.mem base o.x n = wordsVal s.mem base a.x n ∧
      wordsVal t.mem base o.y n = wordsVal s.mem base a.y n ∧
      wordsVal t.mem base o.z n = wordsVal s.mem base a.z n ∧
      KeepRegs [.eax] s t ∧ Unch base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem t.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, not_or] at hle hap hne
  obtain ⟨⟨xa, xb, xc⟩, ⟨ya, yb, yc⟩, ⟨za, zb, zc⟩⟩ := hne
  have pxy := hap.1.2.1 ho.1
  have pxz := hap.1.2.2.1 ho.2.1
  have pyz := hap.2.1.2.2.1 ho.2.2
  have pxa := hap.1.2.2.2.1 xa
  have pxb := hap.1.2.2.2.2.1 xb
  have pxc := hap.1.2.2.2.2.2 xc
  have pyb := hap.2.1.2.2.2.2.1 yb
  have pyc := hap.2.1.2.2.2.2.2 yc
  have pzc := hap.2.2.2.2.2.2.2 zc
  rw [copyPt, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyWords_ok hs (o := o.x) (a := a.x) hle.1 hle.2.2.2.1 (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.mono (copyWords_ok hs₁ (o := o.y) (a := a.y) hle.2.1 hle.2.2.2.2.1 (by omega)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (copyWords_ok hs₂ (o := o.z) (a := a.z) hle.2.2.1 hle.2.2.2.2.2 (by omega))
    fun t ⟨e₃, k₃, O₃⟩ => ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.wordsVal (by omega) (by omega), O₂.wordsVal (by omega) (by omega), e₁]
  · rw [O₃.wordsVal (by omega) (by omega), e₂, O₁.wordsVal (by omega) (by omega)]
  · rw [e₃, O₂.wordsVal (by omega) (by omega), O₁.wordsVal (by omega) (by omega)]
  · exact (O₁.unch.trans (O₂.unch.trans O₃.unch)).mono fun w hw => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h <;> simp [h]

theorem clob_powClob : ∀ r ∈ clob, r ∈ powClob := fun _ h => List.mem_cons_of_mem _ h


end VG.Proof.Weierstrass.X86
