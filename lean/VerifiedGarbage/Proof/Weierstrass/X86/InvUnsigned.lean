import VerifiedGarbage.Impl.Weierstrass.X86.InvMemory
import VerifiedGarbage.Proof.Mont.X86.Chain
import VerifiedGarbage.Proof.Mont.X86.Ops

/-! ## `InvAdd` -/

section

/-! # In-place addition for signed divstep products -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem chainAddSelf_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {acc b : Nat} :
    ∀ k, acc + 4 * (k + 1) ≤ size → b + 4 * (k + 1) ≤ size →
    (acc + 4 * (k + 1) ≤ b ∨ b + 4 * (k + 1) ≤ acc) →
    WP isa (.block (chainK .add .adc acc acc b (k + 1))) s fun u =>
      Outside base acc (4 * (k + 1)) s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ val32 u.mem base acc (k + 1) + 2 ^ (32 * (k + 1)) * c.toNat =
        val32 s.mem base acc (k + 1) + val32 s.mem base b (k + 1)) ∧ Keeps [.eax] s u
  | 0, hacc, hb, _ => by
    rw [chainK_one]
    refine WP.mono (tripleAdd_ok hs (.inl ⟨rfl, rfl⟩) (j := 0) (by omega) (by omega) (by omega))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ⟨O, ⟨c, hc, ?_⟩, K⟩
    simp only [val32, Nat.mul_zero, Nat.add_zero, Bool.toNat_false] at V ⊢
    exact V
  | k + 1, hacc, hb, hsb => by
    have hn := hs.nowrap
    rw [chainK_succ, ite_eq_right_of_eq_false _ _ (eq_false (Nat.add_one_ne_zero k))]
    refine WP.block_append (WP.mono (chainAddSelf_ok hs k (by omega) (by omega) (by omega))
      fun s₁ ⟨O₁, ⟨c₁, hc₁, V₁⟩, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    refine WP.mono (tripleAdd_ok hs₁ (.inr ⟨rfl, hc₁⟩) (j := k + 1)
      (by omega) (by omega) (by omega)) fun u ⟨O, ⟨c, hc, V⟩, K⟩ =>
      ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (O.mono (by omega) (by omega)), ⟨c, hc, ?_⟩,
        K₁.trans K⟩
    rw [O₁.w32 (d := acc + 4 * (k + 1)) (by omega) (by omega),
      O₁.w32 (d := b + 4 * (k + 1)) (by omega) (by omega)] at V
    rw [val32_succ u.mem base acc (k + 1), val32_succ s.mem base acc (k + 1),
      val32_succ s.mem base b (k + 1), O.val32 (by omega) (by omega), pow32_succ (k + 1)]
    generalize 2 ^ (32 * (k + 1)) = P at *
    grind

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvRow` -/

section

/-! # Unsigned rows used by the divstep matrix updates -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem rowAdd_ok {s : State} {base : Addr} {size coefficient acc src n : Nat}
    (hs : Scr s base size) (hc : coefficient + 4 ≤ size) (ha : acc + 4 * (n + 2) ≤ size)
    (hb : src + 4 * n ≤ size) (sep : src + 4 * n ≤ acc ∨ acc + 4 * (n + 2) ≤ src)
    (hlt : val32 s.mem base acc (n + 2) + w32 s.mem base coefficient * val32 s.mem base src n <
      2 ^ (32 * (n + 2))) :
    WP isa (.block (rowAdd coefficient acc src n)) s fun u =>
      Outside base acc (4 * (n + 2)) s.mem u.mem ∧
      val32 u.mem base acc (n + 2) = val32 s.mem base acc (n + 2) +
        w32 s.mem base coefficient * val32 s.mem base src n ∧ Keeps clob s u := by
  simp only [rowAdd, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs hc) fun s₁ U₁ _ => ?_
  refine wp_movS rfl fun s₂ U₂ _ => ?_
  have K : Keeps clob s s₂ := (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  have hs₂ := hs.of_keeps K (by decide)
  have M : s₂.mem = s.mem := U₂.mem.trans U₁.mem
  have C : s₂.gpr .ecx = s.mem.readW (off base coefficient) 32 := by
    rw [U₂.other _ (by decide), U₁.gpr]
  have P : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * 0) := by
    change s₂.gpr .ebp = s₂.gpr .edi + 0
    simpa using U₂.gpr.trans (U₂.other .edi (by decide)).symm
  refine WP.mono (mulRow_ok hs₂ P (acc := acc) (b := src) (N := n) (w := acc) (by omega)
    hb (by omega) (by omega) (by rw [M, C]; exact hlt)) fun u ⟨O, V, K'⟩ => ?_
  rw [show 4 * n + 8 = 4 * (n + 2) by omega, M] at O
  rw [M, C] at V
  exact ⟨O, V, K.trans (K'.mono (by decide))⟩

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvSub` -/

section

/-! # In-place subtraction for signed divstep products -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem subInPlace_eq (dst src n : Nat) :
    subInPlace dst src n = chainK .sub .sbb dst dst src n := rfl

theorem chainSubSelf_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {acc b : Nat} :
    ∀ k, acc + 4 * (k + 1) ≤ size → b + 4 * (k + 1) ≤ size →
    (acc + 4 * (k + 1) ≤ b ∨ b + 4 * (k + 1) ≤ acc) →
    WP isa (.block (chainK .sub .sbb acc acc b (k + 1))) s fun u =>
      Outside base acc (4 * (k + 1)) s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ val32 u.mem base acc (k + 1) + val32 s.mem base b (k + 1) =
        val32 s.mem base acc (k + 1) + 2 ^ (32 * (k + 1)) * c.toNat) ∧ Keeps [.eax] s u
  | 0, hacc, hb, _ => by
    rw [chainK_one]
    refine WP.mono (tripleSub_ok hs (.inl ⟨rfl, rfl⟩) (j := 0) (by omega) (by omega) (by omega))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ⟨O, ⟨c, hc, ?_⟩, K⟩
    simp only [val32, Nat.mul_zero, Nat.add_zero, Bool.toNat_false] at V ⊢
    exact V
  | k + 1, hacc, hb, hsb => by
    have hn := hs.nowrap
    rw [chainK_succ, ite_eq_right_of_eq_false _ _ (eq_false (Nat.add_one_ne_zero k))]
    refine WP.block_append (WP.mono (chainSubSelf_ok hs k (by omega) (by omega) (by omega))
      fun s₁ ⟨O₁, ⟨c₁, hc₁, V₁⟩, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    refine WP.mono (tripleSub_ok hs₁ (.inr ⟨rfl, hc₁⟩) (j := k + 1)
      (by omega) (by omega) (by omega)) fun u ⟨O, ⟨c, hc, V⟩, K⟩ =>
      ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (O.mono (by omega) (by omega)), ⟨c, hc, ?_⟩,
        K₁.trans K⟩
    rw [O₁.w32 (d := acc + 4 * (k + 1)) (by omega) (by omega),
      O₁.w32 (d := b + 4 * (k + 1)) (by omega) (by omega)] at V
    rw [val32_succ u.mem base acc (k + 1), val32_succ s.mem base acc (k + 1),
      val32_succ s.mem base b (k + 1), O.val32 (by omega) (by omega), pow32_succ (k + 1)]
    generalize 2 ^ (32 * (k + 1)) = P at *
    grind

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvUnsigned` -/

section

/-! # Two unsigned rows before their signed corrections -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem product_bound (m : Mem) (base : Addr) (q a n : Nat) :
    w32 m base q * val32 m base a n < 2 ^ (32 * (n + 1)) := by
  have hq := (m.readW (off base q) 32).isLt
  change w32 m base q < 2 ^ 32 at hq
  have ha := val32_lt m base a n
  have hp : 0 < 2 ^ (32 * n) := by omega
  have h := Nat.mul_le_mul (show w32 m base q ≤ 2 ^ 32 - 1 by omega)
    (show val32 m base a n ≤ 2 ^ (32 * n) - 1 by omega)
  rw [pow32_succ]
  omega

theorem products_bound (m : Mem) (base : Addr) (u v a b n : Nat) :
    w32 m base u * val32 m base a n + w32 m base v * val32 m base b n <
      2 ^ (32 * (n + 2)) := by
  have A := product_bound m base u a n
  have B := product_bound m base v b n
  rw [show n + 2 = (n + 1) + 1 by omega, pow32_succ]
  omega

theorem linearUnsigned_ok {s : State} {base : Addr} {size u v acc a b n : Nat}
    (hs : Scr s base size) (hu : u + 4 ≤ size) (hv : v + 4 ≤ size)
    (ha : a + 4 * n ≤ size) (hb : b + 4 * n ≤ size) (hc : acc + 4 * (n + 2) ≤ size)
    (su : u + 4 ≤ acc ∨ acc + 4 * (n + 2) ≤ u)
    (sv : v + 4 ≤ acc ∨ acc + 4 * (n + 2) ≤ v)
    (sa : a + 4 * n ≤ acc ∨ acc + 4 * (n + 2) ≤ a)
    (sb : b + 4 * n ≤ acc ∨ acc + 4 * (n + 2) ≤ b) :
    WP isa (.block (linearUnsigned u v acc a b n)) s fun z =>
      Outside base acc (4 * (n + 2)) s.mem z.mem ∧
      val32 z.mem base acc (n + 2) =
        w32 s.mem base u * val32 s.mem base a n + w32 s.mem base v * val32 s.mem base b n ∧
      Keeps clob s z := by
  have hn := hs.nowrap
  unfold linearUnsigned
  refine WP.block_append (WP.block_append (WP.mono (zeros_ok hs hc) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_))
  have hs₁ := hs.of_keeps K₁ (by decide)
  have U₁ := O₁.w32 su (by omega)
  have A₁ := O₁.val32 sa (by omega)
  have V₁' := O₁.w32 sv (by omega)
  have B₁ := O₁.val32 sb (by omega)
  have bound := products_bound s.mem base u v a b n
  refine WP.mono (rowAdd_ok hs₁ hu hc ha sa (by rw [V₁, U₁, A₁]; omega))
    fun s₂ ⟨O₂, V₂, K₂⟩ => ?_
  rw [V₁, U₁, A₁, Nat.zero_add] at V₂
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  have V₂' := O₂.w32 sv (by omega)
  have B₂ := O₂.val32 sb (by omega)
  refine WP.mono (rowAdd_ok hs₂ hv hc hb sb (by rw [V₂, V₂', V₁', B₂, B₁]; exact bound))
    fun z ⟨O₃, V₃, K₃⟩ => ?_
  rw [V₂, V₂', V₁', B₂, B₁] at V₃
  exact ⟨(O₁.trans O₂).trans O₃, V₃, ((K₁.mono (by decide)).trans K₂).trans K₃⟩

end VG.Proof.Weierstrass.X86.Inv

end
