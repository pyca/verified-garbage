import VerifiedGarbage.Proof.Weierstrass.X86.InvRow

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
