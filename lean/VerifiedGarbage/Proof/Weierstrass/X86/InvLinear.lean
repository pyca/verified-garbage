import VerifiedGarbage.Proof.Weierstrass.X86.InvLinearMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvShift

/-! # The signed multiword divstep matrix row -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

structure LinearLay (size u v acc a b tmp n k : Nat) : Prop where
  prefix_le : k + 1 ≤ n
  u_bound : u + 4 ≤ size
  v_bound : v + 4 ≤ size
  a_bound : a + 4 * n ≤ size
  b_bound : b + 4 * n ≤ size
  acc_bound : acc + 4 * (n + 2) ≤ size
  tmp_bound : tmp + 4 * (k + 1) ≤ size
  au : u + 4 ≤ acc ∨ acc + 4 * (n + 2) ≤ u
  av : v + 4 ≤ acc ∨ acc + 4 * (n + 2) ≤ v
  aa : a + 4 * n ≤ acc ∨ acc + 4 * (n + 2) ≤ a
  ab : b + 4 * n ≤ acc ∨ acc + 4 * (n + 2) ≤ b
  tu : u + 4 ≤ tmp ∨ tmp + 4 * (k + 1) ≤ u
  tv : v + 4 ≤ tmp ∨ tmp + 4 * (k + 1) ≤ v
  ta : a + 4 * n ≤ tmp ∨ tmp + 4 * (k + 1) ≤ a
  tb : b + 4 * n ≤ tmp ∨ tmp + 4 * (k + 1) ≤ b
  acc_tmp : tmp + 4 * (k + 1) ≤ acc ∨ acc + 4 * (n + 2) ≤ tmp

theorem word_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem}
    (U : Unch base W m m') {d : Nat}
    (hd : ∀ w ∈ W, d + 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) (hb : d + 4 ≤ 2 ^ 64) :
    w32 m' base d = w32 m base d := by
  have H := Outs.val32 U (d := d) (k := 1) hd hb
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

theorem linear_ok {s : State} {base : Addr} {size u v acc a b tmp n k : Nat}
    (hs : Scr s base size) (L : LinearLay size u v acc a b tmp n k) :
    WP isa (.block (linear u v acc a b tmp n k)) s fun z =>
      Unch base [(acc, 4 * (n + 2)), (tmp, 4 * (k + 1))] s.mem z.mem ∧ Keeps clob s z ∧
      (val32 z.mem base acc (k + 2) : Int) % 2 ^ (32 * (k + 2)) =
        ((s.mem.readW (off base u) 32).toInt * val32 s.mem base a n +
         (s.mem.readW (off base v) 32).toInt * val32 s.mem base b n) % 2 ^ (32 * (k + 2)) := by
  have hn := hs.nowrap
  have hp := L.prefix_le
  have ha := L.a_bound; have hb := L.b_bound; have hc := L.acc_bound; have ht := L.tmp_bound
  have hu := L.u_bound; have hv := L.v_bound
  have hst := L.acc_tmp; have hsa := L.ta; have hsb := L.tb
  unfold linear
  refine WP.block_append (WP.block_append (WP.mono
    (linearUnsigned_ok hs L.u_bound L.v_bound L.a_bound L.b_bound L.acc_bound L.au L.av L.aa L.ab)
    fun s₁ ⟨O₁, V₁, K₁⟩ => ?_))
  have hs₁ := hs.of_keeps K₁ (by decide)
  have C₁u := O₁.w32 L.au (by omega)
  have C₁v := O₁.w32 L.av (by omega)
  have A₁ := O₁.val32 (k := k + 1) (d := a) (by have := L.aa; omega) (by omega)
  have B₁ := O₁.val32 (k := k + 1) (d := b) (by have := L.ab; omega) (by omega)
  have H₀ : val32 s₁.mem base acc (k + 2) =
      (w32 s.mem base u * val32 s.mem base a n + w32 s.mem base v * val32 s.mem base b n) %
        2 ^ (32 * (k + 2)) := by
    rw [prefix_mod s₁.mem base acc (k + 2) (n + 2) (by omega), V₁]
  refine WP.mono (correction_ok hs₁ L.u_bound (by omega) (by omega) L.tmp_bound (by omega) (by omega))
    fun s₂ ⟨O₂, K₂, c, V₂⟩ => ?_
  rw [C₁u, A₁] at V₂
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  have C₂v : w32 s₂.mem base v = w32 s₁.mem base v := word_unch O₂
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · have := L.av; omega
        · exact L.tv) (by omega)
  have B₂ : val32 s₂.mem base b (k + 1) = val32 s₁.mem base b (k + 1) := Outs.val32 O₂
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · have := L.ab; omega
        · omega) (by omega)
  refine WP.mono (correction_ok hs₂ L.v_bound (by omega) (by omega) L.tmp_bound (by omega) (by omega))
    fun z ⟨O₃, K₃, d, V₃⟩ => ?_
  rw [C₂v, C₁v, B₂, B₁] at V₃
  have H := corrections_mod H₀ V₂ V₃
  refine ⟨?_, (K₁.trans K₂).trans K₃, ?_⟩
  · intro x hx
    have hacc := hx (acc, 4 * (n + 2)) (by simp)
    have htmp := hx (tmp, 4 * (k + 1)) (by simp)
    have small : ∀ w ∈ [(acc, 4 * (k + 2)), (tmp, 4 * (k + 1))],
        ofs base x < w.1 ∨ w.1 + w.2 ≤ ofs base x := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega
    rw [O₃ x small, O₂ x small, O₁ x hacc]
  · have HX := shifted_prefix_mod s.mem base a (k + 1) n hp
    have HY := shifted_prefix_mod s.mem base b (k + 1) n hp
    have E := Divstep.W32.lin_words
      (M := (2 : Int) ^ (32 * (k + 2)))
      (V := val32 z.mem base acc (k + 2))
      (X := val32 s.mem base a n) (X' := val32 s.mem base a (k + 1))
      (Y := val32 s.mem base b n) (Y' := val32 s.mem base b (k + 1))
      (W := w32 s.mem base u) (W' := w32 s.mem base v)
      (c := 2 ^ 31 ≤ w32 s.mem base u) (c' := 2 ^ 31 ≤ w32 s.mem base v)
      (by exact_mod_cast HX) (by exact_mod_cast HY) (by exact_mod_cast H)
    simpa only [w32, Divstep.W32.toInt_sgn] using E

end VG.Proof.Weierstrass.X86.Inv
