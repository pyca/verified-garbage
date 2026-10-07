import VerifiedGarbage.Proof.Divstep.Red32
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedSum
import VerifiedGarbage.Proof.Weierstrass.X86.InvNormalize
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedMath

/-! # Reduction of a signed divstep coefficient row -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass VG.Impl.Mont

structure RedLay (M : Mod) (size acc tmp out n : Nat) : Prop where
  width : words M = n
  positive : 0 < n
  acc_bound : acc + 4 * (n + 2) ≤ size
  tmp_bound : tmp + 4 * (n + 1) ≤ size
  out_bound : out + 4 * n ≤ size
  mod_bound : M.mo + 4 * n ≤ size
  sub_bound : M.tmp + 4 * n ≤ size
  ta : tmp + 4 * (n + 1) ≤ acc ∨ acc + 4 * (n + 2) ≤ tmp
  am : acc + 4 * (n + 2) ≤ M.mo ∨ M.mo + 4 * n ≤ acc
  tm : tmp + 4 * (n + 1) ≤ M.mo ∨ M.mo + 4 * n ≤ tmp
  sa : M.tmp + 4 * n ≤ acc ∨ acc + 4 * (n + 2) ≤ M.tmp
  sm : M.tmp + 4 * n ≤ M.mo ∨ M.mo + 4 * n ≤ M.tmp
  oa : out + 4 * n ≤ acc ∨ acc + 4 * (n + 2) ≤ out
  os : out + 4 * n ≤ M.tmp ∨ M.tmp + 4 * n ≤ out

theorem reduce_ok {s : State} {base : Addr} {size acc tmp out n p : Nat} {M : Mod} {t : Int}
    (hs : Scr s base size) (L : RedLay M size acc tmp out n)
    (hp : 0 < p) (hm : val32 s.mem base M.mo n = p)
    (hinv : (p * (minv32 M).toNat + 1) % 2 ^ 32 = 0)
    (ht : |t| ≤ 2 ^ 31 * p)
    (hval : (val32 s.mem base acc (n + 1) : Int) % 2 ^ (32 * (n + 1)) = t % 2 ^ (32 * (n + 1))) :
    WP isa (.block (reduce M acc tmp out)) s fun z =>
      Unch base [(acc, 4 * (n + 2)), (tmp, 4 * (n + 1)), (M.tmp, 4 * n), (out, 4 * n)] s.mem z.mem ∧
      Keeps wordClob s z ∧ (val32 z.mem base out n : Int) = Divstep.W32.mred p (minv32 M).toNat t := by
  have hn := hs.nowrap
  have ha := L.acc_bound; have htmp := L.tmp_bound; have hout := L.out_bound
  have hmod := L.mod_bound; have hsub := L.sub_bound
  have hta := L.ta; have ham := L.am; have htm := L.tm
  have hsa := L.sa; have hoa := L.oa
  unfold reduce
  rw [L.width]
  refine WP.block_append (WP.block_append (WP.mono
    (redSum_ok (minv32 M) hs ha hmod (by omega) (by omega) ham (by omega))
    fun s₁ ⟨O₁, K₁, V₁⟩ => ?_))
  have hs₁ := hs.of_keeps K₁ (by decide)
  have M₁ : val32 s₁.mem base M.mo n = p := by
    rw [Outs.val32 O₁ (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega) (by omega), hm]
  refine WP.mono (addIfNeg_ok hs₁ (acc := acc + 4) (modulus := M.mo) (tmp := tmp) (n := n)
    (by omega) hmod htmp (by omega) htm) fun s₂ ⟨O₂, K₂, V₂⟩ => ?_
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  have M₂ : val32 s₂.mem base M.mo n = p := by
    rw [Outs.val32 O₂ (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega) (by omega), M₁]
  have P : 2 ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by
    rw [pow32_succ, Nat.mul_comm]
  have E : val32 s₁.mem base acc (n + 2) =
      (val32 s.mem base acc (n + 1) + 2 ^ (32 * n) * 2 ^ 32 *
        (if 2 ^ (32 * n) * 2 ^ 31 ≤ val32 s.mem base acc (n + 1) then 2 ^ 32 - 1 else 0) +
        (w32 s.mem base acc * (minv32 M).toNat % 2 ^ 32) * p) %
        (2 ^ (32 * n) * 2 ^ 32 * 2 ^ 32) := by
    rw [V₁, hm]
    simp only [sign32]
    have P' : 2 ^ (32 * (n + 2)) = (2 ^ (32 * n) * 2 ^ 32) * 2 ^ 32 := by
      rw [show n + 2 = (n + 1) + 1 by omega, pow32_succ, pow32_succ]
      ring
    rw [P', P]
    rw [Nat.add_right_comm]
  have F : val32 s₂.mem base (acc + 4) (n + 1) =
      (val32 s₁.mem base (acc + 4) (n + 1) +
        if 2 ^ (32 * n) * 2 ^ 31 ≤ val32 s₁.mem base (acc + 4) (n + 1) then p else 0) %
        (2 ^ (32 * n) * 2 ^ 32) := by
    rw [V₂, M₁]
    simp only [sign32, P]
  have H := Divstep.W32.mred_first_nat
    (A := 2 ^ (32 * n)) (B := 2 ^ 32) (H := 2 ^ 31) (p := p) (m := (minv32 M).toNat)
    (W := val32 s.mem base acc (n + 1))
    (k := w32 s.mem base acc * (minv32 M).toNat % 2 ^ 32)
    (E := val32 s₁.mem base acc (n + 2)) (R := val32 s₁.mem base (acc + 4) (n + 1))
    (R₁ := val32 s₂.mem base (acc + 4) (n + 1)) (t := t)
    rfl rfl (Nat.two_pow_pos _) hp (by rw [← hm]; exact val32_lt _ _ _ _) hinv ht
    (by rw [← P]; exact val32_lt _ _ _ _)
    (by simpa only [← P, Nat.cast_pow, Nat.cast_ofNat] using hval)
    (by rw [← low32]) E (high32 _ _ _ _) F
  rcases H with ⟨bound, result⟩
  refine WP.mono (csub_ok hs₂ L.width L.positive (by omega) hout hsub hmod
    (by omega) L.sm (by omega) L.os M₂ bound) fun z ⟨O₃, V₃, K₃⟩ => ⟨?_, ?_, ?_⟩
  · intro x hx
    have hac := hx (acc, 4 * (n + 2)) (by simp)
    have htc := hx (tmp, 4 * (n + 1)) (by simp)
    rw [O₃ x (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> exact hx _ (by simp)),
      O₂ x (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega),
      O₁ x (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega)]
  · exact (K₁.trans (K₂.mono (by decide))).trans (K₃.mono (by decide))
  · rw [V₃]
    exact result

end VG.Proof.Weierstrass.X86.Inv
