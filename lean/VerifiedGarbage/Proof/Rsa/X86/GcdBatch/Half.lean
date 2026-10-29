module

import VerifiedGarbage.Proof.Weierstrass.X86.InvHalf
import VerifiedGarbage.Proof.Divstep.Tc32Words
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import VerifiedGarbage.Proof.Weierstrass.X86.InvLinear
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.BitVec
import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Group.Nat.Defs

/-! # A signed matrix row with one extra input bit -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv

theorem half_wide_ok {s : State} {base : Addr} {size u v acc a b tmp dst k p : Nat} {cu cv f g : Int}
    (hs : Scr s base size) (L : LinearLay size u v acc a b tmp (k + 2) k)
    (hd : dst + 4 * (k + 2) ≤ size)
    (sep : dst + 4 * (k + 2) ≤ acc ∨ acc + 4 * (k + 2) ≤ dst)
    (hu : s.mem.readW (off base u) 32 = BitVec.ofInt 32 cu)
    (hv : s.mem.readW (off base v) 32 = BitVec.ofInt 32 cv)
    (huv : |cu| + |cv| ≤ 2 ^ 30)
    (hf : (val32 s.mem base a (k + 2) : Int) % 2 ^ (32 * (k + 2)) = f % 2 ^ (32 * (k + 2)))
    (hg : (val32 s.mem base b (k + 2) : Int) % 2 ^ (32 * (k + 2)) = g % 2 ^ (32 * (k + 2)))
    (hfb : |f| ≤ p) (hgb : |g| ≤ p) (hp : p < 2 ^ (32 * (k + 1) + 1))
    (hdiv : 2 ^ 30 ∣ cu * f + cv * g) :
    WP isa (.block (linear u v acc a b tmp (k + 2) k ++ shr30 dst acc (k + 2))) s fun z =>
      (val32 z.mem base dst (k + 2) : Int) % 2 ^ (32 * (k + 2)) =
        ((cu * f + cv * g) / 2 ^ 30) % 2 ^ (32 * (k + 2)) ∧ Keeps clob s z ∧
      Unch base [(acc, 4 * (k + 2 + 2)), (tmp, 4 * (k + 1)), (dst, 4 * (k + 2))] s.mem z.mem := by
  refine WP.block_append (WP.mono (linear_ok hs L) fun s₁ ⟨O₁, K₁, V₁⟩ => ?_)
  rw [hu, hv, Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv),
    Divstep.W32.cong_comb hf hg] at V₁
  have hcomb := Divstep.W32.comb_le huv hfb hgb
  have hpI : (p : Int) < 2 ^ (32 * (k+1)) * 2 := by
    exact_mod_cast (by simpa only [pow_succ] using hp)
  have cap : ((2 ^ (32*(k+1)) * 2^31 : Nat) : Int) = (2 : Int)^(32*(k+1)) * 2^31 := by push_cast; rfl
  have lo : -((2 ^ (32*(k+1)) * 2^31 : Nat) : Int) ≤ cu*f+cv*g := by
    rw [cap]; have := neg_abs_le (cu*f+cv*g); linarith
  have hi : cu*f+cv*g < ((2 ^ (32*(k+1)) * 2^31 : Nat) : Int) := by
    rw [cap]; have := le_abs_self (cu*f+cv*g); linarith
  have ha := L.acc_bound
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (shrSigned_ok hs₁ (dst := dst) (src := acc) (by omega) (by omega) hd sep
    (by exact_mod_cast V₁) (by simpa only [show k + 2 - 1 = k + 1 by omega] using lo)
    (by simpa only [show k + 2 - 1 = k + 1 by omega] using hi) (Int.mul_ediv_cancel' hdiv).symm)
    fun z ⟨V, K, O⟩ => ⟨?_, K₁.trans (K.mono (by decide)), ?_⟩
  · exact_mod_cast V
  · intro x hx
    rw [O x (hx (dst, 4 * (k + 2)) (by simp)), O₁ x (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hx (acc, 4 * (k + 2 + 2)) (by simp)
      · exact hx (tmp, 4 * (k + 1)) (by simp))]

end VG.Proof.Rsa.X86.GcdBatch
