module

import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Red
public import VerifiedGarbage.Proof.Weierstrass.X86.InvLinear
import VerifiedGarbage.Proof.Weierstrass.X86.InvLayout
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Divstep.Tc32Words
public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Weierstrass.X86.InvRed
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead

/-! # A coefficient matrix row followed by reduction with a loaded inverse -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass VG.Impl.Mont VG.Proof.Weierstrass.X86.Inv

theorem abHalfLoaded_ok {s : State} {base : Addr} {size u v acc a b tmp out iv k p : Nat}
    {M : Mod} {cu cv x y : Int} (hs : Scr s base size)
    (L : LinearLay size u v acc a b tmp (k + 1) k) (R : RedLay M size acc tmp out (k + 1))
    (hivfit : iv+4≤size)
    (hiva : iv+4≤acc ∨ acc+4*(k+3)≤iv) (hivt : iv+4≤tmp ∨ tmp+4*(k+1)≤iv)
    (hiv : w32 s.mem base iv=(minv32 M).toNat)
    (hp : 0 < p) (hm : val32 s.mem base M.mo (k + 1) = p)
    (hinv : (p * (minv32 M).toNat + 1) % 2 ^ 32 = 0)
    (hu : s.mem.readW (off base u) 32 = BitVec.ofInt 32 cu)
    (hv : s.mem.readW (off base v) 32 = BitVec.ofInt 32 cv)
    (huv : |cu| + |cv| ≤ 2 ^ 30)
    (hx : (val32 s.mem base a (k + 1) : Int) = x) (hy : (val32 s.mem base b (k + 1) : Int) = y)
    (hxb : |x| ≤ p) (hyb : |y| ≤ p) :
    WP isa (.block (linear u v acc a b tmp (k + 1) k ++ VG.Impl.Rsa.X86.InvBatch.reduceLoaded M acc tmp out iv)) s fun z =>
      (val32 z.mem base out (k + 1) : Int) = Divstep.W32.mred p (minv32 M).toNat (cu * x + cv * y) ∧
      Keeps wordClob s z ∧
      Unch base [(acc, 4 * (k + 1 + 2)), (tmp, 4 * (k + 1 + 1)),
        (M.tmp, 4 * (k + 1)), (out, 4 * (k + 1))] s.mem z.mem := by
  have hn := hs.nowrap
  have hmod := R.mod_bound; have ham := R.am; have htm := R.tm
  refine WP.block_append (WP.mono (linear_ok hs L) fun s₁ ⟨O₁, K₁, V₁⟩ => ?_)
  rw [hu, hv, Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv), hx, hy] at V₁
  have hm₁ : val32 s₁.mem base M.mo (k + 1) = p := by
    rw [Outs.val32 O₁ (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega) (by omega), hm]
  have bound : |cu * x + cv * y| ≤ 2 ^ 31 * p := by
    have H := Divstep.W32.comb_le huv hxb hyb
    have hp' : (0 : Int) ≤ p := Int.natCast_nonneg _
    omega
  have iv₁ : w32 s₁.mem base iv=(minv32 M).toNat := by
    rw [w32,read32_unch O₁ (by
      intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl <;> dsimp only <;> omega) (by omega)]
    exact hiv
  refine WP.mono (reduceLoaded_ok (hs.of_keeps K₁ (by decide)) R hivfit
    (by omega) iv₁ hp hm₁ hinv bound V₁)
    fun z ⟨O₂, K₂, V₂⟩ => ⟨V₂, (K₁.mono (by decide)).trans K₂, ?_⟩
  intro q hq
  rw [O₂ q hq]
  apply O₁ q
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact hq (acc, 4 * (k + 1 + 2)) (by simp)
  · have := hq (tmp, 4 * (k + 1 + 1)) (by simp)
    simp only
    omega

end VG.Proof.Rsa.X86.InvBatch
