module

public import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.InitWords
public import VerifiedGarbage.Proof.Rsa.Divstep.Absolute
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.InvShift
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

/-! # The absolute final GCD from its signed representation -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.GcdBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass.X86.Inv

local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega))

theorem finish_ok {s : State} {base : Addr} {size n : Nat} {f : Int}
    (hs : Scr s base size) (hn : 16 ≤ n) (hz : offset n 15 ≤ size)
    (hb : |f|<2^(32*n))
    (hc : (val32 s.mem base (offset n 4) n : Int)%(2^(32*n) : Int)=f%(2^(32*n) : Int))
    (sign : (2^31 ≤ w32 s.mem base (offset n 4+4*n)) ↔ f<0) :
    WP isa (.block (finish n)) s fun z =>
      val32 z.mem base (offset n 1) n=f.natAbs ∧
      Keeps [.eax,.ecx,.edx] s z ∧ Outside base (offset n 1) (4*n) s.mem z.mem := by
  have nowrap := hs.nowrap
  have en : n-1+1=n := by omega
  unfold finish
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono
    (zeros_ok hs (acc:=offset n 1) (k:=n) (by apart)) fun s₁ ⟨O₁,V₁,K₁⟩ => ?_)))
  have hs₁ := hs.of_keeps K₁ (by decide)
  have sub := chainSubSelf_ok hs₁ (n-1) (acc:=offset n 1) (b:=offset n 4)
    (by rw [en]; apart) (by rw [en]; apart) (by rw [en]; apart)
  rw [en] at sub
  rw [subInPlace_eq]
  refine WP.mono sub fun s₂ ⟨O₂,⟨c,_,V₂⟩,K₂⟩ => ?_
  rw [O₁.val32 (by apart) (by apart),V₁,Nat.zero_add] at V₂
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (maskOf_ok hs₂ (coefficient:=offset n 4+4*n) (by apart)) fun s₃ ⟨C₃,K₃,M₃⟩ => ?_
  rw [O₂.w32 (by apart) (by apart),O₁.w32 (by apart) (by apart)] at C₃
  simp only [sign] at C₃
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  refine WP.mono (sel_ok (decide (f<0)) n hs₃ (by simpa only [decide_eq_true_eq] using C₃)
    (o:=offset n 1) (a:=offset n 4) (b:=offset n 1)
    (by apart) (by apart) (by apart) (by apart) (by apart)) fun z ⟨V₄,K₄,O₄⟩ => ⟨?_,?_,?_⟩
  · rw [V₄,M₃,O₂.val32 (d:=offset n 4) (by apart) (by apart),O₁.val32 (d:=offset n 4) (by apart) (by apart)]
    simp only [decide_eq_true_eq]
    exact VG.Proof.Rsa.Divstep.abs_select (Nat.two_pow_pos _) hb (val32_lt _ _ _ _) (by exact_mod_cast hc) ⟨c,V₂⟩
  · have Kstart : Keeps [.eax,.ecx,.edx] s s₁ := K₁.mono (by decide)
    exact ((Kstart.trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))
  · intro x hx
    rw [O₄ x hx,M₃,O₂ x hx,O₁ x hx]

end VG.Proof.Rsa.X86.GcdBatch
