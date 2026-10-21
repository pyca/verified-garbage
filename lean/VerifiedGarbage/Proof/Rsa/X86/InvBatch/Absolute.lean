module

import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.InitWords
public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
import VerifiedGarbage.Proof.Rsa.Divstep.Absolute
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.InvShift
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # The absolute final GCD from its signed representation -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.InvBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass.X86.Inv

local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega))

theorem absolute_low_ok {s : State} {base : Addr} {size w n : Nat} {f : Int}
    (hs : Scr s base size) (hn : 16 ≤ n) (hw : w=2*n) (hz : offset w 15 ≤ size)
    (hb : |f|<2^(32*n))
    (hc : (val32 s.mem base (offset w 4) n : Int)%(2^(32*n) : Int)=f%(2^(32*n) : Int))
    (sign : (2^31 ≤ w32 s.mem base (offset w 4+4*n)) ↔ f<0) :
    WP isa (.block (absolute w n)) s fun z =>
      val32 z.mem base (offset w 1) n=f.natAbs ∧
      val32 z.mem base (offset w 1+4*n) (w-n)=0 ∧
      Keeps [.eax,.ecx,.edx] s z ∧ Outside base (offset w 1) (4*w) s.mem z.mem := by
  have nowrap := hs.nowrap
  have en : n-1+1=n := by omega
  unfold absolute
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono
    (zeros_ok hs (acc:=offset w 1) (k:=w) (by apart)) fun s₁ ⟨O₁,V₁,K₁⟩ => ?_)))
  have split := val32_append s₁.mem base (offset w 1) n (w-n)
  rw [show n+(w-n)=w by omega,V₁] at split
  have lowZero : val32 s₁.mem base (offset w 1) n=0 := by omega
  have tailZero : val32 s₁.mem base (offset w 1+4*n) (w-n)=0 := by
    have pow := Nat.two_pow_pos (32*n)
    by_contra h
    have bound := Nat.mul_le_mul_left (2^(32*n)) (show 1≤val32 s₁.mem base (offset w 1+4*n) (w-n) by omega)
    omega
  have hs₁ := hs.of_keeps K₁ (by decide)
  have sub := chainSubSelf_ok hs₁ (n-1) (acc:=offset w 1) (b:=offset w 4)
    (by rw [en]; apart) (by rw [en]; apart) (by rw [en]; apart)
  rw [en] at sub
  rw [subInPlace_eq]
  refine WP.mono sub fun s₂ ⟨O₂,⟨c,_,V₂⟩,K₂⟩ => ?_
  rw [O₁.val32 (by apart) (by apart),lowZero,Nat.zero_add] at V₂
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (maskOf_ok hs₂ (coefficient:=offset w 4+4*n) (by apart)) fun s₃ ⟨C₃,K₃,M₃⟩ => ?_
  rw [O₂.w32 (by apart) (by apart),O₁.w32 (by apart) (by apart)] at C₃
  simp only [sign] at C₃
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  refine WP.mono (sel_ok (decide (f<0)) n hs₃ (by simpa only [decide_eq_true_eq] using C₃)
    (o:=offset w 1) (a:=offset w 4) (b:=offset w 1)
    (by apart) (by apart) (by apart) (by apart) (by apart)) fun z ⟨V₄,K₄,O₄⟩ => ⟨?_,?_,?_,?_⟩
  · rw [V₄,M₃,O₂.val32 (d:=offset w 4) (by apart) (by apart),O₁.val32 (d:=offset w 4) (by apart) (by apart)]
    simp only [decide_eq_true_eq]
    exact VG.Proof.Rsa.Divstep.abs_select (Nat.two_pow_pos _) hb (val32_lt _ _ _ _) (by exact_mod_cast hc) ⟨c,V₂⟩
  · rw [O₄.val32 (by apart) (by apart),M₃,O₂.val32 (by apart) (by apart),tailZero]
  · have Kstart : Keeps [.eax,.ecx,.edx] s s₁ := K₁.mono (by decide)
    exact ((Kstart.trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))
  · intro x hx
    rw [O₄ x (by apart),M₃,O₂ x (by apart),O₁ x hx]

end VG.Proof.Rsa.X86.InvBatch
