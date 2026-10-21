module

import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Absolute
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Mont.X86.Ops
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Returning zero-padded full-width GCD and inverse values -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.Impl.Rsa.X86.InvBatch VG.Impl.Mont.X86
 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

 theorem zeroCopy_ok {s : State} {base : Addr} {size dst src n w : Nat}
    (hs : Scr s base size) (hw : n≤w) (hd : dst+4*w≤size) (hsrc : src+4*n≤size)
    (sep : dst+4*w≤src ∨ src+4*n≤dst) :
    WP isa (.block (zeros dst w ++ VG.Impl.Weierstrass.X86.copy n dst src)) s fun z =>
      val32 z.mem base dst w=val32 s.mem base src n ∧
      Keeps [.eax] s z ∧ Outside base dst (4*w) s.mem z.mem := by
  have nw := hs.nowrap
  refine WP.block_append (WP.mono (zeros_ok hs hd) fun s1 ⟨O1,V1,K1⟩ => ?_)
  refine WP.mono (copy_ok n (hs.of_keeps K1 (by decide)) (by omega) hsrc (by omega)) fun z ⟨V2,K2,O2⟩ => ?_
  have split := val32_append s1.mem base dst n (w-n)
  rw [show n+(w-n)=w by omega,V1] at split
  have tailZero : val32 s1.mem base (dst+4*n) (w-n)=0 := by
    have power := Nat.two_pow_pos (32*n)
    by_contra h
    have bound := Nat.mul_le_mul_left (2^(32*n)) (show 1≤val32 s1.mem base (dst+4*n) (w-n) by omega)
    omega
  refine ⟨?_,K1.trans K2,?_⟩
  · have split2 := val32_append z.mem base dst n (w-n)
    rw [show n+(w-n)=w by omega] at split2
    rw [split2,V2,O1.val32 (by omega) (by omega),O2.val32 (by omega) (by omega),tailZero,Nat.mul_zero,Nat.add_zero]
  · exact O1.trans (O2.mono (by omega) (by omega))

 def finishWrites (w : Nat) : List (Nat × Nat) := [(offset w 1,4*w),(offset w 3,4*w)]
local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega))

 theorem finish_ok {s : State} {base : Addr} {size w n a : Nat} {f : Int}
    (hs : Scr s base size) (hn : 16≤n) (hw : w=2*n) (hz : offset w 15≤size)
    (hb : |f|<2^(32*n))
    (hc : (val32 s.mem base (offset w 4) n : Int)%(2^(32*n) : Int)=f%(2^(32*n) : Int))
    (sign : (2^31≤w32 s.mem base (offset w 4+4*n)) ↔ f<0)
    (coef : val32 s.mem base (offset w 6) n=a) :
    WP isa (.block (finish w n)) s fun z =>
      val32 z.mem base (offset w 1) w=f.natAbs ∧ val32 z.mem base (offset w 3) w=a ∧
      Keeps [.eax,.ecx,.edx] s z ∧ Unch base (finishWrites w) s.mem z.mem := by
  have nw := hs.nowrap
  unfold finish
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (absolute_low_ok hs hn hw hz hb hc sign) fun s1 ⟨V1,T1,K1,O1⟩ => ?_)
  have full1 : val32 s1.mem base (offset w 1) w=f.natAbs := by
    have sp := val32_append s1.mem base (offset w 1) n (w-n)
    rw [show n+(w-n)=w by omega,V1,T1,Nat.mul_zero,Nat.add_zero] at sp
    exact sp
  refine WP.mono (zeroCopy_ok (hs.of_keeps K1 (by decide)) (n:=n) (w:=w) (dst:=offset w 3) (src:=offset w 6)
    (by omega) (by apart) (by apart) (by apart)) fun z ⟨V2,K2,O2⟩ => ?_
  refine ⟨?_,?_,K1.trans (K2.mono (by decide)),?_⟩
  · rw [O2.val32 (by apart) (by apart),full1]
  · rw [V2,O1.val32 (by apart) (by apart),coef]
  · intro x hx
    rw [O2 x (hx (offset w 3,4*w) (by simp [finishWrites])),O1 x (hx (offset w 1,4*w) (by simp [finishWrites]))]

end VG.Proof.Rsa.X86.InvBatch
