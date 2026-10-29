module

public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Divstep.Steps
public import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Weierstrass.X86.InvLinear

import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Update
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Count
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Weierstrass.X86.InvLayout
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.BitVec
import Mathlib.Tactic.Linarith
import VerifiedGarbage.Proof.Divstep.BatchBasic
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Start
import VerifiedGarbage.Proof.Divstep.Word32
import Mathlib.Algebra.Group.Monoid
import VerifiedGarbage.Proof.Framework.GetElem
/-! # One complete batch updates the GCD state and the public counter -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/GcdBatch/Matrix.lean`, which only this module imported.
section

/-! # The transition matrix stored in the RSA workspace -/
section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.Impl.Rsa.X86.GcdBatch VG.Proof.Mont
structure MatrixAt (n : Nat) (base : Addr) (T : Divstep.MSt) (s : State) : Prop where
  d : s.mem.readW (VG.Proof.Mont.off base (offset n 3)) 32 = BitVec.ofInt 32 T.d
  u : s.mem.readW (VG.Proof.Mont.off base (offset n 3+12)) 32 = BitVec.ofInt 32 T.u
  v : s.mem.readW (VG.Proof.Mont.off base (offset n 3+16)) 32 = BitVec.ofInt 32 T.v
  q : s.mem.readW (VG.Proof.Mont.off base (offset n 3+20)) 32 = BitVec.ofInt 32 T.q
  r : s.mem.readW (VG.Proof.Mont.off base (offset n 3+24)) 32 = BitVec.ofInt 32 T.r

end VG.Proof.Rsa.X86.GcdBatch
end

end

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/GcdBatch/Words.lean`, which only this module imported.
section

/-! # Thirty low-word divsteps produce the full transition matrix -/

section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.GcdBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv


theorem low_cong {m : Mem} {base : Addr} {d n : Nat} {x : Int}
    (h : (val32 m base d (n+1) : Int)%2^(32*(n+1))=x%2^(32*(n+1))) :
    ((m.readW (VG.Proof.Mont.off base d) 32).toNat : Int)%2^32=x%2^32 := by
  have D : (2:Int)^32 ∣ 2^(32*(n+1)) := pow_dvd_pow 2 (by omega)
  have E : (w32 m base d : Int)%2^32=(val32 m base d (n+1) : Int)%2^32 := by
    rw [val32,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Int.add_mul_emod_self_left]
  rw [E,← Int.emod_emod_of_dvd _ D,h,Int.emod_emod_of_dvd _ D]

theorem words_ok {s : State} {base : Addr} {size n : Nat} {d f g : Int}
    (hs : Scr s base size) (hn : 16 ≤ n) (hz : offset n 15 ≤ size)
    (hd : s.mem.readW (VG.Proof.Mont.off base (offset n 3)) 32=BitVec.ofInt 32 d)
    (hf : (val32 s.mem base (offset n 4) (n+1) : Int)%2^(32*(n+1))=f%2^(32*(n+1)))
    (hg : (val32 s.mem base (offset n 5) (n+1) : Int)%2^(32*(n+1))=g%2^(32*(n+1)))
    (hdb : |d|+64<2^30) (hfo : f%2=1) :
    WP isa (.seq (.block (start n)) (VG.Impl.Weierstrass.X86.Inv.wordSteps (offset n 3) 30)) s fun z =>
      MatrixAt n base (Divstep.msteps 30 (Divstep.MSt.init d f g)) z ∧
      Keeps wordClob s z ∧ Outside base (offset n 3) 28 s.mem z.mem := by
  have nowrap := hs.nowrap
  refine WP.seq (WP.mono (start_ok hs hn hz) fun s₁ ⟨V₁,K₁,O₁⟩ => ?_)
  have rel : (wordState s₁.mem base (offset n 3)).rel (Divstep.MSt.init d f g) 32 := by
    rw [V₁]
    exact ⟨hd,rfl,rfl,rfl,rfl,low_cong hf,low_cong hg⟩
  have matrix := Divstep.W32.wsteps_rel (by decide) rel hdb hfo 30 (by decide)
  refine WP.mono (wordSteps_ok (hs.of_keeps K₁ (by decide)) (by dsimp only [offset] at *; omega)
    (by decide) (by decide)) fun z ⟨V₂,K₂,O₂⟩ => ⟨?_,(K₁.mono (by decide)).trans K₂,?_⟩
  · rw [← V₂] at matrix
    obtain ⟨D,U,V,Q,R,_,_⟩ := matrix
    exact ⟨D,U,V,Q,R⟩
  · intro x hx
    rw [O₂ x hx,O₁ x (by omega)]

end VG.Proof.Rsa.X86.GcdBatch
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.GcdBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (read32_unch wordClob)

structure StateAt (n : Nat) (base : Addr) (I : Int × Int × Int) (s : State) : Prop where
  d : s.mem.readW (VG.Proof.Mont.off base (offset n 3)) 32 = BitVec.ofInt 32 I.1
  f : (val32 s.mem base (offset n 4) (n+1) : Int)%2^(32*(n+1))=I.2.1%2^(32*(n+1))
  g : (val32 s.mem base (offset n 5) (n+1) : Int)%2^(32*(n+1))=I.2.2%2^(32*(n+1))

def batchWrites (n : Nat) : List (Nat × Nat) :=
 [(offset n 3,5*(4*n+8)),(offset n 11,3*(4*n+8)),(100,4)]

local macro "apart" : tactic => `(tactic|
 (simp only [writes,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
   Prod.fst,Prod.snd,offset] at * <;> omega_arith))

theorem batch_ok {s : State} {base : Addr} {size n p j : Nat} {I : Int × Int × Int}
    (hs : Scr s base size) (hn : 16 ≤ n) (hz : offset n 15 ≤ size)
    (hI : StateAt n base I s) (hdb : |I.1|+64<2^30) (hodd : I.2.1%2=1)
    (hfb : |I.2.1| ≤ p) (hgb : |I.2.2| ≤ p) (hp : p<2^(32*n+1))
    (hj : 1 ≤ j) (hj32 : j<2^32) (hc : w32 s.mem base 100=j) :
    WP isa (batch n) s fun z => StateAt n base (Divstep.divsteps 30 I) z ∧
      w32 z.mem base 100=j-1 ∧ z.zf=some (decide (j-1=0)) ∧
      Keeps wordClob s z ∧ Unch base (batchWrites n) s.mem z.mem := by
  have nowrap := hs.nowrap
  generalize hT : Divstep.msteps 30 (Divstep.MSt.init I.1 I.2.1 I.2.2) = T
  have mat := Divstep.msteps_mat (d:=I.1) (g:=I.2.2) hodd 30
  have bound := Divstep.msteps_bnd I.1 I.2.1 I.2.2 30
  rw [hT] at mat bound
  change 2^30*T.f=T.u*I.2.1+T.v*I.2.2 ∧ 2^30*T.g=T.q*I.2.1+T.r*I.2.2 at mat
  change |T.u|+|T.v| ≤ 2^30 ∧ |T.q|+|T.r| ≤ 2^30 at bound
  have df : (T.d,T.f,T.g)=Divstep.divsteps 30 I := by
    have D := Divstep.msteps_dfg 30 (Divstep.MSt.init I.1 I.2.1 I.2.2)
    rw [hT] at D
    simpa only [Divstep.MSt.init,Prod.eta] using D
  unfold batch
  refine WP.seq (WP.mono (words_ok hs hn hz hI.d hI.f hI.g hdb hodd) fun s₁ ⟨M₁,K₁,O₁⟩ => ?_)
  rw [hT] at M₁
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.seq (WP.mono (update_ok hs₁ hn hz M₁.u M₁.v M₁.q M₁.r bound.1 bound.2
    (by rw [O₁.val32 (by apart) (by apart)]; exact hI.f)
    (by rw [O₁.val32 (by apart) (by apart)]; exact hI.g) hfb hgb hp
    ⟨T.f,mat.1.symm⟩ ⟨T.g,mat.2.symm⟩) fun s₂ ⟨F₂,G₂,K₂,O₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  have C₂ : w32 s₂.mem base 100=j := by
    rw [VG.Proof.Weierstrass.X86.Inv.word_unch O₂ (by apart) (by apart),O₁.w32 (by apart) (by apart),hc]
  refine WP.mono (countDown_ok hs₂ (d:=100) (by apart) hj hj32 C₂) fun z ⟨C₃,Z₃,K₃,O₃⟩ => ?_
  refine ⟨?_,C₃,Z₃,(K₁.trans (K₂.mono (by decide))).trans (K₃.mono (by decide)),?_⟩
  · rw [← df]
    refine ⟨?_,?_,?_⟩
    · rw [read32_unch O₃.unch (by apart) (by apart),read32_unch O₂ (by apart) (by apart)]
      exact M₁.d
    · rw [O₃.val32 (by apart) (by apart),F₂,← mat.1,Int.mul_ediv_cancel_left _ (by norm_num)]
    · rw [O₃.val32 (by apart) (by apart),G₂,← mat.2,Int.mul_ediv_cancel_left _ (by norm_num)]
  · intro x hx
    have hx3 := hx (offset n 3,5*(4*n+8)) (by simp [batchWrites])
    have hx11 := hx (offset n 11,3*(4*n+8)) (by simp [batchWrites])
    have hx100 := hx (100,4) (by simp [batchWrites])
    rw [O₃ x hx100,O₂ x (by apart),O₁ x (by dsimp only at *; apart)]

end VG.Proof.Rsa.X86.GcdBatch
