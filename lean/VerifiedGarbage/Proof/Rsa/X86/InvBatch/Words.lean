module
public import VerifiedGarbage.Proof.Mont.Words32

public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Words
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Matrix
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
public import Mathlib.Data.BitVec
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Divstep.Word32
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Start

/-! # The thirty-step matrix at full workspace strides and a half-width value -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.InvBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv

theorem words_ok {s : State} {base : Addr} {size w n : Nat} {d f g : Int}
    (hs : Scr s base size) (hn : 16 ≤ w) (hz : offset w 15 ≤ size)
    (hd : s.mem.readW (VG.Proof.Mont.off base (offset w 3)) 32=BitVec.ofInt 32 d)
    (hf : (val32 s.mem base (offset w 4) (n+1) : Int)%2^(32*(n+1))=f%2^(32*(n+1)))
    (hg : (val32 s.mem base (offset w 5) (n+1) : Int)%2^(32*(n+1))=g%2^(32*(n+1)))
    (hdb : |d|+64<2^30) (hfo : f%2=1) :
    WP isa (.seq (.block (VG.Impl.Rsa.X86.InvBatch.start w)) (VG.Impl.Weierstrass.X86.Inv.wordSteps (offset w 3) 30)) s fun z =>
      GcdBatch.MatrixAt w base (Divstep.msteps 30 (Divstep.MSt.init d f g)) z ∧
      Keeps wordClob s z ∧ Outside base (offset w 3) 28 s.mem z.mem := by
  have nowrap := hs.nowrap
  refine WP.seq (WP.mono (GcdBatch.start_ok hs hn hz) fun s₁ ⟨V₁,K₁,O₁⟩ => ?_)
  change Outside base (offset w 3+4) 24 s.mem s₁.mem at O₁
  change wordState s₁.mem base (offset w 3)=_ at V₁
  have rel : (wordState s₁.mem base (offset w 3)).rel (Divstep.MSt.init d f g) 32 := by
    rw [V₁]
    exact ⟨hd,rfl,rfl,rfl,rfl,GcdBatch.low_cong hf,GcdBatch.low_cong hg⟩
  have matrix := Divstep.W32.wsteps_rel (by decide) rel hdb hfo 30 (by decide)
  refine WP.mono (wordSteps_ok (hs.of_keeps K₁ (by decide)) (by dsimp only [offset] at *; omega)
    (by decide) (by decide)) fun z ⟨V₂,K₂,O₂⟩ => ⟨?_,(K₁.mono (by decide)).trans K₂,?_⟩
  · rw [← V₂] at matrix
    obtain ⟨D,U,V,Q,R,_,_⟩ := matrix
    exact ⟨D,U,V,Q,R⟩
  · intro x hx
    rw [O₂ x hx,O₁ x (by omega)]

end VG.Proof.Rsa.X86.InvBatch
