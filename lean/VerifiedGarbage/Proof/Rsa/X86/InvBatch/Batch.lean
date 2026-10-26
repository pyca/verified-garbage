module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Update
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Words
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Weierstrass.X86.InvLayout
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
import Mathlib.Data.BitVec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # One complete matrix batch of the RSA inverse -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.Impl.Rsa.X86.InvBatch VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv

 def batchWrites (w : Nat) : List (Nat × Nat) := (offset w 3,28)::updateWrites w

 local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega))

 theorem batch_ok {s : State} {base : Addr} {size w n p iv cap : Nat} {st : VG.Proof.Divstep.W32.IState}
    (hs : Scr s base size) (hn : 16≤n) (hw : w=2*n) (he : n%2=0) (hz : offset w 15≤size)
    (h : StateAt w n base p iv st s) (hi : iv<2^32) (hp : 0<p) (hinv : (p*iv+1)%2^32=0)
    (hd : |st.d|+64<2^30) (odd : st.f%2=1)
    (hf : |st.f|≤cap) (hg : |st.g|≤cap) (capBound : cap<2^(32*n+1))
    (ha : |st.a|≤p) (hb : |st.b|≤p) :
    WP isa (.seq (.seq (.block (VG.Impl.Rsa.X86.InvBatch.start w))
      (VG.Impl.Weierstrass.X86.Inv.wordSteps (offset w 3) 30))
      (.block (VG.Impl.Rsa.X86.InvBatch.update w n))) s fun z =>
      StateAt w n base p iv (VG.Proof.Divstep.W32.batch 30 p iv st) z ∧
      Keeps wordClob s z ∧ Unch base (batchWrites w) s.mem z.mem := by
  have nowrap := hs.nowrap
  generalize hT : VG.Proof.Divstep.msteps 30 (VG.Proof.Divstep.MSt.init st.d st.f st.g)=T
  have mat := VG.Proof.Divstep.msteps_mat (d:=st.d) (g:=st.g) odd 30
  have bound := VG.Proof.Divstep.msteps_bnd st.d st.f st.g 30
  rw [hT] at mat bound
  change 2^30*T.f=T.u*st.f+T.v*st.g ∧ 2^30*T.g=T.q*st.f+T.r*st.g at mat
  change |T.u|+|T.v|≤2^30 ∧ |T.q|+|T.r|≤2^30 at bound
  refine WP.seq (WP.mono (words_ok hs (by omega) hz h.d h.f h.g hd odd) fun u ⟨M,K,O⟩ => ?_)
  rw [hT] at M
  have hu := hs.of_keeps K (by decide)
  have input : RowInput w n base p iv T st u := by
    refine ⟨M,?_,?_,?_,?_,?_,?_⟩
    · rw [O.val32 (by apart) (by apart)]; exact h.modulus
    · rw [O.w32 (by apart) (by apart)]; exact h.inverse
    · rw [O.val32 (by apart) (by apart)]; exact h.f
    · rw [O.val32 (by apart) (by apart)]; exact h.g
    · rw [O.val32 (by apart) (by apart)]; exact h.a
    · rw [O.val32 (by apart) (by apart)]; exact h.b
  have topA : w32 u.mem base (offset w 6+4*n)=0 := by rw [O.w32 (by apart) (by apart)]; exact h.aTop
  have topB : w32 u.mem base (offset w 7+4*n)=0 := by rw [O.w32 (by apart) (by apart)]; exact h.bTop
  refine WP.mono (update_ok hu hn hw he hz input hi hp hinv bound.1 bound.2 hf hg capBound
    ⟨T.f,mat.1.symm⟩ ⟨T.g,mat.2.symm⟩ ha hb topA topB) fun z ⟨I,K',O'⟩ => ?_
  refine ⟨?_,K.trans K',?_⟩
  · unfold VG.Proof.Divstep.W32.batch
    rw [hT]
    exact I
  · intro x hx
    exact (O' x fun r hr => hx r (List.mem_cons_of_mem _ hr)).trans
      (O x (hx (offset w 3,28) (List.mem_cons_self ..)))

end VG.Proof.Rsa.X86.InvBatch
