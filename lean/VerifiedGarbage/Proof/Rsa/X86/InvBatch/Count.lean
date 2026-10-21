module

import VerifiedGarbage.Proof.Rsa.X86.InvBatch.StateFrame
public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Batch
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Count
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.State
public import VerifiedGarbage.Proof.Weierstrass.Unch

/-! # The public batch counter in the existing inverse header -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.Impl.Rsa.X86.InvBatch VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv

 def batchCode (w n : Nat) : Prog isa :=
 .seq (.seq (.seq (.block (VG.Impl.Rsa.X86.InvBatch.start w))
   (VG.Impl.Weierstrass.X86.Inv.wordSteps (offset w 3) 30)) (.block (VG.Impl.Rsa.X86.InvBatch.update w n)))
   (.block (VG.Impl.Rsa.X86.GcdBatch.countDown 100))

 def countedWrites (w : Nat) : List (Nat × Nat) := (100,4)::batchWrites w
 local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega))


 theorem countedBatch_ok {s : State} {base : Addr} {size w n p iv cap j : Nat} {st : VG.Proof.Divstep.W32.IState}
    (hs : Scr s base size) (hn : 16≤n) (hw : w=2*n) (he : n%2=0) (hz : offset w 15≤size)
    (h : StateAt w n base p iv st s) (hi : iv<2^32) (hp : 0<p) (hinv : (p*iv+1)%2^32=0)
    (hd : |st.d|+64<2^30) (odd : st.f%2=1)
    (hf : |st.f|≤cap) (hg : |st.g|≤cap) (capBound : cap<2^(32*n+1))
    (ha : |st.a|≤p) (hb : |st.b|≤p) (jp : 1≤j) (jl : j<2^32) (counter : w32 s.mem base 100=j) :
    WP isa (batchCode w n) s fun z => StateAt w n base p iv (VG.Proof.Divstep.W32.batch 30 p iv st) z ∧
      w32 z.mem base 100=j-1 ∧ z.zf=some (decide (j-1=0)) ∧
      Keeps wordClob s z ∧ Unch base (countedWrites w) s.mem z.mem := by
  have nowrap := hs.nowrap
  unfold batchCode
  refine WP.seq (WP.mono (batch_ok hs hn hw he hz h hi hp hinv hd odd hf hg capBound ha hb)
    fun u ⟨I,K,O⟩ => ?_)
  have hu := hs.of_keeps K (by decide)
  have cu : w32 u.mem base 100=j := by
    rw [word_unch O (by
      intro r hr; simp only [batchWrites,updateWrites,rowWrites,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_assoc] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> apart) (by apart),counter]
  refine WP.mono (GcdBatch.countDown_ok hu (d:=100) (by apart) jp jl cu) fun z ⟨c,zf,K',O'⟩ => ?_
  refine ⟨I.keep_counter hu hn hw hz O',c,zf,K.trans (K'.mono (by decide)),?_⟩
  intro x hx
  exact (O' x (hx (100,4) (List.mem_cons_self ..))).trans
    (O x fun r hr => hx r (List.mem_cons_of_mem _ hr))

end VG.Proof.Rsa.X86.InvBatch
