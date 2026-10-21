module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.FourRows
public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.State
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Copying the four new rows into the next encoded inversion state -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.Impl.Rsa.X86.InvBatch VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv

 def nextState (p iv : Nat) (T : VG.Proof.Divstep.MSt) (st : VG.Proof.Divstep.W32.IState) : VG.Proof.Divstep.W32.IState :=
 ⟨T.d,(T.u*st.f+T.v*st.g)/2^30,(T.q*st.f+T.r*st.g)/2^30,
   VG.Proof.Divstep.W32.mred p iv (T.u*st.a+T.v*st.b),VG.Proof.Divstep.W32.mred p iv (T.q*st.a+T.r*st.b)⟩

 def updateWrites (w : Nat) : List (Nat × Nat) := rowWrites w++[(offset w 4,4*(4*w+8))]

 local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega))

 theorem update_ok {s : State} {base : Addr} {size w n p iv cap : Nat} {T : VG.Proof.Divstep.MSt}
    {st : VG.Proof.Divstep.W32.IState}
    (hs : Scr s base size) (hn : 16≤n) (hw : w=2*n) (he : n%2=0) (hz : offset w 15≤size)
    (h : RowInput w n base p iv T st s) (hi : iv<2^32) (hp : 0<p) (hinv : (p*iv+1)%2^32=0)
    (huv : |T.u|+|T.v|≤2^30) (hqr : |T.q|+|T.r|≤2^30)
    (hf : |st.f|≤cap) (hg : |st.g|≤cap) (capBound : cap<2^(32*n+1))
    (divF : 2^30∣T.u*st.f+T.v*st.g) (divG : 2^30∣T.q*st.f+T.r*st.g)
    (ha : |st.a|≤p) (hb : |st.b|≤p)
    (aTop : w32 s.mem base (offset w 6+4*n)=0) (bTop : w32 s.mem base (offset w 7+4*n)=0) :
    WP isa (.block (VG.Impl.Rsa.X86.InvBatch.update w n)) s fun z =>
      StateAt w n base p iv (nextState p iv T st) z ∧ Keeps wordClob s z ∧ Unch base (updateWrites w) s.mem z.mem := by
  have nowrap := hs.nowrap
  have code : VG.Impl.Rsa.X86.InvBatch.update w n=
      (fgCode w n 0++fgCode w n 1++abCode w n 0++abCode w n 1)++
      (VG.Impl.Weierstrass.X86.copy (n+1) (offset w 4) (offset w 0)++
       VG.Impl.Weierstrass.X86.copy (n+1) (offset w 5) (offset w 1)++
       VG.Impl.Weierstrass.X86.copy n (offset w 6) (offset w 13)++
       VG.Impl.Weierstrass.X86.copy n (offset w 7) (offset w 14)) := by
    simp only [VG.Impl.Rsa.X86.InvBatch.update,fgCode,abCode,Nat.mul_zero,Nat.add_zero,Nat.mul_one,
      Nat.reduceAdd,List.append_assoc]
  rw [code]
  refine WP.block_append (WP.mono (fourRows_ok hs hn hw he hz h hi hp hinv huv hqr hf hg capBound divF divG ha hb)
    fun r ⟨F,G,A,B,hr,kr,orr⟩ => ?_)
  have hsr := hs.of_keeps kr (by decide)
  rw [List.append_assoc,List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.Weierstrass.X86.copy_ok (n+1) hsr
    (o:=offset w 4) (a:=offset w 0) (by apart) (by apart) (by apart)) fun r₁ ⟨F₁,K₁,O₁⟩ => ?_)
  have hs₁ := hsr.of_keeps K₁ (by decide)
  refine WP.block_append (WP.mono (VG.Proof.Weierstrass.X86.copy_ok (n+1) hs₁
    (o:=offset w 5) (a:=offset w 1) (by apart) (by apart) (by apart)) fun r₂ ⟨G₂,K₂,O₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.block_append (WP.mono (VG.Proof.Weierstrass.X86.copy_ok n hs₂
    (o:=offset w 6) (a:=offset w 13) (by apart) (by apart) (by apart)) fun r₃ ⟨A₃,K₃,O₃⟩ => ?_)
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  refine WP.mono (VG.Proof.Weierstrass.X86.copy_ok n hs₃
    (o:=offset w 7) (a:=offset w 14) (by apart) (by apart) (by apart)) fun z ⟨B₄,K₄,O₄⟩ => ?_
  have copies : Outside base (offset w 4) (4*(4*w+8)) r.mem z.mem :=
    (((O₁.mono (by apart) (by apart)).trans (O₂.mono (by apart) (by apart))).trans
      (O₃.mono (by apart) (by apart))).trans (O₄.mono (by apart) (by apart))
  have readonly (d : Nat) (lo : offset w 2≤d) (up : d+4≤offset w 11) :
      w32 r.mem base d=w32 s.mem base d :=
    word_unch orr (by
      intro r hr; simp only [rowWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only [offset] at * <;> omega) (by apart)
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · apply BitVec.eq_of_toNat_eq
    change w32 z.mem base (offset w 3)=_
    rw [copies.w32 (by apart) (by apart)]
    exact congrArg BitVec.toNat hr.matrix.d
  · rw [copies.val32 (by apart) (by apart)]
    exact hr.modulus
  · rw [copies.w32 (by apart) (by apart)]
    exact hr.inverse
  · rw [O₄.val32 (by apart) (by apart),O₃.val32 (by apart) (by apart),O₂.val32 (by apart) (by apart),F₁]
    exact F
  · rw [O₄.val32 (by apart) (by apart),O₃.val32 (by apart) (by apart),G₂,O₁.val32 (by apart) (by apart)]
    exact G
  · rw [O₄.val32 (by apart) (by apart),A₃,O₂.val32 (by apart) (by apart),O₁.val32 (by apart) (by apart)]
    exact A
  · rw [B₄,O₃.val32 (by apart) (by apart),O₂.val32 (by apart) (by apart),O₁.val32 (by apart) (by apart)]
    exact B
  · rw [O₄.w32 (by apart) (by apart),O₃.w32 (by apart) (by apart),O₂.w32 (by apart) (by apart),O₁.w32 (by apart) (by apart),
      readonly _ (by apart) (by apart)]
    exact aTop
  · rw [O₄.w32 (by apart) (by apart),O₃.w32 (by apart) (by apart),O₂.w32 (by apart) (by apart),O₁.w32 (by apart) (by apart),
      readonly _ (by apart) (by apart)]
    exact bTop
  · exact kr.trans ((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans (K₄.mono (by decide)))
  · intro x hx
    exact (copies x (hx (offset w 4,4*(4*w+8)) (by simp [updateWrites]))).trans (orr x fun r hr => hx r (by simp only [updateWrites,List.mem_append]; exact Or.inl hr))

end VG.Proof.Rsa.X86.InvBatch
