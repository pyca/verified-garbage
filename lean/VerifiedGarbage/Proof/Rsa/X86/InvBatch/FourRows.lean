module

import VerifiedGarbage.Proof.Rsa.X86.InvBatch.RowFrame
import VerifiedGarbage.Proof.Weierstrass.X86.InvLayout
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Inputs
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Rows

/-! # Applying both value rows and both coefficient rows before copying -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.Impl.Rsa.X86.InvBatch VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv VG.Impl.Weierstrass.X86.Inv

 def fgCode (w n row : Nat) : List Instr :=
  linear (offset w 3+12+8*row) (offset w 3+16+8*row) (offset w 11) (offset w 4) (offset w 5) (offset w 12) (n+1) (n-1)++
    shr30 (offset w row) (offset w 11) (n+1)
 def abCode (w n row : Nat) : List Instr :=
  linear (offset w 3+12+8*row) (offset w 3+16+8*row) (offset w 11) (offset w 6) (offset w 7) (offset w 12) n (n-1)++
    VG.Impl.Rsa.X86.InvBatch.reduce w n (offset w (13+row))

 local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega))

 theorem fourRows_ok {s : State} {base : Addr} {size w n p iv cap : Nat} {T : VG.Proof.Divstep.MSt}
    {st : VG.Proof.Divstep.W32.IState}
    (hs : Scr s base size) (hn : 16≤n) (hw : w=2*n) (he : n%2=0) (hz : offset w 15≤size)
    (h : RowInput w n base p iv T st s) (hi : iv<2^32) (hp : 0<p) (hinv : (p*iv+1)%2^32=0)
    (huv : |T.u|+|T.v|≤2^30) (hqr : |T.q|+|T.r|≤2^30)
    (hf : |st.f|≤cap) (hg : |st.g|≤cap) (capBound : cap<2^(32*n+1))
    (divF : 2^30∣T.u*st.f+T.v*st.g) (divG : 2^30∣T.q*st.f+T.r*st.g)
    (ha : |st.a|≤p) (hb : |st.b|≤p) :
    WP isa (.block (fgCode w n 0++fgCode w n 1++abCode w n 0++abCode w n 1)) s fun z =>
      (val32 z.mem base (offset w 0) (n+1) : Int)%2^(32*(n+1))=((T.u*st.f+T.v*st.g)/2^30)%2^(32*(n+1)) ∧
      (val32 z.mem base (offset w 1) (n+1) : Int)%2^(32*(n+1))=((T.q*st.f+T.r*st.g)/2^30)%2^(32*(n+1)) ∧
      (val32 z.mem base (offset w 13) n : Int)=VG.Proof.Divstep.W32.mred p iv (T.u*st.a+T.v*st.b) ∧
      (val32 z.mem base (offset w 14) n : Int)=VG.Proof.Divstep.W32.mred p iv (T.q*st.a+T.r*st.b) ∧
      RowInput w n base p iv T st z ∧ Keeps wordClob s z ∧ Unch base (rowWrites w) s.mem z.mem := by
  have nowrap := hs.nowrap
  rw [List.append_assoc,List.append_assoc]
  refine WP.block_append (WP.mono (fgRow_ok (row:=0) hs hn hw hz (by decide) h.matrix.u h.matrix.v huv
    h.f h.g hf hg capBound divF) fun s₁ ⟨F₁,K₁,O₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  have C₁ := fg_cover hn hw (by decide : 0<2) O₁
  have h₁ := h.keep hs hn hw hz C₁
  refine WP.block_append (WP.mono (fgRow_ok (row:=1) hs₁ hn hw hz (by decide) h₁.matrix.q h₁.matrix.r hqr
    h₁.f h₁.g hf hg capBound divG) fun s₂ ⟨G₂,K₂,O₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  have C₂ := fg_cover hn hw (by decide : 1<2) O₂
  have h₂ := h₁.keep hs₁ hn hw hz C₂
  refine WP.block_append (WP.mono (abRow_ok (row:=0) hs₂ hn hw he hz (by decide) hi h₂.inverse hp h₂.modulus hinv
    h₂.matrix.u h₂.matrix.v huv h₂.a h₂.b ha hb) fun s₃ ⟨A₃,K₃,O₃⟩ => ?_)
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  have C₃ := ab_cover hn hw (by decide : 0<2) O₃
  have h₃ := h₂.keep hs₂ hn hw hz C₃
  refine WP.mono (abRow_ok (row:=1) hs₃ hn hw he hz (by decide) hi h₃.inverse hp h₃.modulus hinv
    h₃.matrix.q h₃.matrix.r hqr h₃.a h₃.b ha hb) fun z ⟨B₄,K₄,O₄⟩ => ?_
  have C₄ := ab_cover hn hw (by decide : 1<2) O₄
  have h₄ := h₃.keep hs₃ hn hw hz C₄
  have pf4 (j k : Nat) (jl : j≤1) (kb : k≤n+1) : val32 z.mem base (offset w j) k=val32 s₃.mem base (offset w j) k := by
    rcases (show j=0 ∨ j=1 by omega) with rfl | rfl
    all_goals
      refine Outs.val32 O₄ ?_ (by apart)
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> apart
  have pf3 (j k : Nat) (jl : j≤1) (kb : k≤n+1) : val32 s₃.mem base (offset w j) k=val32 s₂.mem base (offset w j) k := by
    rcases (show j=0 ∨ j=1 by omega) with rfl | rfl
    all_goals
      refine Outs.val32 O₃ ?_ (by apart)
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> apart
  refine ⟨?_,?_,?_,B₄,h₄,?_,?_⟩
  · rw [pf4 0 (n+1) (by decide) (by omega),pf3 0 (n+1) (by decide) (by omega)]
    rw [Outs.val32 (d:=offset w 0) (k:=n+1) O₂ (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl <;> apart) (by apart)]
    exact F₁
  · rw [pf4 1 (n+1) (by decide) (by omega),pf3 1 (n+1) (by decide) (by omega)]
    exact G₂
  · rw [Outs.val32 (d:=offset w 13) (k:=n) O₄ (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> apart) (by apart)]
    exact A₃
  · exact (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans K₃).trans K₄
  · intro x hx
    exact (C₄ x hx).trans ((C₃ x hx).trans ((C₂ x hx).trans (C₁ x hx)))

end VG.Proof.Rsa.X86.InvBatch
