import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8BlockCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRowsCT

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout LoopState GoodV)

def AtBlock (ps : List (Nat × Nat)) (p : Layout × Nat) (s : State) : Prop := p.2<p.1.n ∧ LoopState ps p.1 p.2 s

theorem block_loop_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp) (p : Layout × Nat) (s : State) (h : AtBlock ps p s) :
    WP isa (AdxTri8.block ca) s (AtBlock ps p) := by
  obtain ⟨hk,mi,hg,hv,hI⟩ := h
  have wn := p.1.hwN
  refine WP.mono (block_ok hg.scr hg.rdi hg.hdr p.1.hZ hv pa ha ha1 ha2 (by omega) hI)
    fun t ⟨_,ot,kt⟩ => ?_
  refine ⟨hk,mi,⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ot (by unfold output slot; omega)⟩,
    hv.of_outside ot (by unfold output slot sFn hdrBytes; omega),?_⟩
  rw [ot.word (by unfold output slot hdrBytes sFn; omega) (by decide)]; exact hI

theorem block_loop_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) hint).isSome=true) :
    RelCT isa (Two (AtBlock ps)) (AdxTri8.block ca) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨⟨L,k⟩,⟨hk,mi,gs,vs,is⟩,⟨_,mj,gt,vt,it⟩⟩ es et
  dsimp only at hk
  have wn := L.hwN
  have sa := slot_le (w := L.w) ha
  have hi : 8*k+8≤L.w := by omega
  have hZ := L.hZ
  let C : CtLayout := ⟨L.B,L.Z,L.w,8*k,slot L.w a+8*(8*k),L.hZ,hi,by omega⟩
  exact block_ct pa hS s t ts tt s' t' ⟨C,⟨⟨mi,gs,is⟩,vs,rfl⟩,⟨⟨mj,gt,it⟩,vt,rfl⟩⟩ es et

theorem step_loop_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) hint).isSome=true) :
    RelCT isa (Two (AtBlock ps)) (.seq (AdxTri8.block ca) (.block AdxTri8.nextBlock)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (block_loop_ct pa ha hS) (block_loop_fw pa ha ha1 ha2))
    (two_taint [.rdi] ?_ (by taint_decide))
  rintro p s t ⟨_,mi,hs,_⟩ ⟨_,mj,ht,_⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

theorem step_loop_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp) (L : Layout) (k : Nat) (s : State) (hk : k<L.n) (h : LoopState ps L k s) :
    WP isa (.seq (AdxTri8.block ca) (.block AdxTri8.nextBlock)) s fun t =>
      isa.eval .ne t=some (decide (k+1<L.n)) ∧
      (k+1<L.n → LoopState ps L (k+1) t) ∧ (k+1=L.n → GoodV ps L t) := by
  refine WP.seq (WP.mono (block_loop_fw pa ha ha1 ha2 (L,k) s ⟨hk,h⟩) fun u ⟨_,mi,hg,hv,hI⟩ => ?_)
  dsimp only at hg hI
  have wn := L.hwN
  have hw := L.hw
  have nowrap := hg.scr.nowrap
  refine WP.mono (AdxTiledProduct.nextRow_ok hg.scr hg.rdi hg.hdr L.hZ (by omega) (by omega) hI)
    fun t ⟨mt,zt,kt⟩ => ?_
  have ot : Outside L.B (8*sFn 12) 8 u.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by decide)
  have ft : Frm L.B (AdxTiledProduct.ranges L.w) u.mem t.mem := by
    intro x hx
    apply ot x
    have := hx (8*sFn 12,32) (by simp [AdxTiledProduct.ranges]); omega
  have gt : Good t L.B L.Z L.w mi :=
    ⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,AdxTiledProduct.frame_hdr hg.hdr ft⟩
  have vt := AdxTiledProduct.frame_ops hv ft
  refine ⟨?_,fun _ => ⟨mi,gt,vt,?_⟩,fun _ => ⟨⟨mi,gt⟩,vt⟩⟩
  · simp only [eval,zt,Option.map_some]
    by_cases he : k+1=L.n
    · simp only [show 8*k+8=L.w by omega,decide_true,Bool.not_true,show ¬(k+1<L.n) by omega,decide_false]
    · simp only [show ¬(8*k+8=L.w) by omega,decide_false,Bool.not_false,show k+1<L.n by omega,decide_true]
  · rw [mt,word_writeW_self,show 8*(k+1)=8*k+8 by omega]

theorem blocks_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) hint).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTri8.blocks ca) (Two (GoodV ps)) := by
  unfold AdxTri8.blocks
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) AdxTiledProduct.rows_init_fw)
    (two_loop (fun L : Layout => L.n) (step_loop_ct pa ha ha1 ha2 hS) (step_loop_fw pa ha ha1 ha2))
  rintro L s t ⟨⟨mi,hs⟩,_⟩ ⟨⟨mj,ht⟩,_⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

end VG.Proof.Bignum.X86_64.AdxTri8
