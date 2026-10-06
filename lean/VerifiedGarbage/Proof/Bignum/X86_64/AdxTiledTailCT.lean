import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCarry8CT

/-! The carry-tail branch depends only on the public row number and width. -/
namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRect8 (RowLayout rawBase)
open VG.Proof.Bignum.X86_64.AdxHeader (highPad)

def TailReady (L : RowLayout) (s : State) : Prop :=
  (∃ mi, Good s L.B L.Z L.w mi) ∧
    word s.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.i ∧
    s.gpr .rsi=off L.B (rawBase L.w+8*(L.i+L.w))

def TailTested (L : RowLayout) (s : State) : Prop :=
  TailReady L s ∧ s.zf=some (decide (L.i+8=L.w))

def TailBases (L : RowLayout) (s : State) : Prop :=
  s.gpr .rsi=off L.B (rawBase L.w+8*(L.i+L.w+8)) ∧ s.gpr .rdx=off L.B (highPad L.w)

theorem tail_ct : RelCT isa (Two TailReady) AdxTiledProduct.tail (fun _ _ => True) := by
  unfold AdxTiledProduct.tail
  refine RelCT.seq (two_piece (Ψ := TailTested) [.rdi] ?_ (by taint_decide) ?_) ?_
  · rintro L s t ⟨⟨mi,hs⟩,_,_⟩ ⟨⟨mj,ht⟩,_,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  · rintro L s ⟨⟨mi,hg⟩,idx,ptr⟩
    refine WP.mono (tailTest_ok hg.scr hg.rdi hg.hdr L.hZ L.hw L.hi idx) fun t ⟨zt,mt,kt⟩ => ?_
    exact ⟨⟨⟨mi,hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,
      mt ▸ idx,(kt.gpr (by decide)).trans ptr⟩,zt⟩
  apply two_ite (Φ := TailTested)
  · intro L s t hs ht
    simp only [eval,hs.2,ht.2]
  · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
  · refine RelCT.seq (two_piece (Ψ := TailBases) [.rdi,.rsi] ?_ (by taint_decide) ?_)
      (two_taint [.rsi,.rdx] ?_ (by taint_decide))
    · rintro L s t ⟨⟨⟨⟨mi,hs⟩,_,ps⟩,_⟩,_⟩ ⟨⟨⟨⟨mj,ht⟩,_,pt⟩,_⟩,_⟩ r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.rdi.trans ht.rdi.symm
      · exact ps.trans pt.symm
    · rintro L s ⟨⟨⟨⟨mi,hg⟩,_,ptr⟩,_⟩,_⟩
      exact WP.mono (tailSetup_ok hg.scr hg.rdi hg.hdr L.hZ ptr) fun _ ⟨_,p,e,_,_,_⟩ => ⟨p,e⟩
    · intro L s t hs ht r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.trans ht.2.symm

end VG.Proof.Bignum.X86_64.AdxTiledProduct
