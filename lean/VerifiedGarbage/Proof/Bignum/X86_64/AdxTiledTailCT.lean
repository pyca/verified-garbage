module

public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowCT
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledProduct
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderSave
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailSetup
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCarry8CT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCopy
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Digit
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxCarry8CT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCopy
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Digit
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! The carry-tail branch depends only on the public row number and width. -/

@[expose] public section

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
