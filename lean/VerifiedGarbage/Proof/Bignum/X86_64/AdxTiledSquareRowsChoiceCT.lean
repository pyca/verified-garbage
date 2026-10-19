module
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledSquare
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRowsCT

import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareChoice
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledSquare
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRowsCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareChoice
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout GoodV)

theorem rowsChoice_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) hint).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledSquare.rowsChoice ca) (Two (GoodV ps)) := by
  unfold AdxTiledSquare.rowsChoice
  refine RelCT.seq (two_piece (Ψ := fun L s => GoodV ps L s ∧ s.zf=some (decide (L.w=8)))
    [.rdi] ?_ (by taint_decide) ?_) ?_
  · rintro L s t ⟨⟨mi,hs⟩,_⟩ ⟨⟨mj,ht⟩,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  · rintro L s ⟨⟨mi,hg⟩,hv⟩
    exact WP.mono (rowsTest_ok hg.scr hg.rdi hg.hdr L.hZ L.hw) fun t ⟨zt,mt,kt⟩ =>
      ⟨⟨⟨mi,hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,mt ▸ hv⟩,zt⟩
  refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
  · exact RelCT.block_nil fun _ _ h => two_mono (fun _ _ h => h.1.1) h
  · refine RelCT.seq (two_piece (Φ := fun L s => (GoodV ps L s ∧ s.zf=some (decide (L.w=8))) ∧
        isa.eval .e s=some false)
      (Ψ := fun L s => StartGood ps L s ∧ s.zf=some (decide (L.w=16)))
      [.rdi] ?_ (by taint_decide) ?_) ?_
    · rintro L s t ⟨⟨⟨⟨mi,hs⟩,_⟩,_⟩,_⟩ ⟨⟨⟨⟨mj,ht⟩,_⟩,_⟩,_⟩ r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      subst r; exact hs.rdi.trans ht.rdi.symm
    · rintro L s ⟨⟨⟨⟨mi,hg⟩,hv⟩,z⟩,e⟩
      simp only [eval,z,Option.some.injEq,decide_eq_false_iff_not] at e
      have wn := L.hwN; have hn := L.hn
      exact WP.mono (rowsTest16_ok hg.scr hg.rdi hg.hdr L.hZ L.hw) fun t ⟨zt,mt,kt⟩ =>
        ⟨⟨by change 1<L.n; omega,
          ⟨mi,hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,mt ▸ hv⟩,zt⟩
    refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
    · exact two_map id (fun L s ⟨⟨hg,_⟩,_⟩ => hg) (rows1_ct pa ha ha1 ha2 hS)
    · exact two_map id (fun L s ⟨⟨hg,_⟩,_⟩ => hg) (rows_ct pa ha ha1 ha2 hS)

end VG.Proof.Bignum.X86_64.AdxTiledSquare
