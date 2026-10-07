import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareChoice

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout)

theorem rowsChoice_ct {a : Nat} (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a a)) hint).isSome=true) :
    RelCT isa (Two AdxTiledProduct.GoodL) (AdxTiledSquare.rowsChoice a) (Two AdxTiledProduct.GoodL) := by
  unfold AdxTiledSquare.rowsChoice
  refine RelCT.seq (two_piece (Ψ := fun L s => AdxTiledProduct.GoodL L s ∧ s.zf=some (decide (L.w=8)))
    [.rdi] ?_ (by taint_decide) ?_) ?_
  · rintro L s t ⟨mi,hs⟩ ⟨mj,ht⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  · rintro L s ⟨mi,hg⟩
    exact WP.mono (rowsTest_ok hg.scr hg.rdi hg.hdr L.hZ L.hw) fun t ⟨zt,mt,kt⟩ =>
      ⟨⟨mi,hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,zt⟩
  refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
  · exact RelCT.block_nil fun _ _ h => two_mono (fun _ _ h => h.1.1) h
  · refine two_map id (fun L s ⟨⟨hg,z⟩,e⟩ => ⟨?_,hg⟩) (rows_ct ha ha1 ha2 hS)
    simp only [eval,z,Option.some.injEq,decide_eq_false_iff_not] at e
    have wn := L.hwN; have hn := L.hn
    change 1<L.n
    omega

end VG.Proof.Bignum.X86_64.AdxTiledSquare
