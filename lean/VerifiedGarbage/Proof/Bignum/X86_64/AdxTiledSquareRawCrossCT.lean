import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsChoiceCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8BlocksCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout pins_good setup_fw zero_fw save_fw)

theorem rawCross_ct {a : Nat} (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup a)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a a)) h₂).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup a)) h₃).isSome=true) :
    RelCT isa (Two AdxTiledProduct.GoodL) (AdxTiledSquare.rawCross a) (fun _ _ => True) := by
  unfold AdxTiledSquare.rawCross
  refine RelCT.seq (two_piece [.rdi] AdxTiledProduct.pins_good hS (setup_fw ha)) ?_
  refine RelCT.seq (two_piece [.r8,.rbx] ?_ (by taint_decide) zero_fw) ?_
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.2.2.trans ht.2.2.symm
  have mapGood : ∀ L s, AdxTiledProduct.GoodL L s → GoodW ⟨L.B,L.Z,L.w⟩ s := by
    rintro L s ⟨mi,hg⟩; exact ⟨mi,hg,L.hZ⟩
  refine RelCT.seq (two_post (two_map (fun L : Layout => (⟨L.B,L.Z,L.w⟩ : Ws)) mapGood AdxHeader.save_ct) save_fw) ?_
  exact RelCT.seq (RelCT.seq (AdxTri8.blocks_ct ha ha1 ha2 hT) (rowsChoice_ct ha ha1 ha2 hR))
    (two_map (fun L : Layout => (⟨L.B,L.Z,L.w⟩ : Ws)) mapGood AdxHeader.restore_ct)

end VG.Proof.Bignum.X86_64.AdxTiledSquare
