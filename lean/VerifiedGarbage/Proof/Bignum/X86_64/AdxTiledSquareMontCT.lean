import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRawCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout GoodV pins_goodV)

theorem montSquare_ct {ps : List (Nat × Nat)} {co ca o a : Nat} (po : (co, o) ∈ ps) (pa : (ca, a) ∈ ps)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup ca)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.finishBases co)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) h₄).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledSquare.montSquare co ca) (fun _ _ => True) := by
  unfold AdxTiledSquare.montSquare
  refine RelCT.seq (two_post (raw_ct pa ha ha1 ha2 hS hR hT) (raw_fw pa ha ha1 ha2)) ?_
  refine RelCT.seq AdxTiledProduct.redcV_ct ?_
  refine RelCT.seq (two_piece (Ψ := fun L s => GoodV ps L s ∧ s.gpr .r10=off L.B (slot L.w aN))
    [.rdi] (pins_goodV ps) (by taint_decide) ?_) ?_
  · rintro L s ⟨⟨mi,hg⟩,hv⟩
    have hZ := L.hZ
    have hsrc : readSrc s (.mem (hdr (sArr aN)))=some (off L.B (slot L.w aN)) := by
      rw [readSrc_word (d := 8*sArr aN) hg.scr (by simp only [State.ea,hdr,hg.rdi,hdrOff])
        (by have := hdr_lt_slot L.w 8 (show sArr aN<32 by decide); omega),hg.hdr.harr aN (by decide)]
    exact WP.mono (movMem_ok s (dst := .r10) hsrc) fun _ ⟨p,_,_,k⟩ =>
      ⟨⟨⟨mi,hg.scr.congr k.keep.2.2,(k.keep.gpr (by decide)).trans hg.rdi,k.2.1 ▸ hg.hdr⟩,k.2.1 ▸ hv⟩,p⟩
  unfold Adx.finish
  refine RelCT.seq (two_piece (Ψ := fun L : Layout => FF o ⟨L.B,L.Z,L.w⟩) [.rdi]
    (fun L s t hs ht => pins_goodV ps L s t hs.1 ht.1) hF ?_)
    (two_taint _ (fun L => pins_ff o ⟨L.B,L.Z,L.w⟩) (by taint_decide))
  rintro L s ⟨⟨⟨mi,hg⟩,hv⟩,p⟩
  exact WP.mono (finishBasesV_ok hg.scr hg.rdi hg.hdr L.hZ (hv.at po) (hv.lt po)) fun _ ⟨p12,p8,psi,pbx,_,k⟩ =>
    ⟨p12,p8,psi,pbx,(k.gpr (by decide)).trans p⟩

end VG.Proof.Bignum.X86_64.AdxTiledSquare
