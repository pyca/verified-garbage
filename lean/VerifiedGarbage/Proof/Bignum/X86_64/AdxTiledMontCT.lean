import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMont
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem raw_fw {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    (L : Layout) (s : State) (h : GoodV ps L s) :
    WP isa (AdxTiledProduct.rawProduct ca cb) s (GoodV ps L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact WP.mono (rawProduct_ok hg.scr hg.rdi hg.hdr hv pa pb L.hZ L.hw L.hwN L.hn ha hb ha1 ha2 hb1 hb2)
    fun _ ⟨_,_,o,k⟩ => GoodV.of_outside ⟨⟨mi,hg⟩,hv⟩ o k

theorem redc_ct : RelCT isa (Two GoodL) AdxRotate8.redc (Two GoodL) := by
  apply two_post ?_ ?_
  · refine two_map (fun L : Layout => (⟨⟨L.B,L.Z,L.w⟩,L.n,L.hwN,L.hn⟩ : AdxRotate8.W8)) ?_
      (AdxRotate8.redc_ct.mono (fun _ _ h => h) (fun _ _ _ => True.intro))
    rintro L s ⟨mi,hg⟩; exact ⟨mi,hg,L.hZ⟩
  · rintro L s ⟨mi,hg⟩
    exact WP.mono (AdxRotate8.redc_ok hg.scr hg.rdi hg.hdr L.hZ L.hwN L.hn) fun _ ⟨_,o,k⟩ =>
      ⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,hg.hdr.of_outside o (by unfold slot; omega)⟩

/-- `redc_ct`, keeping the operands' slots. -/
theorem redcV_ct {ps : List (Nat × Nat)} : RelCT isa (Two (GoodV ps)) AdxRotate8.redc (Two (GoodV ps)) := by
  apply two_post ((redc_ct.mono (fun _ _ ⟨L,hs,ht⟩ => ⟨L,hs.1,ht.1⟩) (fun _ _ _ => True.intro)))
  rintro L s ⟨⟨mi,hg⟩,hv⟩
  exact WP.mono (AdxRotate8.redc_ok hg.scr hg.rdi hg.hdr L.hZ L.hwN L.hn) fun _ ⟨_,o,k⟩ =>
    GoodV.of_outside ⟨⟨mi,hg⟩,hv⟩ o k

theorem montMul_ct {ps : List (Nat × Nat)} {co ca cb o a b : Nat} (po : (co, o) ∈ ps) (pa : (ca, a) ∈ ps)
    (pb : (cb, b) ∈ ps) (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup cb)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.finishBases co)) h₃).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledProduct.montMul co ca cb) (fun _ _ => True) := by
  unfold AdxTiledProduct.montMul
  refine RelCT.seq (two_post (raw_ct pa pb ha hb ha1 ha2 hb1 hb2 hS hR) (raw_fw pa pb ha hb ha1 ha2 hb1 hb2)) ?_
  refine RelCT.seq redcV_ct ?_
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

end VG.Proof.Bignum.X86_64.AdxTiledProduct
