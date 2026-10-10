import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMont
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRowRedcCT
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

theorem redc_ct : RelCT isa (Two GoodL) AdxRowRedc.redc (Two GoodL) := by
  apply two_post ?_ ?_
  · refine two_map (fun L : Layout => (⟨⟨L.B,L.Z,L.w⟩,L.n,L.hwN,L.hn⟩ : AdxRotate8.W8)) ?_
      (AdxRowRedc.redc_ct.mono (fun _ _ h => h) (fun _ _ _ => True.intro))
    rintro L s ⟨mi,hg⟩; exact ⟨mi,hg,L.hZ⟩
  · rintro L s ⟨mi,hg⟩
    exact WP.mono (AdxRowRedc.redc_ok hg.scr hg.rdi hg.hdr L.hZ L.hwN L.hn) fun _ ⟨_,o,k⟩ =>
      ⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,hg.hdr.of_outside o (by unfold slot; omega)⟩

/-- `redc_ct`, keeping the operands' slots. -/
theorem redcV_ct {ps : List (Nat × Nat)} : RelCT isa (Two (GoodV ps)) AdxRowRedc.redc (Two (GoodV ps)) := by
  apply two_post ((redc_ct.mono (fun _ _ ⟨L,hs,ht⟩ => ⟨L,hs.1,ht.1⟩) (fun _ _ _ => True.intro)))
  rintro L s ⟨⟨mi,hg⟩,hv⟩
  exact WP.mono (AdxRowRedc.redc_ok hg.scr hg.rdi hg.hdr L.hZ L.hwN L.hn) fun _ ⟨_,o,k⟩ =>
    GoodV.of_outside ⟨⟨mi,hg⟩,hv⟩ o k

/-- `redcV_ct`, for slots and layouts given by any public data `x`. -/
theorem redcV_ct' {α : Type} {P : α → List (Nat × Nat)} {L : α → Layout} :
    RelCT isa (Two fun x s => GoodV (P x) (L x) s) AdxRowRedc.redc (Two fun x s => GoodV (P x) (L x) s) := by
  apply two_post (redc_ct.mono (fun _ _ ⟨x,hs,ht⟩ => ⟨L x,hs.1,ht.1⟩) (fun _ _ _ => True.intro))
  rintro x s ⟨⟨mi,hg⟩,hv⟩
  exact WP.mono (AdxRowRedc.redc_ok hg.scr hg.rdi hg.hdr (L x).hZ (L x).hwN (L x).hn) fun _ ⟨_,o,k⟩ =>
    GoodV.of_outside ⟨⟨mi,hg⟩,hv⟩ o k

/-- `redcFinish`, for slots and layouts given by any public data `x`. -/
theorem redcFinish_ct {α : Type} {P : α → List (Nat × Nat)} {L : α → Layout} {O : α → Nat} {co : Nat}
    (po : ∀ x, (co, O x) ∈ P x) {h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.finishBases co)) h₃).isSome=true) :
    RelCT isa (Two fun x s => GoodV (P x) (L x) s) (AdxTiledProduct.redcFinish co) (fun _ _ => True) := by
  have pins : Pins (fun x s => GoodV (P x) (L x) s) [.rdi] := fun x => pins_goodV (P x) (L x)
  unfold AdxTiledProduct.redcFinish
  refine RelCT.seq redcV_ct' ?_
  refine RelCT.seq (two_piece (Ψ := fun x s => GoodV (P x) (L x) s ∧ s.gpr .r10=off (L x).B (slot (L x).w aN))
    [.rdi] pins (by taint_decide) ?_) ?_
  · rintro x s ⟨⟨mi,hg⟩,hv⟩
    have hZ := (L x).hZ
    have hsrc : readSrc s (.mem (hdr (sArr aN)))=some (off (L x).B (slot (L x).w aN)) := by
      rw [readSrc_word (d := 8*sArr aN) hg.scr (by simp only [State.ea,hdr,hg.rdi,hdrOff])
        (by have := hdr_lt_slot (L x).w 8 (show sArr aN<32 by decide); omega),hg.hdr.harr aN (by decide)]
    exact WP.mono (movMem_ok s (dst := .r10) hsrc) fun _ ⟨p,_,_,k⟩ =>
      ⟨⟨⟨mi,hg.scr.congr k.keep.2.2,(k.keep.gpr (by decide)).trans hg.rdi,k.2.1 ▸ hg.hdr⟩,k.2.1 ▸ hv⟩,p⟩
  unfold Adx.finish8
  refine RelCT.seq (two_piece (Ψ := fun x => FF (O x) ⟨(L x).B,(L x).Z,(L x).w⟩) [.rdi]
    (fun x s t hs ht => pins x s t hs.1 ht.1) hF ?_)
    (two_taint _ (fun x => pins_ff (O x) ⟨(L x).B,(L x).Z,(L x).w⟩) (by taint_decide))
  rintro x s ⟨⟨⟨mi,hg⟩,hv⟩,p⟩
  exact WP.mono (finishBasesV_ok hg.scr hg.rdi hg.hdr (L x).hZ (hv.at (po x)) (hv.lt (po x)))
    fun _ ⟨p12,p8,psi,pbx,_,k⟩ => ⟨p12,p8,psi,pbx,(k.gpr (by decide)).trans p⟩

theorem montMul_ct {ps : List (Nat × Nat)} {co ca cb o a b : Nat} (po : (co, o) ∈ ps) (pa : (ca, a) ∈ ps)
    (pb : (cb, b) ∈ ps) (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup cb)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.finishBases co)) h₃).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledProduct.montMul co ca cb) (fun _ _ => True) :=
  RelCT.seq (two_post (raw_ct pa pb ha hb ha1 ha2 hb1 hb2 hS hR) (raw_fw pa pb ha hb ha1 ha2 hb1 hb2))
    (redcFinish_ct (P := fun _ => ps) (L := id) (O := fun _ => o) (fun _ => po) hF)

end VG.Proof.Bignum.X86_64.AdxTiledProduct
