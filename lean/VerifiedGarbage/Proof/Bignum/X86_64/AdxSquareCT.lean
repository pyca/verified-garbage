import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareCtRedc

/-! Constant time of the complete Montgomery square. -/
namespace VG.Proof.Bignum.X86_64.AdxSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem montSquare_ct {o a : Nat} (ho : o < 8) (ha : a < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup a)) hc₁).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.finishBases o)) hc₂).isSome = true) :
    RelCT isa (Two GW) (AdxSquare.montSquare o a) (fun _ _ => True) := by
  unfold AdxSquare.montSquare
  refine RelCT.seq (two_post (raw_ct ha ha1 ha2 hS) (raw_gw ha ha1 ha2)) ?_
  refine RelCT.seq redc_ct ?_
  refine RelCT.seq (two_piece (Ψ := fun L s => GW L s ∧ s.gpr .r10 = off L.B (slot L.w aN))
    [.rdi] pins_gw (by taint_decide) ?_) ?_
  · intro L s h
    obtain ⟨⟨mi, hg, hZ⟩, hsz⟩ := h
    have hsrc : readSrc s (.mem (hdr (sArr aN))) = some (off L.B (slot L.w aN)) := by
      rw [readSrc_word (d := 8 * sArr aN) hg.scr (by simp only [State.ea, hdr, hg.rdi, hdrOff])
        (by have := hdr_lt_slot L.w 8 (show sArr aN < 32 by decide); omega), hg.hdr.harr aN (by decide)]
    refine WP.mono (movMem_ok s (dst := .r10) hsrc) fun t ⟨h10, _, _, k⟩ => ?_
    exact ⟨⟨⟨mi, ⟨hg.scr.congr k.keep.2.2, (k.keep.gpr (by decide)).trans hg.rdi,
      k.2.1 ▸ hg.hdr⟩, hZ⟩, hsz⟩, h10⟩
  unfold Adx.finish
  refine RelCT.seq (two_piece (Ψ := FF o) [.rdi]
    (fun L s₁ s₂ h₁ h₂ => pins_gw L s₁ s₂ h₁.1 h₂.1) hF ?_)
    (two_taint _ (pins_ff o) (by taint_decide))
  intro L s h
  obtain ⟨⟨⟨mi, hg, hZ⟩, _⟩, h10⟩ := h
  exact WP.mono (finishBases_ok hg.scr hg.rdi hg.hdr hZ ho) fun t ⟨h12, h8, hsi, hbx, _, k⟩ =>
    ⟨h12, h8, hsi, hbx, (k.gpr (by decide)).trans h10⟩
end VG.Proof.Bignum.X86_64.AdxSquare
