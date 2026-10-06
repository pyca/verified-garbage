import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareCtRaw
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcFrame

/-! Reduction loops depend only on the public workspace size. -/
namespace VG.Proof.Bignum.X86_64.AdxSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

def RW (L : Ws) (i : Nat) (s : State) : Prop :=
  GW L s ∧ s.gpr .r8 = off L.B (slot L.w aAcc + 16 + 8 * i) ∧
    s.gpr .r9 = off L.B (slot L.w aN) ∧ s.gpr .rbp = BitVec.ofNat 64 L.w

theorem RW.pins {L : Ws} {i : Nat} {s₁ s₂ : State} (h₁ : RW L i s₁) (h₂ : RW L i s₂) :
    ∀ r ∈ [Reg.rdi, .r8, .r9, .rbp], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact pins_gw L s₁ s₂ h₁.1 h₂.1 .rdi (by simp)
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]

theorem redc_row_fw (L : Ws) (j : Nat) (s : State) (hj : j < L.w) (h : RW L j s) :
    WP isa AdxSquare.redcRow s fun t => isa.eval .ne t = some (decide (j + 1 < L.w)) ∧
      (j + 1 < L.w → RW L (j + 1) t) ∧ (j + 1 = L.w → RW L L.w t) := by
  obtain ⟨⟨⟨mi, hg, hZ⟩, hsz⟩, h8, h9, hbp⟩ := h
  have hn := hg.scr.nowrap
  have hA := slot_le (w := L.w) (show aTmp < 8 by decide)
  refine WP.mono (redcRow_frame hg.scr hg.rdi hg.hdr hZ h8 h9 hbp
    (by have := hsz.2.1; omega) hsz.lt (by unfold slot; omega)
    (by unfold slot aAcc aTmp at *; omega) (by unfold slot aN aAcc; omega))
    fun t ⟨ho, h8', hz, k⟩ => ?_
  have gw : GW L t := ⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ho (by unfold slot; omega)⟩, hZ⟩, hsz⟩
  have hw : RW L (j + 1) t := ⟨gw,
    by rw [h8']; congr 1,
    (k.gpr (by decide)).trans h9, (k.gpr (by decide)).trans hbp⟩
  refine ⟨?_, fun _ => hw, fun he => he ▸ hw⟩
  simp only [eval, hz, Option.map_some]
  have he : (slot L.w aAcc + 16 + 8 * j + 8 = slot L.w aTmp) ↔ j + 1 = L.w := by
    unfold slot aAcc aTmp; omega
  simp only [he]
  by_cases hj' : j + 1 = L.w
  · simp [hj']
  · simp [hj']; omega

theorem redc_ct : RelCT isa (Two GW) AdxSquare.redc (Two GW) := by
  unfold AdxSquare.redc
  refine RelCT.seq (two_piece (Ψ := fun L s => 0 < L.w ∧ RW L 0 s) [.rdi] pins_gw
    (by taint_decide) fun L s ⟨⟨mi, hg, hZ⟩, hsz⟩ => ?_) ?_
  · refine WP.mono (redcSetup_ok hg.scr hg.rdi hg.hdr hZ) fun t ⟨h8, h9, hbp, _, hm, k⟩ => ?_
    exact ⟨by have := hsz.2.1; omega,
      ⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩, hsz⟩,
      by simpa only [Nat.mul_zero, Nat.add_zero] using h8, h9, hbp⟩
  refine RelCT.seq (two_loop (fun L => L.w) (Φ := RW) (Ψ := fun L s => RW L L.w s)
    (two_taint [.rdi, .r8, .r9, .rbp] (fun p s₁ s₂ h₁ h₂ => h₁.2.pins h₂.2) (by taint_decide))
    redc_row_fw) ?_
  refine two_piece [.rdi, .r8, .r9, .rbp] (fun L s₁ s₂ h₁ h₂ => h₁.pins h₂) (by taint_decide) ?_
  intro L s h
  obtain ⟨⟨⟨mi, hg, hZ⟩, hsz⟩, h8, _, hbp⟩ := h
  have hA := slot_le (w := L.w) (show aTmp < 8 by decide)
  refine WP.mono (redcFinish_ok hg.scr h8 hbp (by unfold slot aAcc aTmp at *; omega))
    fun t ⟨_, ho, k⟩ => ?_
  exact ⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ho (by unfold slot; omega)⟩, hZ⟩, hsz⟩
end VG.Proof.Bignum.X86_64.AdxSquare
