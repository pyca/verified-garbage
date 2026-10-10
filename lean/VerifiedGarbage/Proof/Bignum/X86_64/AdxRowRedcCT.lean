import VerifiedGarbage.Proof.Bignum.X86_64.AdxRowRedc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT

/-!
# Constant time of the row reduction

`AdxRowRedc.redc` leaks the same in runs with the same working space
(`redc_ct`, `AdxRotate8.redc_ct`'s statement): the rows' count is `w`, and a
row's addresses and its blocks' count depend only on the window's and the
modulus's addresses and on `w` (`r8`, `r9`, `rbp`), which correctness pins
(`RW`); the taint check covers the rest.
-/

namespace VG.Proof.Bignum.X86_64.AdxRowRedc

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8 (W8)

/-- Before row `i`: the window's, the modulus's addresses and `w`. -/
def RW (L : W8) (i : Nat) (s : State) : Prop :=
  GoodW L.ws s ∧ s.gpr .r8 = off L.ws.B (slot L.ws.w aAcc + 16 + 8 * i) ∧
    s.gpr .r9 = off L.ws.B (slot L.ws.w aN) ∧ s.gpr .rbp = BitVec.ofNat 64 L.ws.w

theorem RW.pins {L : W8} {i : Nat} {s₁ s₂ : State} (h₁ : RW L i s₁) (h₂ : RW L i s₂) :
    ∀ r ∈ [Reg.rdi, .r8, .r9, .rbp], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact pins_goodW L.ws s₁ s₂ h₁.1 h₂.1 .rdi (by simp)
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]

theorem row_fw (L : W8) (j : Nat) (s : State) (hj : j < L.ws.w) (h : RW L j s) :
    WP isa AdxRowRedc.redcRow s fun t => isa.eval .ne t = some (decide (j + 1 < L.ws.w)) ∧
      (j + 1 < L.ws.w → RW L (j + 1) t) ∧ (j + 1 = L.ws.w → RW L L.ws.w t) := by
  obtain ⟨⟨mi, hg, hZ⟩, h8, h9, hbp⟩ := h
  have hn := hg.scr.nowrap
  have hA := slot_le (w := L.ws.w) (show aTmp < 8 by decide)
  have hw := L.hw
  have hw58 : L.ws.w < 2 ^ 58 := by
    have h8Z : slot L.ws.w 8 ≤ 2 ^ 64 := by omega
    unfold slot at h8Z; omega
  refine WP.mono (redcRow_ok (n := 2 * L.ws.w - j) hg.scr hg.rdi hg.hdr hZ h8 h9 hbp
    (by have := L.hn; omega) (by omega) hw58 (by omega) (by unfold slot; omega)
    (by unfold slot aAcc aTmp at *; omega) (by unfold slot aN aAcc; omega))
    fun t ⟨_, _, _, ho, h8', hz, k⟩ => ?_
  have gw : GoodW L.ws t := ⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ho (by unfold slot; omega)⟩, hZ⟩
  have hw' : RW L (j + 1) t := ⟨gw, by rw [h8']; congr 1, (k.gpr (by decide)).trans h9,
    (k.gpr (by decide)).trans hbp⟩
  refine ⟨?_, fun _ => hw', fun he => he ▸ hw'⟩
  simp only [eval, hz, Option.map_some]
  have he : (slot L.ws.w aAcc + 16 + 8 * j + 8 = slot L.ws.w aTmp) ↔ j + 1 = L.ws.w := by
    unfold slot aAcc aTmp; omega
  simp only [he]
  by_cases hj' : j + 1 = L.ws.w
  · simp [hj']
  · simp [hj']; omega

theorem redc_ct : RelCT isa (Two fun L : W8 => GoodW L.ws) AdxRowRedc.redc
    (Two fun L : W8 => GoodW L.ws) := by
  unfold AdxRowRedc.redc
  refine RelCT.seq (two_piece (Ψ := fun L s => 0 < L.ws.w ∧ RW L 0 s) [.rdi]
    (fun L => pins_goodW L.ws) (by taint_decide) fun L s ⟨mi, hg, hZ⟩ => ?_) ?_
  · refine WP.mono (AdxSquare.redcSetup_ok hg.scr hg.rdi hg.hdr hZ) fun t ⟨h8, h9, hbp, _, hm, k⟩ => ?_
    exact ⟨by have := L.hw; have := L.hn; omega,
      ⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩,
      by simpa only [Nat.mul_zero, Nat.add_zero] using h8, h9, hbp⟩
  refine RelCT.seq (two_loop (fun L : W8 => L.ws.w) (Φ := RW) (Ψ := fun L s => RW L L.ws.w s)
    (two_taint [.rdi, .r8, .r9, .rbp] (fun p s₁ s₂ h₁ h₂ => h₁.2.pins h₂.2) (by taint_decide))
    row_fw) ?_
  refine two_piece [.rdi, .r8, .r9, .rbp] (fun L s₁ s₂ h₁ h₂ => h₁.pins h₂) (by taint_decide) ?_
  intro L s h
  obtain ⟨⟨mi, hg, hZ⟩, h8, _, hbp⟩ := h
  have hA := slot_le (w := L.ws.w) (show aTmp < 8 by decide)
  refine WP.mono (AdxSquare.redcFinish_ok hg.scr h8 hbp (by unfold slot aAcc aTmp at *; omega))
    fun t ⟨_, ho, k⟩ => ?_
  exact ⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ho (by unfold slot; omega)⟩, hZ⟩

end VG.Proof.Bignum.X86_64.AdxRowRedc
