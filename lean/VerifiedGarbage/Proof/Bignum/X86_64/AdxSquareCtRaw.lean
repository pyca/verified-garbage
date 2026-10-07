import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareMont
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT

/-! Constant-time composition of the raw square's header loads and loops. -/

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

def GW (L : Ws) (s : State) : Prop := GoodW L s ∧ SizeOk L.w

def Ready (a : Nat) (L : Ws) (s : State) : Prop :=
  GW L s ∧ s.gpr .r8 = off L.B (slot L.w aAcc + 16) ∧
    s.gpr .r9 = off L.B (slot L.w a) ∧ s.gpr .rbx = BitVec.ofNat 64 L.w

theorem pins_gw : Pins GW [.rdi] := fun L s₁ s₂ h₁ h₂ => pins_goodW L s₁ s₂ h₁.1 h₂.1

theorem pins_ready (a : Nat) : Pins (Ready a) [.rdi, .r8, .r9, .rbx] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact pins_gw L s₁ s₂ h₁.1 h₂.1 .rdi (by simp)
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]

theorem setup_ready {a : Nat} (ha : a < 8) (L : Ws) (s : State) (h : GW L s) :
    WP isa (.block (Adx.setup a)) s (Ready a L) := by
  obtain ⟨⟨mi, hg, hZ⟩, hsz⟩ := h
  refine WP.mono (adxSetup_ok hg.scr hg.rdi hg.hdr hZ ha) fun t ⟨h9, _, h8, hbx, hm, k⟩ => ?_
  exact ⟨⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩, hsz⟩,
    h8, h9, hbx⟩

theorem cross_gw {a : Nat} (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (L : Ws) (s : State) (h : Ready a L s) : WP isa AdxSquare.cross s (GW L) := by
  obtain ⟨⟨⟨mi, hg, hZ⟩, hsz⟩, h8, h9, hbx⟩ := h
  have hn := hg.scr.nowrap
  have hw := hsz.lt
  have hA := slot_le (w := L.w) (show aTmp < 8 by decide)
  have hb := slot_le (w := L.w) ha
  have sb : slot L.w a + 8 * L.w ≤ slot L.w aAcc + 16 ∨
      slot L.w aAcc + 16 + 8 * (2 * L.w + 2) ≤ slot L.w a := by
    have := slot_sep (w := L.w) ha1; have := slot_sep (w := L.w) ha2
    unfold slot aAcc aTmp at *; omega
  refine WP.mono (cross_ok hg.scr h8 h9 hbx (by have := hsz.2.1; omega) (by omega)
    (by unfold slot aAcc aTmp at *; omega) (by omega) sb) fun t ⟨_, ho, _, k⟩ => ?_
  exact ⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ho (by unfold slot; omega)⟩, hZ⟩, hsz⟩

theorem raw_ct {a : Nat} (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup a)) hc).isSome = true) :
    RelCT isa (Two GW) (AdxSquare.rawSquare a) (fun _ _ => True) := by
  unfold AdxSquare.rawSquare
  refine RelCT.seq (two_piece [.rdi] pins_gw hS (setup_ready ha)) ?_
  refine RelCT.seq (two_piece [.rdi, .r8, .r9, .rbx] (pins_ready a) (by taint_decide) (cross_gw ha ha1 ha2)) ?_
  refine RelCT.seq (two_piece [.rdi] pins_gw hS (setup_ready ha)) ?_
  exact two_taint [.rdi, .r8, .r9, .rbx] (pins_ready a) (by taint_decide)

theorem raw_gw {a : Nat} (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (L : Ws) (s : State) (h : GW L s) : WP isa (AdxSquare.rawSquare a) s (GW L) := by
  obtain ⟨⟨mi, hg, hZ⟩, hsz⟩ := h
  refine WP.mono (rawSquare_ok hg.scr hg.rdi hg.hdr hZ (by have := hsz.2.1; omega) hsz.lt ha ha1 ha2)
    fun t ⟨_, _, ho, k⟩ => ?_
  exact ⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ho (by unfold slot; omega)⟩, hZ⟩, hsz⟩

end VG.Proof.Bignum.X86_64.AdxSquare
