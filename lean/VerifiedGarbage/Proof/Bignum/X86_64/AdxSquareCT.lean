module
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRaw
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcFrame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcChoice
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Edges
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRaw
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcFrame
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcChoice
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Edges
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcRow

/-! ## AdxSquareCtRaw -/

@[expose] public section

section

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
    unfold slot aAcc aTmp at *; omega_arith
  refine WP.mono (cross_ok hg.scr h8 h9 hbx (by have := hsz.2.1; omega_arith) (by omega_arith)
    (by unfold slot aAcc aTmp at *; omega_arith) (by omega_arith) sb) fun t ⟨_, ho, _, k⟩ => ?_
  exact ⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ho (by unfold slot; omega_arith)⟩, hZ⟩, hsz⟩

theorem rawWith_ct {diag : Prog isa} {a : Nat} (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    {hc hd : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup a)) hc).isSome = true)
    (hD : (taint.check (Taint.ofRegs [.rdi, .r8, .r9, .rbx])
      (.seq (.block [.mov .r10 (.reg .rbx)]) diag) hd).isSome = true) :
    RelCT isa (Two GW) (AdxSquare.rawSquareWith diag a) (fun _ _ => True) := by
  unfold AdxSquare.rawSquareWith
  refine RelCT.seq (two_piece [.rdi] pins_gw hS (setup_ready ha)) ?_
  refine RelCT.seq (two_piece [.rdi, .r8, .r9, .rbx] (pins_ready a) (by taint_decide) (cross_gw ha ha1 ha2)) ?_
  refine RelCT.seq (two_piece [.rdi] pins_gw hS (setup_ready ha)) ?_
  exact two_taint [.rdi, .r8, .r9, .rbx] (pins_ready a) hD

theorem rawWith_gw {diag : Prog isa} {P : Nat → Prop} (hd : DiagOk diag P) (hP : ∀ w, SizeOk w → P w)
    {a : Nat} (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (L : Ws) (s : State) (h : GW L s) : WP isa (AdxSquare.rawSquareWith diag a) s (GW L) := by
  obtain ⟨⟨mi, hg, hZ⟩, hsz⟩ := h
  refine WP.mono (rawSquareWith_ok hd hg.scr hg.rdi hg.hdr hZ (by have := hsz.2.1; omega_arith) hsz.lt
    (hP _ hsz) ha ha1 ha2) fun t ⟨_, _, ho, k⟩ => ?_
  exact ⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ho (by unfold slot; omega_arith)⟩, hZ⟩, hsz⟩

end VG.Proof.Bignum.X86_64.AdxSquare

end

/-! ## AdxSquareCtRedc -/
section

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
    (by have := hsz.2.1; omega_arith) hsz.lt (by unfold slot; omega_arith)
    (by unfold slot aAcc aTmp at *; omega_arith) (by unfold slot aN aAcc; omega_arith))
    fun t ⟨ho, h8', hz, k⟩ => ?_
  have gw : GW L t := ⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ho (by unfold slot; omega_arith)⟩, hZ⟩, hsz⟩
  have hw : RW L (j + 1) t := ⟨gw,
    by rw [h8']; congr 1,
    (k.gpr (by decide)).trans h9, (k.gpr (by decide)).trans hbp⟩
  refine ⟨?_, fun _ => hw, fun he => he ▸ hw⟩
  simp only [eval, hz, Option.map_some]
  have he : (slot L.w aAcc + 16 + 8 * j + 8 = slot L.w aTmp) ↔ j + 1 = L.w := by
    unfold slot aAcc aTmp; omega_arith
  simp only [he]
  by_cases hj' : j + 1 = L.w
  · simp [hj']
  · simp [hj']; omega_arith

theorem redc_ct : RelCT isa (Two GW) AdxSquare.redc (Two GW) := by
  unfold AdxSquare.redc
  refine RelCT.seq (two_piece (Ψ := fun L s => 0 < L.w ∧ RW L 0 s) [.rdi] pins_gw
    (by taint_decide) fun L s ⟨⟨mi, hg, hZ⟩, hsz⟩ => ?_) ?_
  · refine WP.mono (redcSetup_ok hg.scr hg.rdi hg.hdr hZ) fun t ⟨h8, h9, hbp, _, hm, k⟩ => ?_
    exact ⟨by have := hsz.2.1; omega_arith,
      ⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩, hsz⟩,
      by simpa only [Nat.mul_zero, Nat.add_zero] using h8, h9, hbp⟩
  refine RelCT.seq (two_loop (fun L => L.w) (Φ := RW) (Ψ := fun L s => RW L L.w s)
    (two_taint [.rdi, .r8, .r9, .rbp] (fun p s₁ s₂ h₁ h₂ => h₁.2.pins h₂.2) (by taint_decide))
    redc_row_fw) ?_
  refine two_piece [.rdi, .r8, .r9, .rbp] (fun L s₁ s₂ h₁ h₂ => h₁.pins h₂) (by taint_decide) ?_
  intro L s h
  obtain ⟨⟨⟨mi, hg, hZ⟩, hsz⟩, h8, _, hbp⟩ := h
  have hA := slot_le (w := L.w) (show aTmp < 8 by decide)
  refine WP.mono (redcFinish_ok hg.scr h8 hbp (by unfold slot aAcc aTmp at *; omega_arith))
    fun t ⟨_, ho, k⟩ => ?_
  exact ⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ho (by unfold slot; omega_arith)⟩, hZ⟩, hsz⟩
end VG.Proof.Bignum.X86_64.AdxSquare

end

/-! ## AdxSquareCtChoice -/
section

/-! Reduction dispatch depends only on the public word count. -/
namespace VG.Proof.Bignum.X86_64.AdxSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem rotate_gw_ct : RelCT isa (Two fun L s => GW L s ∧ L.w % 8 = 0)
    AdxRotate8.redc (Two GW) := by
  intro s t ts tt s' t' h es et
  obtain ⟨L, ⟨hs, h8⟩, ⟨ht, _⟩⟩ := h
  have hn : 0 < L.w / 8 := by have := hs.2.2.1; omega_arith
  let W : AdxRotate8.W8 := ⟨L, L.w / 8, by omega_arith, hn⟩
  obtain ⟨he, ⟨_, _, _⟩⟩ := AdxRotate8.redc_ct _ _ _ _ _ _ ⟨W, hs.1, ht.1⟩ es et
  have fw : ∀ u, GW L u → WP isa AdxRotate8.redc u (GW L) := by
    intro u ⟨⟨mi, hg, hZ⟩, hsz⟩
    refine WP.mono (AdxRotate8.redc_ok hg.scr hg.rdi hg.hdr hZ W.hw W.hn) fun v ⟨_, ot, kt⟩ => ?_
    exact ⟨⟨mi, ⟨hg.scr.congr kt.2.2, (kt.gpr (by decide)).trans hg.rdi,
      hg.hdr.of_outside ot (by unfold slot; omega_arith)⟩, hZ⟩, hsz⟩
  obtain ⟨_, _, e1, h1⟩ := fw s hs
  obtain ⟨_, _, e2, h2⟩ := fw t ht
  obtain ⟨_, rfl⟩ := Exec.det es e1
  obtain ⟨_, rfl⟩ := Exec.det et e2
  exact ⟨he, L, h1, h2⟩

theorem redcChoice_ct : RelCT isa (Two GW) AdxSquare.redcChoice (Two GW) := by
  unfold AdxSquare.redcChoice
  refine RelCT.seq (two_piece (Ψ := fun L s => GW L s ∧ s.zf = some (decide (L.w % 8 = 0)))
    [.rdi] pins_gw (by taint_decide) ?_) ?_
  · intro L s ⟨⟨mi, hg, hZ⟩, hsz⟩
    refine WP.mono (redcTest_ok hg.scr hg.rdi hg.hdr hZ (by have := hsz.lt; omega_arith))
      fun t ⟨hz, hm, kt⟩ => ?_
    exact ⟨⟨⟨mi, ⟨hg.scr.congr kt.2.2, (kt.gpr (by decide)).trans hg.rdi,
      hm ▸ hg.hdr⟩, hZ⟩, hsz⟩, hz⟩
  refine two_ite (fun L s t hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
  · refine two_map id (fun L s ⟨⟨h, hz⟩, he⟩ => ⟨h, ?_⟩) rotate_gw_ct
    simp only [eval, hz, Option.some.injEq, decide_eq_true_eq] at he
    exact he
  · exact two_map id (fun L s h => h.1.1) redc_ct
end VG.Proof.Bignum.X86_64.AdxSquare

end

/-! ## AdxSquareCT -/
section

/-! Constant time of the complete Montgomery square. -/
namespace VG.Proof.Bignum.X86_64.AdxSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem montSquareWith_ct {diag red : Prog isa} {o a : Nat} (ho : o < 8)
    (hraw : RelCT isa (Two GW) (AdxSquare.rawSquareWith diag a) (fun _ _ => True))
    (hgw : ∀ L s, GW L s → WP isa (AdxSquare.rawSquareWith diag a) s (GW L))
    (hred : RelCT isa (Two GW) red (Two GW))
    {hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.finishBases o)) hc₂).isSome = true) :
    RelCT isa (Two GW) (AdxSquare.montSquareWith diag red o a) (fun _ _ => True) := by
  unfold AdxSquare.montSquareWith
  refine RelCT.seq (two_post hraw hgw) ?_
  refine RelCT.seq hred ?_
  refine RelCT.seq (two_piece (Ψ := fun L s => GW L s ∧ s.gpr .r10 = off L.B (slot L.w aN))
    [.rdi] pins_gw (by taint_decide) ?_) ?_
  · intro L s h
    obtain ⟨⟨mi, hg, hZ⟩, hsz⟩ := h
    have hsrc : readSrc s (.mem (hdr (sArr aN))) = some (off L.B (slot L.w aN)) := by
      rw [readSrc_word (d := 8 * sArr aN) hg.scr (by simp only [State.ea, hdr, hg.rdi, hdrOff])
        (by have := hdr_lt_slot L.w 8 (show sArr aN < 32 by decide); omega_arith), hg.hdr.harr aN (by decide)]
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

theorem montSquare_ct {o a : Nat} (ho : o < 8) (ha : a < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup a)) hc₁).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.finishBases o)) hc₂).isSome = true) :
    RelCT isa (Two GW) (AdxSquare.montSquare o a) (fun _ _ => True) :=
  montSquareWith_ct ho (rawWith_ct ha ha1 ha2 hS (by taint_decide))
    (rawWith_gw diagonalChoice_diag (fun _ _ => trivial) ha ha1 ha2) redcChoice_ct hF

theorem montSquare4_ct {o a : Nat} (ho : o < 8) (ha : a < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup a)) hc₁).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.finishBases o)) hc₂).isSome = true) :
    RelCT isa (Two GW) (AdxSquare.montSquare4 o a) (fun _ _ => True) :=
  montSquareWith_ct ho (rawWith_ct ha ha1 ha2 hS (by taint_decide))
    (rawWith_gw diagonal4_diag (fun _ h => h.1) ha ha1 ha2) redc_ct hF
end VG.Proof.Bignum.X86_64.AdxSquare

end