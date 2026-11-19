module

import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRaw
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledSquareDispatch
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMont
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRaw
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
meta import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledSquareDispatch
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMont
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareChoice
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledSquare
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareChoice
meta import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledSquare
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Row
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledProduct
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcChoice
meta import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledProduct
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcChoice
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRaw
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRaw
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcRow
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquare
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow
meta import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquare
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Bignum.X86_64.Words
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow

/-! ### `Bignum.X86_64.AdxTiledChoiceCT`, which only this module used -/

section

/-! ### `Bignum.X86_64.AdxSquareCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxSquareRedcFrame`, which only this module used -/

section

/-! The reduction row's memory and public-control behavior, even when the
header's inverse does not match the modulus. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem redcRow_frame {s : State} {B : Addr} {Z e w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (h8 : s.gpr .r8 = off B e)
    (h9 : s.gpr .r9 = off B (slot w aN)) (hbp : s.gpr .rbp = BitVec.ofNat 64 w)
    (hw1 : 2 ≤ w) (hw : w < 2 ^ 31) (he : hdrBytes ≤ e)
    (heZ : e + 8 * (w + 1) ≤ Z) (hsep : slot w aN + 8 * w ≤ e) :
    WP isa AdxSquare.redcRow s fun t =>
      Outside B e (8 * (w + 1)) s.mem t.mem ∧ t.gpr .r8 = off B (e + 8) ∧
      t.zf = some (decide (e + 8 = slot w aTmp)) ∧
      Keep [.rdx, .rax, .rsi, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx, .r10, .r8] s t := by
  have hn := hs.nowrap
  have hN := slot_le (w := w) (show aN < 8 by decide)
  unfold AdxSquare.redcRow
  refine WP.seq (WP.mono (redcHead_ok hs hdi hH h8 (by omega_using [heZ]) hZ) fun s₁ ⟨_, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (AdxSquareWide.row_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans h8)
    ((k₁.gpr (by decide)).trans h9) ((k₁.gpr (by decide)).trans hbp) (by omega_using [hw1]) (by omega_using [hw])
    (by omega_using [heZ]) (by omega_using [heZ, hsep]) (by omega_using [hsep])) fun s₂ ⟨_, ho, h14, k₂⟩ => ?_)
  rw [hm₁] at ho
  have k12 := k₁.trans k₂
  refine WP.seq (WP.mono (redcTail_ok (hs.congr k12.2.2) ((k12.gpr (by decide)).trans h8)
    h14 (by omega_using [heZ])) fun s₃ ⟨lo, hm₃, _, _, h8₃, k₃⟩ => ?_)
  have out₃ : Outside B (e + 8 * w) 8 s₂.mem s₃.mem := by
    rw [hm₃]; exact writeW_outside _ _ _ (by omega_using [heZ, hn])
  have allout : Outside B e (8 * (w + 1)) s.mem s₃.mem :=
    (ho.mono (o' := e) (n' := 8 * (w + 1)) (Nat.le_refl _) (by omega_using [])).trans
      (out₃.mono (o' := e) (n' := 8 * (w + 1)) (by omega_using []) (by omega_using []))
  have k123 := k12.trans k₃
  refine WP.mono (VG.Proof.Bignum.X86_64.rowEnd_ok (hs.congr k123.2.2)
    ((k123.gpr (by decide)).trans hdi) (hH.of_outside allout he) hZ h8₃ (by omega_using [hw1, heZ]))
    fun t ⟨hz, hm, h8', kt⟩ => ⟨?_, h8', hz, (k123.trans kt).mono (by decide)⟩
  rw [hm]; exact allout

end VG.Proof.Bignum.X86_64.AdxSquare

end

end

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

end

end

/-! ## AdxTiledChoice -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem alignedChoice_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) (hsz : SizeOk w) :
    WP isa (AdxTiledProduct.alignedChoice o a b) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledProduct.alignedChoice
  refine WP.seq (WP.mono (AdxSquare.redcTest_ok hs hdi hH hZ (by omega_using [hw'])) fun s₁ ⟨hz, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  rw [← hm₁] at hinv hB hH ⊢
  have post : ∀ t, (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s₁ t) →
      (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s t) :=
    fun t ⟨h1, h2, h3, k⟩ => ⟨h1, h2, h3, (k₁.trans k).mono (by decide)⟩
  by_cases h8 : w%8=0
  · refine WP.ite true (by simp [eval,hz,h8]) (fun _ => WP.mono
      (montMul_ok hs₁ hdi₁ hH hZ (by omega_using [h8] : w=8*(w/8)) (by omega_using [hw, h8]) hw' (hH.ops3 ho ha hb) (.head _) (.tail _ (.head _)) (.tail _ (.tail _ (.head _))) ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hinv hB) post) (by simp)
  · refine WP.ite false (by simp [eval,hz,h8]) (by simp) (fun _ =>
      WP.mono (fused_ok hs₁ hdi₁ hH hZ hsz.1 hsz.2.1 hw' ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hinv hB) post)

theorem choice_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa (AdxTiledProduct.choice o a b) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledProduct.choice
  refine WP.seq (WP.mono (sizeTest_ok hs hdi hH hZ) fun s₁ ⟨hz, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  rw [← hm₁] at hinv hB hH ⊢
  have post : ∀ t, (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s₁ t) →
      (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s t) :=
    fun t ⟨h1, h2, h3, k⟩ => ⟨h1, h2, h3, (k₁.trans k).mono (by decide)⟩
  by_cases h8 : SizeOk w
  · refine WP.ite true (by simp [eval,hz,h8]) (fun _ => WP.mono
      (alignedChoice_ok hs₁ hdi₁ hH hZ hw hw' ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hinv hB h8) post) (by simp)
  · refine WP.ite false (by simp [eval,hz,h8]) (by simp) (fun _ => WP.mono (VG.Proof.Bignum.X86_64.montMul_ok hs₁ hdi₁ hH hZ hw hw'
      (by decide) (by decide) (by decide) ho ha hb (by decide) (by decide) (Ne.symm ho1) (Ne.symm ha1) (Ne.symm hb1)
      (by decide) (Ne.symm ho2) hinv hB) post)

end VG.Proof.Bignum.X86_64.AdxTiledProduct

end

/-! ## AdxTiledChoiceCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.Bignum.X86_64

theorem aligned_ct {o a b : Nat} (ho : o<8) (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup b)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a b)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true) :
    RelCT isa (Two fun L s => AdxSquare.GW L s ∧ L.w%8=0)
      (AdxTiledProduct.montMul o a b) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨L,⟨⟨⟨mi,gs,hZ⟩,sz⟩,h8⟩,⟨⟨⟨mj,gt,_⟩,_⟩,_⟩⟩ es et
  have hw := sz.lt
  have hp := sz.2.1
  let R : Layout := ⟨L.B,L.Z,L.w,L.w/8,hZ,hw,by omega_using [h8],by omega_using [h8, hp]⟩
  exact montMul_ct (ps := [(o,o),(a,a),(b,b)]) (.head _) (.tail _ (.head _)) (.tail _ (.tail _ (.head _))) ha hb ha1 ha2 hb1 hb2 hS hR hF
    _ _ _ _ _ _ ⟨R,⟨⟨mi,gs⟩,gs.hdr.ops3 ho ha hb⟩,⟨mj,gt⟩,gt.hdr.ops3 ho ha hb⟩ es et

theorem alignedChoice_ct {o a b : Nat} (ho : o<8) (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup b)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a b)) h₄).isSome=true) :
    RelCT isa (Two AdxSquare.GW) (AdxTiledProduct.alignedChoice o a b) (fun _ _ => True) := by
  unfold AdxTiledProduct.alignedChoice
  refine RelCT.seq (two_piece (Ψ := fun L s => AdxSquare.GW L s ∧ s.zf=some (decide (L.w%8=0)))
    [.rdi] AdxSquare.pins_gw (by taint_decide) ?_) ?_
  · intro L s ⟨⟨mi,hg,hZ⟩,sz⟩
    exact WP.mono (AdxSquare.redcTest_ok hg.scr hg.rdi hg.hdr hZ (by have := sz.lt; omega_using [this]))
      fun _ ⟨z,m,k⟩ => ⟨⟨⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,hZ⟩,sz⟩,z⟩
  refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
  · refine two_map id (fun L s ⟨⟨h,z⟩,e⟩ => ⟨h,?_⟩) (aligned_ct ho ha hb ha1 ha2 hb1 hb2 hS hT hF)
    simp only [eval,z,Option.some.injEq,decide_eq_true_eq] at e
    exact e
  · exact two_map id (fun _ _ h => h.1.1) (fused_ct ho ha hb ha1 ha2 hb1 hb2 hS hR hF)

theorem choice_ct {o a b : Nat} (ho : o<8) (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₀ h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hM : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a b aN aAcc aTmp)) h₀).isSome=true)
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup b)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a b)) h₄).isSome=true) :
    RelCT isa (Two GoodW) (AdxTiledProduct.choice o a b) (fun _ _ => True) := by
  unfold AdxTiledProduct.choice
  refine RelCT.seq (two_piece (Ψ := fun L s => GoodW L s ∧ s.zf=some (decide (SizeOk L.w)))
    [.rdi] pins_goodW (by taint_decide) ?_) ?_
  · intro L s ⟨mi,hg,hZ⟩
    exact WP.mono (sizeTest_ok hg.scr hg.rdi hg.hdr hZ) fun _ ⟨z,m,k⟩ =>
      ⟨⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,hZ⟩,z⟩
  refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
  · refine two_map id (fun L s ⟨⟨h,z⟩,e⟩ => ⟨h,?_⟩) (alignedChoice_ct ho ha hb ha1 ha2 hb1 hb2 hS hR hF hT)
    simp only [eval,z,Option.some.injEq,decide_eq_true_eq] at e
    exact e
  · exact two_map id (fun _ _ h => h.1.1) (montMul_ctW (by decide) (by decide) (by decide) ho ha hb hM)

end VG.Proof.Bignum.X86_64.AdxTiledProduct

end

end

end

/-! ### `Bignum.X86_64.AdxTiledSquareDispatch`, which this module and modules that import it used -/

section

/-! ## AdxTiledSquareMont -/

@[expose] public section

section

/-! Correctness of Montgomery squaring with BMI2 and ADX. -/

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- Tiled Montgomery squaring preserves the reduced-input contract. -/
theorem montSquare_ok {s : State} {B : Addr} {Z w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hwN : w=8*n) (hnN : 0<n) (hw : w < 2 ^ 31)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {co ca o a : Nat} (po : (co, o) ∈ ps) (pa : (ca, a) ∈ ps)
    (ho : o < 8) (ha : a < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w) :
    WP isa (AdxTiledSquare.montSquare co ca) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledSquare.montSquare
  refine WP.seq (WP.mono (rawSquare_ok hs hdi hH hZ hwN hnN hw hv pa ha ha1 ha2) fun s₁ ⟨_, hv₁, ho₁, k₁⟩ => ?_)
  exact AdxTiledProduct.redcFinish_ok hs hdi hH hZ hwN hnN hw hv po ho ho1 ho2 hinv
    (AdxTiledProduct.mul_lt_mont (wv_lt _ _ _ _) hB) hv₁ ho₁ k₁

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareDispatch -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem alignedChoice_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a : Nat} (ho : o < 8) (ha : a < 8)
    (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w) (hsz : SizeOk w) :
    WP isa (AdxTiledSquare.alignedChoice o a) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledSquare.alignedChoice
  refine WP.seq (WP.mono (AdxSquare.redcTest_ok hs hdi hH hZ (by omega_using [hw'])) fun s₁ ⟨hz, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  rw [← hm₁] at hinv hB hH ⊢
  have post : ∀ t, (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w a) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s₁ t) →
      (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w a) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s t) :=
    fun t ⟨h1, h2, h3, k⟩ => ⟨h1, h2, h3, (k₁.trans k).mono (by decide)⟩
  by_cases h8 : w%8=0
  · refine WP.ite true (by simp [eval,hz,h8]) (fun _ => WP.mono
      (montSquare_ok hs₁ hdi₁ hH hZ (by omega_using [h8] : w=8*(w/8)) (by omega_using [hw, h8]) hw' (hH.ops3 ho ha ha) (.head _) (.tail _ (.head _)) ho ha ho1 ho2 ha1 ha2 hinv hB) post) (by simp)
  · refine WP.ite false (by simp [eval,hz,h8]) (by simp) (fun _ =>
      WP.mono (AdxSquare.montSquare4_ok hs₁ hdi₁ hH hZ hw hw' ho ha ho1 ho2 ha1 ha2 hinv hB hsz.1) post)

theorem choice_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a : Nat} (ho : o < 8) (ha : a < 8)
    (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w) :
    WP isa (AdxTiledSquare.choice o a) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledSquare.choice
  refine WP.seq (WP.mono (sizeTest_ok hs hdi hH hZ) fun s₁ ⟨hz, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  rw [← hm₁] at hinv hB hH ⊢
  have post : ∀ t, (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w a) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s₁ t) →
      (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w a) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s t) :=
    fun t ⟨h1, h2, h3, k⟩ => ⟨h1, h2, h3, (k₁.trans k).mono (by decide)⟩
  by_cases h8 : SizeOk w
  · refine WP.ite true (by simp [eval,hz,h8]) (fun _ => WP.mono
      (alignedChoice_ok hs₁ hdi₁ hH hZ hw hw' ho ha ho1 ho2 ha1 ha2 hinv hB h8) post) (by simp)
  · refine WP.ite false (by simp [eval,hz,h8]) (by simp) (fun _ => WP.mono
      (VG.Proof.Bignum.X86_64.montMul_ok hs₁ hdi₁ hH hZ hw hw'
        (by decide) (by decide) (by decide) ho ha ha (by decide) (by decide) (Ne.symm ho1) (Ne.symm ha1)
        (Ne.symm ha1) (by decide) (Ne.symm ho2) hinv hB) post)

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

end

end

/-! ### `Bignum.X86_64.AdxTiledSquareRawCrossCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxTiledSquareRowsChoiceCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxTiledSquareRowsCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxRect8RowSCT`, which this module and modules that import it used -/

section

/-!
# A square's row in constant time

`rowS_ct`: as `row_ct`, for `AdxRect8.rowS`: its blocks but the last, the
handed carry, the last block. Whether the row has one block, and when the
loop stops, are the public layout's; the handed carry is only added.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset handOffset)
open VG.Proof.MlKem.X86_64 (Keep)

/-- The handed carry's slot is outside what a row writes. -/
theorem hand_frame {m m' : Mem} {B : Addr} {w : Nat} (hf : Frm B (rowRanges w) m m') :
    word m' B handOffset = word m B handOffset := by
  refine hf.word_eq ?_ (by unfold handOffset sFn; omega_using [])
  intro r hr
  simp only [rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Or.inl (by unfold rawBase handOffset sFn slot hdrBytes aAcc; omega_using [])
  · exact Or.inr (by unfold carryOffset handOffset sFn; omega_using [])
  · exact Or.inr (by unfold handOffset sFn; omega_using [])

/-- At column block `k` of a square's row, before the handed carry is added:
the pending carry and the handed carry at most 2. -/
def LoopStateH (ps : List (Nat × Nat)) (a b : Nat) (L : RowLayout) (k : Nat) (s : State) : Prop :=
  ∃ s₀ mi x cb, Ops s₀.mem L.B L.w ps ∧ cb ≤ 2 ∧ (word s₀.mem L.B handOffset).toNat ≤ 2 ∧
    StreamInv s₀ L.B L.Z L.w a b L.i L.j₀ k mi x cb s

theorem LoopStateH.loop {ps : List (Nat × Nat)} {a b : Nat} {L : RowLayout} {k : Nat} {s : State}
    (h : LoopStateH ps a b L k s) : LoopState ps a b L k s := by
  obtain ⟨s₀,mi,x,cb,hv,_,_,h⟩ := h
  exact ⟨s₀,mi,x,cb,hv,h⟩

theorem pinsH (ps : List (Nat × Nat)) (a b : Nat) (k : RowLayout → Nat) :
    Pins (fun L s => LoopStateH ps a b L (k L) s) [.rdi,.rcx,.rbp,.rsi] := by
  rintro L s t ⟨_,_,_,_,_,_,_,hs⟩ ⟨_,_,_,_,_,_,_,ht⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.rdi.trans ht.rdi.symm
  · exact hs.pa.trans ht.pa.symm
  · exact hs.pb.trans ht.pb.symm
  · exact hs.po.trans ht.po.symm

theorem setupH_fw {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (L : RowLayout) (s : State)
    (h : (RowState ps L 0 s ∧ word s.mem L.B carryOffset = 0) ∧ (word s.mem L.B handOffset).toNat ≤ 2) :
    WP isa (.block (AdxRect8.setup ca cb)) s
      (fun t => RowBases ps a b L t ∧ (word t.mem L.B handOffset).toNat ≤ 2) := by
  obtain ⟨⟨⟨mi,hg,hv,hI,hJ⟩,hc⟩,hh⟩ := h
  simp only [Nat.mul_zero,Nat.add_zero] at hJ
  refine WP.mono (setup_ok hg.scr hg.rdi hg.hdr L.hZ hv pa pb hI hJ) fun t ⟨ca,cb,co,mt,kt⟩ => ?_
  exact ⟨⟨⟨mi,hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,mt ▸ hv,mt ▸ hI,mt ▸ hJ,
    mt ▸ hc,ca,cb,co⟩,mt ▸ hh⟩

theorem loadH_fw {ps : List (Nat × Nat)} {a b : Nat} (L : RowLayout) (s : State)
    (h : RowBases ps a b L s ∧ (word s.mem L.B handOffset).toNat ≤ 2) :
    WP isa (.block AdxRotate8.loadCols) s (LoopStateH ps a b L 0) := by
  obtain ⟨⟨⟨mi,hg⟩,hv,hI,hJ,hc,ca,cb,co⟩,hh⟩ := h
  have hwN := L.hwN; have hn := L.hn
  exact WP.mono (rowLoad_ok (s₀ := s) hg.scr hg.rdi hg.hdr L.hZ L.hi (by omega_using [hwN, hn]) hI hJ (by rw [hc]; rfl)
    ca cb co rfl (Keep.refl _ _)) fun t ht => ⟨s,mi,0,2,hv,Nat.le_refl _,hh,ht⟩

theorem one_fw {ps : List (Nat × Nat)} {a b : Nat} (L : RowLayout) (s : State) (h : LoopStateH ps a b L 0 s) :
    WP isa (.block AdxRect8.oneTest) s
      (fun t => LoopStateH ps a b L 0 t ∧ isa.eval .e t = some (decide (L.n = 1))) := by
  obtain ⟨s₀,mi,x,cb,hv,hcb,hh,h⟩ := h
  have hwN := L.hwN; have hw := L.hw; have hn := L.hn
  refine WP.mono (oneTest_ok (j := L.j₀) h.scr h.rdi h.hdr L.hZ (by omega) (by omega_using [hw])
    (by simpa only [Nat.mul_zero,Nat.add_zero] using h.indexJ)) fun t ⟨mt,zt,kt⟩ =>
      ⟨⟨s₀,mi,x,cb,hv,hcb,hh,h.of_keep mt kt⟩,?_⟩
  simp only [eval,zt]
  exact congrArg some (decide_eq_decide.mpr (by omega_using [hwN]))

theorem rowS_body_ct {ps : List (Nat × Nat)} {a b : Nat}
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) :
    RelCT isa (Two fun (p : RowLayout × Nat) s => p.2 < p.1.n - 1 ∧ LoopStateH ps a b p.1 p.2 s)
      AdxRect8.rowStepS (fun _ _ => True) := by
  unfold AdxRect8.rowStepS
  refine two_map (Φ' := AtLoop ps a b) id (fun p s h => ⟨by dsimp only [id]; omega, h.2.loop⟩) ?_
  refine RelCT.seq (two_piece [.rdi,.rcx,.rbp,.rsi] (loop_pins ps a b) (by taint_decide)
      (tile_fw ha hb ha1 ha2 hb1 hb2)) (two_taint [.rdi] ?_ (by taint_decide))
  intro p s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.trans ht.symm

theorem rowS_fw {ps : List (Nat × Nat)} {a b : Nat}
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (L : RowLayout) (k : Nat) (s : State) (hk : k < L.n - 1) (h : LoopStateH ps a b L k s) :
    WP isa AdxRect8.rowStepS s fun t =>
      isa.eval .ne t = some (decide (k+1 < L.n - 1)) ∧
      (k+1 < L.n - 1 → LoopStateH ps a b L (k+1) t) ∧ (k+1 = L.n - 1 → LoopStateH ps a b L (L.n - 1) t) := by
  obtain ⟨s₀,mi,x,cb,hv,hcb,hh,h⟩ := h
  have hwN := L.hwN; have hw := L.hw
  unfold AdxRect8.rowStepS
  refine WP.mono (streamStep_gen L.hZ L.hw L.hi ha hb ha1 ha2 hb1 hb2 L.hwN (by omega_using [hk])
    (fun u hs hd hh' hj => nextColumnS_ok hs hd hh' L.hZ (by omega) (by omega_using [hw]) hj) h) fun t ⟨zt,ht⟩ => ?_
  have post : LoopStateH ps a b L (k+1) t := ⟨s₀,mi,x,2,hv,Nat.le_refl _,hh,ht⟩
  refine ⟨?_,fun _ => post,fun he => he ▸ post⟩
  simp only [eval,zt,Option.map_some]
  by_cases he : k+1 = L.n - 1
  · simp only [show L.j₀+8*k+16 = L.w by omega_using [hwN, he],decide_true,Bool.not_true,
      show ¬(k+1 < L.n - 1) by omega_using [he],decide_false]
  · simp only [show ¬(L.j₀+8*k+16 = L.w) by omega_using [hwN, he],decide_false,Bool.not_false,
      show k+1 < L.n - 1 by omega_using [hk, he],decide_true]

theorem hand_fw {ps : List (Nat × Nat)} {a b : Nat} (L : RowLayout) (s : State)
    (h : LoopStateH ps a b L (L.n - 1) s) :
    WP isa (.block AdxRect8.addHand) s (LoopState ps a b L (L.n - 1)) := by
  obtain ⟨s₀,mi,x,cb,hv,hcb,hh,h⟩ := h
  have hwN := L.hwN; have hn := L.hn; have hi := L.hi
  refine WP.mono (addHand_inv L.hZ (by omega_using [hwN, hi]) hcb h rfl (by rw [hand_frame h.frame]; exact hh))
    fun t ht => ⟨s₀,mi,_,4,hv,ht⟩

theorem rowS_ct {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) hint).isSome = true) :
    RelCT isa (Two fun L s => (RowState ps L 0 s ∧ word s.mem L.B carryOffset = 0) ∧
        (word s.mem L.B handOffset).toNat ≤ 2) (AdxRect8.rowS ca cb)
      (Two fun L s => RowState ps L L.n s) := by
  unfold AdxRect8.rowS
  refine RelCT.seq (two_piece [.rdi] ?_ hS (setupH_fw pa pb)) ?_
  · rintro L s t ⟨⟨⟨mi,hs,_⟩,_⟩,_⟩ ⟨⟨⟨mj,ht,_⟩,_⟩,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  refine RelCT.seq (two_piece [.rsi] ?_ (by taint_decide) loadH_fw) ?_
  · rintro L s t ⟨⟨_,_,_,_,_,_,_,hs⟩,_⟩ ⟨⟨_,_,_,_,_,_,_,ht⟩,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.trans ht.symm
  -- the blocks but the last
  refine RelCT.seq (R := Two (fun L s => LoopStateH ps a b L (L.n - 1) s))
    (RelCT.seq (two_piece [.rdi,.rcx,.rbp,.rsi] (pinsH ps a b fun _ => 0) (by taint_decide) one_fw)
      (two_ite (fun L s₁ s₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_)) ?_
  · refine two_post (two_taint [] (fun _ _ _ _ _ r hr => by simp at hr) (by taint_decide)) ?_
    intro L s ⟨⟨h,he⟩,hz⟩
    rw [he] at hz
    have h1 : L.n = 1 := by simpa using hz
    exact WP.block_nil (by rw [h1]; exact h)
  · refine (two_loop (fun L : RowLayout => L.n - 1) (Φ := LoopStateH ps a b)
      (Ψ := fun L s => LoopStateH ps a b L (L.n - 1) s)
      (rowS_body_ct ha hb ha1 ha2 hb1 hb2) (rowS_fw ha hb ha1 ha2 hb1 hb2)).mono ?_ (fun _ _ h => h)
    rintro s t ⟨L,⟨⟨hs,es⟩,zs⟩,⟨⟨ht,_⟩,_⟩⟩
    rw [es] at zs
    have h1 : L.n ≠ 1 := by simpa using zs
    have hn := L.hn
    exact ⟨L,⟨by omega_using [h1, hn],hs⟩,by omega_using [h1, hn],ht⟩
  -- the handed carry, the last block, the columns stored
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) hand_fw) ?_
  · rintro L s t ⟨_,_,_,_,_,_,_,hs⟩ ⟨_,_,_,_,_,_,_,ht⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  refine RelCT.seq (two_post (two_map (fun L : RowLayout => (L, L.n - 1))
      (fun L s h => ⟨by dsimp only; have := L.hn; omega_using [this],h⟩) (row_body_ct ha hb ha1 ha2 hb1 hb2))
    (Ψ := fun L s => LoopState ps a b L L.n s) fun L s h => WP.mono
      (row_fw ha hb ha1 ha2 hb1 hb2 L (L.n - 1) s (by have := L.hn; omega_using [this]) h)
      fun t ⟨_,_,h3⟩ => by have := L.hn; rw [show L.n - 1 + 1 = L.n by omega_using [this]] at h3; exact h3 rfl) ?_
  refine two_post (two_taint [.rsi] ?_ (by taint_decide)) end_fw
  rintro L s t ⟨_,_,_,_,_,hs⟩ ⟨_,_,_,_,_,ht⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.po.trans ht.po.symm

end VG.Proof.Bignum.X86_64.AdxRect8

end

end

/-! ## AdxTiledSquareRowCT -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRect8 (RowLayout RowState rawBase)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset handOffset)
open VG.Proof.Bignum.X86_64.AdxTiledProduct (ranges frame_hdr frame_ops TailReady tail_ok tail_ct)
open VG.Proof.MlKem.X86_64 (Keep)

def RowStart (ps : List (Nat × Nat)) (L : RowLayout) (s : State) : Prop :=
  (∃ q, L.w=L.i+8+8*q) ∧ L.j₀=L.i+8 ∧ (∃ mi, Good s L.B L.Z L.w mi) ∧ Ops s.mem L.B L.w ps ∧
    word s.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.i ∧ (word s.mem L.B handOffset).toNat ≤ 2

def RowReady (ps : List (Nat × Nat)) (L : RowLayout) (s : State) : Prop :=
  (∃ q, L.w=L.i+8+8*q) ∧ L.j₀=L.i+8 ∧ RowState ps L 0 s ∧ word s.mem L.B carryOffset=0 ∧
    (word s.mem L.B handOffset).toNat ≤ 2

theorem init_fw {ps : List (Nat × Nat)} (L : RowLayout) (s : State) (h : RowStart ps L s) :
    WP isa (.block AdxTiledSquare.rowInit) s (RowReady ps L) := by
  obtain ⟨tail,j0,⟨mi,hg⟩,hv,idx,hh⟩ := h
  refine WP.mono (rowInit_ok hg.scr hg.rdi L.hZ idx) fun t ⟨c,j,o,k⟩ => ?_
  have f : Frm L.B (ranges L.w) s.mem t.mem := by
    intro x hx
    apply o x
    have := hx (8*sFn 12,32) (by simp [ranges])
    simp only [sFn] at *; omega_arith
  have it : word t.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.i := by
    rw [o.word (by decide) (by decide)]; exact idx
  exact ⟨tail,j0,⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,frame_hdr hg.hdr f⟩,frame_ops hv f,it,
    by rw [j0]; exact j⟩,c,by rw [o.word (by unfold handOffset sFn; omega_arith) (by unfold handOffset sFn; omega_arith)]; exact hh⟩

theorem inner_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    (L : RowLayout) (s : State) (h : RowReady ps L s) :
    WP isa (AdxRect8.rowS ca ca) s (fun t => TailReady L t ∧ ∃ q, L.w=L.i+8+8*q) := by
  obtain ⟨tail,j0,⟨mi,hg,hv,idx,jdx⟩,carry,hh⟩ := h
  simp only [Nat.mul_zero,Nat.add_zero] at jdx
  refine WP.mono (AdxRect8.rowS_ok hg.scr hg.rdi hg.hdr hv pa pa L.hZ L.hw L.hi ha ha ha1 ha2 ha1 ha2
    L.hwN L.hn idx jdx (by rw [carry]; rfl) rfl hh) fun t ht => ?_
  have ptr := ht.endPtr.resolve_left (by have := L.hn; omega_arith)
  have wn := L.hwN
  exact ⟨⟨⟨mi,ht.scr,ht.rdi,ht.hdr⟩,ht.indexI,by simpa only [show L.i+L.j₀+8*L.n=L.i+L.w by omega_arith] using ptr⟩,tail⟩

abbrev TailReadyS (L : RowLayout) (s : State) : Prop := TailReady L s ∧ ∃ q, L.w=L.i+8+8*q

theorem lastTest_fw (L : RowLayout) (s : State) (h : TailReadyS L s) :
    WP isa (.block AdxTiledSquare.lastTest) s
      (fun t => TailReadyS L t ∧ isa.eval .e t = some (decide (L.i+16=L.w))) := by
  obtain ⟨⟨⟨mi,hg⟩,idx,ptr⟩,q⟩ := h
  have hw := L.hw; have hi := L.hi
  refine WP.mono (lastTest_ok hg.scr hg.rdi hg.hdr L.hZ (by omega_arith) (by omega_arith) idx) fun t ⟨mt,zt,kt⟩ => ?_
  exact ⟨⟨⟨⟨mi,hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,mt ▸ idx,
    (kt.gpr (by decide)).trans ptr⟩,q⟩,by simp only [eval,zt]⟩

theorem tailS_ct : RelCT isa (Two TailReadyS) AdxTiledSquare.tail (fun _ _ => True) := by
  unfold AdxTiledSquare.tail
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) lastTest_fw)
    (two_ite (fun L s₁ s₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_)
  · rintro L s t ⟨⟨⟨mi,hs⟩,_,_⟩,_⟩ ⟨⟨⟨mj,ht⟩,_,_⟩,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  · exact two_map id (fun _ _ h => h.1.1.1) tail_ct
  · refine two_taint [.rdi] ?_ (by taint_decide)
    intro L s t h1 h2 r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact h1.1.1.1.1.choose_spec.rdi.trans h2.1.1.1.1.choose_spec.rdi.symm

theorem tailS_fw (L : RowLayout) (s : State) (h : TailReadyS L s) :
    WP isa AdxTiledSquare.tail s (fun t => t.gpr .rdi=L.B) := by
  obtain ⟨⟨⟨mi,hg⟩,idx,ptr⟩,q,hq⟩ := h
  have hw := L.hw; have hi := L.hi
  unfold AdxTiledSquare.tail
  refine WP.seq (WP.mono (lastTest_ok hg.scr hg.rdi hg.hdr L.hZ (by omega_arith) (by omega_arith) idx)
    fun y ⟨my,zy,ky⟩ => ?_)
  have sy := hg.scr.congr ky.2.2
  have dy : y.gpr .rdi = L.B := (ky.gpr (by decide)).trans hg.rdi
  by_cases hl : L.i+16=L.w
  · refine WP.ite true (by simp [eval,zy,hl]) (fun _ => ?_) (by intro h; cases h)
    exact WP.mono (AdxTiledProduct.tail_ok sy dy (my ▸ hg.hdr) L.hZ L.hw hq (my ▸ idx)
      ((ky.gpr (by decide)).trans ptr)) fun t ⟨_,_,k⟩ => (k.gpr (by decide)).trans dy
  · refine WP.ite false (by simp [eval,zy,hl]) (by intro h; cases h) (fun _ => ?_)
    exact WP.mono (hand_ok sy dy L.hZ) fun t ⟨_,k⟩ => (k.gpr (by decide)).trans dy

theorem row_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) hint).isSome=true) :
    RelCT isa (Two (RowStart ps)) (AdxTiledSquare.row ca) (fun _ _ => True) := by
  unfold AdxTiledSquare.row
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) init_fw) ?_
  · rintro L s t ⟨_,_,⟨mi,hs⟩,_,_⟩ ⟨_,_,⟨mj,ht⟩,_,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  refine RelCT.seq (two_post (two_map id (fun _ _ h => ⟨⟨h.2.2.1,h.2.2.2.1⟩,h.2.2.2.2⟩)
    ((AdxRect8.rowS_ct pa pa ha ha ha1 ha2 ha1 ha2 hS).mono (fun _ _ h => h) (fun _ _ _ => True.intro)))
    (inner_fw pa ha ha1 ha2)) ?_
  refine RelCT.seq (two_post tailS_ct (Ψ := fun L s => s.gpr .rdi=L.B) tailS_fw)
    (two_taint [.rdi] ?_ (by taint_decide))
  intro L s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.trans ht.symm

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareRowsCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout LoopState GoodV frame_ops ranges frame_hdr)

def StartGood (ps : List (Nat × Nat)) (L : Layout) (s : State) : Prop := 1<L.n ∧ GoodV ps L s

/-- Before row `k`, with the carry the row before handed at most 2. -/
def LoopStateQ (ps : List (Nat × Nat)) (L : Layout) (k : Nat) (s : State) : Prop :=
  LoopState ps L k s ∧ (word s.mem L.B AdxRect8.handOffset).toNat ≤ 2

theorem row_loop_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) hint).isSome=true) :
    RelCT isa (Two fun p : Layout × Nat => fun s => p.2<p.1.n-1 ∧ LoopStateQ ps p.1 p.2 s)
      (AdxTiledSquare.row ca) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨⟨L,k⟩,⟨hk,⟨mi,gs,vs,is⟩,hs⟩,⟨_,⟨mj,gt,vt,it⟩,ht⟩⟩ es et
  dsimp only at hk
  have wn := L.hwN
  let R : AdxRect8.RowLayout := ⟨L.B,L.Z,L.w,8*k,8*k+8,L.n-k-1,L.hZ,L.hw,by omega_arith,by omega_arith,by omega_arith⟩
  apply row_ct pa ha ha1 ha2 hS s t ts tt s' t' ?_ es et
  exact ⟨R,⟨⟨L.n-k-1,by dsimp [R]; omega_arith⟩,rfl,⟨mi,gs⟩,vs,is,hs⟩,
    ⟨L.n-k-1,by dsimp [R]; omega_arith⟩,rfl,⟨mj,gt⟩,vt,it,ht⟩

theorem row_loop_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    (L : Layout) (k : Nat) (s : State) (hk : k<L.n-1) (h : LoopStateQ ps L k s) :
    WP isa (AdxTiledSquare.row ca) s fun t =>
      isa.eval .ne t=some (decide (k+1<L.n-1)) ∧
      (k+1<L.n-1 → LoopStateQ ps L (k+1) t) ∧ (k+1=L.n-1 → GoodV ps L t) := by
  obtain ⟨⟨mi,hg,hv,idx⟩,hh⟩ := h
  have wn := L.hwN
  refine WP.mono (row_ok hg.scr hg.rdi hg.hdr hv pa L.hZ L.hw
    (by omega_arith : L.w=8*k+8+8*(L.n-k-1)) (by omega_arith) ha ha1 ha2 idx rfl hh)
    fun t ⟨zt,it,σt,_,ht,ft,kt⟩ => ?_
  have good : Good t L.B L.Z L.w mi := ⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,ht⟩
  have vt := frame_ops hv ft
  refine ⟨?_,fun _ => ⟨⟨mi,good,vt,?_⟩,σt⟩,fun _ => ⟨⟨mi,good⟩,vt⟩⟩
  · simp only [eval,zt,Option.map_some]
    by_cases he : k+1=L.n-1
    · simp only [show 8*k+8=L.w-8 by omega_arith,decide_true,Bool.not_true,
        show ¬(k+1<L.n-1) by omega_arith,decide_false]
    · simp only [show ¬(8*k+8=L.w-8) by omega_arith,decide_false,Bool.not_false,
        show k+1<L.n-1 by omega_arith,decide_true]
  · simpa only [show 8*(k+1)=8*k+8 by omega_arith] using it

theorem rows_init_fw {ps : List (Nat × Nat)} (L : Layout) (s : State) (h : StartGood ps L s) :
    WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax,.store (hdr (sFn 15)) .rax]) s
      (fun t => 0<L.n-1 ∧ LoopStateQ ps L 0 t) := by
  obtain ⟨h1,⟨mi,hg⟩,hv⟩ := h
  have hZ := L.hZ
  have iZ : 8*sFn 12+8 ≤ L.Z := by
    have := hdr_lt_slot L.w 8 (show sFn 12<32 by decide); omega_arith
  have i15 : 8*sFn 15+8 ≤ L.Z := by
    have := hdr_lt_slot L.w 8 (show sFn 15<32 by decide); omega_arith
  have nowrap := hg.scr.nowrap
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem=(s.mem.writeW (off L.B (8*sFn 12)) (0 : BitVec 64)).writeW
    (off L.B (8*sFn 15)) (0 : BitVec 64)) ?_ rfl) fun t ⟨mt,kt⟩ => ?_
  · xrun [State.ea,hdr,hg.rdi,hdrOff,hg.scr.st iZ,hg.scr.st i15]; rfl
  have o1 : Outside L.B (8*sFn 12) 8 s.mem (s.mem.writeW (off L.B (8*sFn 12)) (0 : BitVec 64)) :=
    writeW_outside _ _ _ (by decide)
  have o2 : Outside L.B (8*sFn 15) 8 (s.mem.writeW (off L.B (8*sFn 12)) (0 : BitVec 64)) t.mem := by
    rw [mt]; exact writeW_outside _ _ _ (by decide)
  have ft : Frm L.B (ranges L.w) s.mem t.mem := by
    intro x hx
    have := hx (8*sFn 12,32) (by simp [ranges])
    exact (o2 x (by simp only [sFn] at *; omega_arith)).trans (o1 x (by simp only [sFn] at *; omega_arith))
  refine ⟨by omega_arith,⟨mi,⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,frame_hdr hg.hdr ft⟩,
    frame_ops hv ft,?_⟩,?_⟩
  · rw [o2.word (by decide) (by decide),word_writeW_self]; rfl
  · rw [mt,show AdxRect8.handOffset = 8*sFn 15 from rfl,word_writeW_self]; decide

theorem rows_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) hint).isSome=true) :
    RelCT isa (Two (StartGood ps)) (AdxTiledSquare.rows ca) (Two (GoodV ps)) := by
  unfold AdxTiledSquare.rows
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) rows_init_fw)
    (two_loop (fun L : Layout => L.n-1) (Φ := LoopStateQ ps) (row_loop_ct pa ha ha1 ha2 hS)
      (row_loop_fw pa ha ha1 ha2))
  rintro L s t ⟨_,⟨mi,hs⟩,_⟩ ⟨_,⟨mj,ht⟩,_⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareRow1CT: the rows of a square of one row, without hand-off -/

section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRect8 (RowLayout RowState rawBase)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)
open VG.Proof.Bignum.X86_64.AdxTiledProduct (ranges frame_hdr frame_ops TailReady tail_ok tail_ct)

def RowStart1 (ps : List (Nat × Nat)) (L : RowLayout) (s : State) : Prop :=
  (∃ q, L.w=L.i+8+8*q) ∧ L.j₀=L.i+8 ∧ (∃ mi, Good s L.B L.Z L.w mi) ∧ Ops s.mem L.B L.w ps ∧
    word s.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.i

def RowReady1 (ps : List (Nat × Nat)) (L : RowLayout) (s : State) : Prop :=
  (∃ q, L.w=L.i+8+8*q) ∧ L.j₀=L.i+8 ∧ RowState ps L 0 s ∧ word s.mem L.B carryOffset=0

theorem init1_fw {ps : List (Nat × Nat)} (L : RowLayout) (s : State) (h : RowStart1 ps L s) :
    WP isa (.block AdxTiledSquare.rowInit) s (RowReady1 ps L) := by
  obtain ⟨tail,j0,⟨mi,hg⟩,hv,idx⟩ := h
  refine WP.mono (rowInit_ok hg.scr hg.rdi L.hZ idx) fun t ⟨c,j,o,k⟩ => ?_
  have f : Frm L.B (ranges L.w) s.mem t.mem := by
    intro x hx
    apply o x
    have := hx (8*sFn 12,32) (by simp [ranges])
    simp only [sFn] at *; omega_arith
  have hh : Hdr t.mem L.B L.w mi := frame_hdr hg.hdr f
  have it : word t.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.i := by
    rw [o.word (by decide) (by decide)]; exact idx
  exact ⟨tail,j0,⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,hh⟩,frame_ops hv f,it,
    by rw [j0]; exact j⟩,c⟩

theorem inner1_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    (L : RowLayout) (s : State) (h : RowReady1 ps L s) :
    WP isa (AdxRect8.row ca ca) s (fun t => TailReady L t ∧ ∃ q, L.w=L.i+8+8*q) := by
  obtain ⟨tail,j0,⟨mi,hg,hv,idx,jdx⟩,carry⟩ := h
  simp only [Nat.mul_zero,Nat.add_zero] at jdx
  refine WP.mono (AdxRect8.row_ok hg.scr hg.rdi hg.hdr hv pa pa L.hZ L.hw L.hi ha ha ha1 ha2 ha1 ha2
    L.hwN L.hn idx jdx (by rw [carry]; rfl)) fun t ht => ?_
  have ptr := ht.endPtr.resolve_left (by have := L.hn; omega_arith)
  have wn := L.hwN
  exact ⟨⟨⟨mi,ht.scr,ht.rdi,ht.hdr⟩,ht.indexI,by simpa only [show L.i+L.j₀+8*L.n=L.i+L.w by omega_arith] using ptr⟩,tail⟩

theorem row1_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) hint).isSome=true) :
    RelCT isa (Two (RowStart1 ps)) (AdxTiledSquare.row1 ca) (fun _ _ => True) := by
  unfold AdxTiledSquare.row1
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) init1_fw) ?_
  · rintro L s t ⟨_,_,⟨mi,hs⟩,_,_⟩ ⟨_,_,⟨mj,ht⟩,_,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  refine RelCT.seq (two_post (two_map id (fun _ _ h => ⟨h.2.2.1,h.2.2.2⟩)
    ((AdxRect8.row_ct pa pa ha ha ha1 ha2 ha1 ha2 hS).mono (fun _ _ h => h) (fun _ _ _ => True.intro)))
    (inner1_fw pa ha ha1 ha2)) ?_
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.1) tail_ct)
    (Ψ := fun L s => s.gpr .rdi=L.B) ?_)
    (two_taint [.rdi] ?_ (by taint_decide))
  · rintro L s ⟨⟨⟨mi,hg⟩,idx,ptr⟩,q,hq⟩
    exact WP.mono (AdxTiledProduct.tail_ok hg.scr hg.rdi hg.hdr L.hZ L.hw hq idx ptr)
      fun t ⟨_,_,k⟩ => (k.gpr (by decide)).trans hg.rdi
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.trans ht.symm

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareRows1CT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout LoopState GoodV frame_ops)

theorem row1_loop_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) hint).isSome=true) :
    RelCT isa (Two fun p : Layout × Nat => fun s => p.2<p.1.n-1 ∧ LoopState ps p.1 p.2 s)
      (AdxTiledSquare.row1 ca) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨⟨L,k⟩,⟨hk,mi,gs,vs,is⟩,⟨_,mj,gt,vt,it⟩⟩ es et
  dsimp only at hk
  have wn := L.hwN
  let R : AdxRect8.RowLayout := ⟨L.B,L.Z,L.w,8*k,8*k+8,L.n-k-1,L.hZ,L.hw,by omega_arith,by omega_arith,by omega_arith⟩
  apply row1_ct pa ha ha1 ha2 hS s t ts tt s' t' ?_ es et
  exact ⟨R,⟨⟨L.n-k-1,by dsimp [R]; omega_arith⟩,rfl,⟨mi,gs⟩,vs,is⟩,
    ⟨L.n-k-1,by dsimp [R]; omega_arith⟩,rfl,⟨mj,gt⟩,vt,it⟩

theorem row1_loop_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    (L : Layout) (k : Nat) (s : State) (hk : k<L.n-1) (h : LoopState ps L k s) :
    WP isa (AdxTiledSquare.row1 ca) s fun t =>
      isa.eval .ne t=some (decide (k+1<L.n-1)) ∧
      (k+1<L.n-1 → LoopState ps L (k+1) t) ∧ (k+1=L.n-1 → GoodV ps L t) := by
  obtain ⟨mi,hg,hv,idx⟩ := h
  have wn := L.hwN
  refine WP.mono (row1_ok hg.scr hg.rdi hg.hdr hv pa L.hZ L.hw
    (by omega_arith : L.w=8*k+8+8*(L.n-k-1)) (by omega_arith) ha ha1 ha2 idx)
    fun t ⟨zt,it,_,ht,ft,kt⟩ => ?_
  have good : Good t L.B L.Z L.w mi := ⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,ht⟩
  have vt := frame_ops hv ft
  refine ⟨?_,fun _ => ⟨mi,good,vt,?_⟩,fun _ => ⟨⟨mi,good⟩,vt⟩⟩
  · simp only [eval,zt,Option.map_some]
    by_cases he : k+1=L.n-1
    · simp only [show 8*k+8=L.w-8 by omega_arith,decide_true,Bool.not_true,
        show ¬(k+1<L.n-1) by omega_arith,decide_false]
    · simp only [show ¬(8*k+8=L.w-8) by omega_arith,decide_false,Bool.not_false,
        show k+1<L.n-1 by omega_arith,decide_true]
  · simpa only [show 8*(k+1)=8*k+8 by omega_arith] using it

theorem rows1_init_fw {ps : List (Nat × Nat)} (L : Layout) (s : State) (h : StartGood ps L s) :
    WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax]) s
      (fun t => 0<L.n-1 ∧ LoopState ps L 0 t) :=
  WP.mono (AdxTiledProduct.rows_init_fw L s h.2) fun _ ht => ⟨by have := h.1; omega_arith,ht.2⟩

theorem rows1_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) hint).isSome=true) :
    RelCT isa (Two (StartGood ps)) (AdxTiledSquare.rows1 ca) (Two (GoodV ps)) := by
  unfold AdxTiledSquare.rows1
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) rows1_init_fw)
    (two_loop (fun L : Layout => L.n-1) (row1_loop_ct pa ha ha1 ha2 hS)
      (row1_loop_fw pa ha ha1 ha2))
  rintro L s t ⟨_,⟨mi,hs⟩,_⟩ ⟨_,⟨mj,ht⟩,_⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

end

end

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout GoodV)

theorem rowsChoice_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) hint).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledSquare.rowsChoice ca) (Two (GoodV ps)) := by
  unfold AdxTiledSquare.rowsChoice
  refine RelCT.seq (two_piece (Ψ := fun L s => GoodV ps L s ∧ s.zf=some (decide (L.w=8)))
    [.rdi] ?_ (by taint_decide) ?_) ?_
  · rintro L s t ⟨⟨mi,hs⟩,_⟩ ⟨⟨mj,ht⟩,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  · rintro L s ⟨⟨mi,hg⟩,hv⟩
    exact WP.mono (rowsTest_ok hg.scr hg.rdi hg.hdr L.hZ L.hw) fun t ⟨zt,mt,kt⟩ =>
      ⟨⟨⟨mi,hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,mt ▸ hv⟩,zt⟩
  refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
  · exact RelCT.block_nil fun _ _ h => two_mono (fun _ _ h => h.1.1) h
  · refine RelCT.seq (two_piece (Φ := fun L s => (GoodV ps L s ∧ s.zf=some (decide (L.w=8))) ∧
        isa.eval .e s=some false)
      (Ψ := fun L s => StartGood ps L s ∧ s.zf=some (decide (L.w=16)))
      [.rdi] ?_ (by taint_decide) ?_) ?_
    · rintro L s t ⟨⟨⟨⟨mi,hs⟩,_⟩,_⟩,_⟩ ⟨⟨⟨⟨mj,ht⟩,_⟩,_⟩,_⟩ r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      subst r; exact hs.rdi.trans ht.rdi.symm
    · rintro L s ⟨⟨⟨⟨mi,hg⟩,hv⟩,z⟩,e⟩
      simp only [eval,z,Option.some.injEq,decide_eq_false_iff_not] at e
      have wn := L.hwN; have hn := L.hn
      exact WP.mono (rowsTest16_ok hg.scr hg.rdi hg.hdr L.hZ L.hw) fun t ⟨zt,mt,kt⟩ =>
        ⟨⟨by change 1<L.n; omega,
          ⟨mi,hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,mt ▸ hv⟩,zt⟩
    refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
    · exact two_map id (fun L s ⟨⟨hg,_⟩,_⟩ => hg) (rows1_ct pa ha ha1 ha2 hS)
    · exact two_map id (fun L s ⟨⟨hg,_⟩,_⟩ => hg) (rows_ct pa ha ha1 ha2 hS)

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

end

/-! ## AdxTri8RowCT -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

structure CtLayout where
  B : Addr
  Z : Nat
  w : Nat
  I : Nat
  e : Nat
  hZ : slot w 8≤Z
  hi : I+8≤w
  he : e+64≤Z

def HeadState (L : CtLayout) (s : State) : Prop :=
  ∃ mi, Good s L.B L.Z L.w mi ∧ word s.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.I

/-- The rows' state before `clearEnds` sets the output base. -/
def Pre (_n : Nat) (_rs : List Reg) (L : CtLayout) (s : State) : Prop :=
  HeadState L s ∧ s.gpr .rbp=off L.B L.e

/-- The block's output base, in `rcx` through the rows. -/
def Based (L : CtLayout) (s : State) : Prop :=
  HeadState L s ∧ s.gpr .rcx=off L.B (slot L.w aAcc+16*L.I)

def Stage (n : Nat) (rs : List Reg) (L : CtLayout) (s : State) : Prop :=
  Pre n rs L s ∧ s.gpr .rcx=off L.B (slot L.w aAcc+16*L.I)

theorem head_pins : Pins HeadState [.rdi] := by
  rintro L s t ⟨mi,hs,_⟩ ⟨mj,ht,_⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

theorem storeHead_ct (i : Nat) (lo hi : Reg)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rcx]) (AdxTri8.storeHead i lo hi) hint).isSome=true) :
    RelCT isa (Two Based) (AdxTri8.storeHead i lo hi) (fun _ _ => True) := by
  refine two_taint [.rcx] ?_ hT
  intro L s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.2.trans ht.2.symm

theorem rowCore_head {i n : Nat} {col : Reg} {rest : List Reg} (hr : Regs (col::rest))
    (hlen : (col::rest).length=n+1) (hn : rest≠[])
    (hi : i+n+1≤8) (L : CtLayout) (s : State) (h : Stage n (col::rest) L s) :
    WP isa (.block (AdxTri8.rowCore i col rest)) s (Based L) := by
  obtain ⟨⟨⟨mi,hg,hI⟩,hp⟩,hc⟩ := h
  have he := L.he
  refine WP.mono (rowCore_ok col rest hg.scr hp (by rw [hlen]; omega_arith) hn
    hr.1 (fun r h => let q := hr.2 r h; ⟨q.1,q.2.1,q.2.2.1,q.2.2.2.1⟩)) fun t ⟨_,kt⟩ => ?_
  have dr : t.gpr .rdi=s.gpr .rdi := kt.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,fun h => (hr.2 .rdi (List.mem_cons.mpr (Or.inl h))).2.2.2.2 rfl,
      fun h => (hr.2 .rdi (List.mem_cons.mpr (Or.inr h))).2.2.2.2 rfl⟩)
  have cr : t.gpr .rcx=s.gpr .rcx := kt.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,fun h => (hr.2 .rcx (List.mem_cons.mpr (Or.inl h))).2.2.2.1 rfl,
      fun h => (hr.2 .rcx (List.mem_cons.mpr (Or.inr h))).2.2.2.1 rfl⟩)
  exact ⟨⟨mi,⟨hg.scr.congr kt.2.2.2,dr.trans hg.rdi,kt.2.1 ▸ hg.hdr⟩,kt.2.1 ▸ hI⟩,cr.trans hc⟩

theorem rowStep_ct {i n : Nat} {lo hi : Reg} {tail : List Reg}
    (hr : Regs (lo::hi::tail)) (hlen : (lo::hi::tail).length=n+2) (hi8 : i+n+2≤8)
    {hint htail : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rcx]) (AdxTri8.storeHead i lo hi) htail).isSome=true)
    (hC : (taint.check (Taint.ofRegs [.rbp]) (.block (AdxTri8.rowCore i lo (hi::tail))) hint).isSome=true) :
    RelCT isa (Two (Stage (n+1) (lo::hi::tail))) (AdxTri8.rowStep i lo hi tail) (fun _ _ => True) := by
  unfold AdxTri8.rowStep
  refine RelCT.seq (two_piece [.rbp] ?_ hC (rowCore_head hr hlen (by simp) hi8)) ?_
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.1.2.trans ht.1.2.symm
  exact storeHead_ct i lo hi hT

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8RowsCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem rowStep_stage {i n : Nat} {lo hi : Reg} {tail : List Reg}
    (hr : Regs (lo::hi::tail)) (hlen : (lo::hi::tail).length=n+2) (hi8 : i+n+2≤8)
    (L : CtLayout) (s : State) (h : Stage (n+1) (lo::hi::tail) L s) :
    WP isa (AdxTri8.rowStep i lo hi tail) s (Stage n (tail++[lo]) L) := by
  obtain ⟨⟨⟨mi,hg,hI⟩,hp⟩,hc⟩ := h
  have he := L.he; have hiL := L.hi; have hZ := L.hZ
  have bound : slot L.w aAcc+16*L.I+(16+8*(2*i+2))+8≤L.Z := by
    unfold slot aAcc at *; omega_arith
  refine WP.mono (rowStep_ok hg.scr hc hp (by rw [hlen]; omega_arith)
    bound hr.1 hr.2)
    fun t ⟨_,ot,kt⟩ => ?_
  have dr : t.gpr .rdi=L.B := (kt.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,⟨(hr.2 lo (by simp)).2.2.2.2.symm,(hr.2 hi (by simp)).2.2.2.2.symm,
      fun h => (hr.2 .rdi (by simp [h])).2.2.2.2 rfl⟩⟩)).trans hg.rdi
  have pr : t.gpr .rbp=off L.B L.e := (kt.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,⟨(hr.2 lo (by simp)).1.2.1.symm,(hr.2 hi (by simp)).1.2.1.symm,
      fun h => (hr.2 .rbp (by simp [h])).1.2.1 rfl⟩⟩)).trans hp
  have ht := hg.hdr.of_outside ot (by unfold slot; omega_arith)
  have it : word t.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.I := by
    rw [ot.word (by unfold slot hdrBytes sFn; omega_arith) (by decide)]; exact hI
  have len : tail.length=n := by simp only [List.length_cons] at hlen; omega_arith
  have cr : t.gpr .rcx=s.gpr .rcx := kt.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,⟨(hr.2 lo (by simp)).2.2.2.1.symm,(hr.2 hi (by simp)).2.2.2.1.symm,
      fun h => (hr.2 .rcx (by simp [h])).2.2.2.1 rfl⟩⟩)
  exact ⟨⟨⟨mi,⟨hg.scr.congr kt.2.2,dr,ht⟩,it⟩,pr⟩,cr.trans hc⟩

/-- Closed hints for each unrolled row; the loop itself is proved relationally. -/
def RowChecks (i : Nat) (lo hi : Reg) (tail : List Reg) : Prop :=
  ∃ ht hc : VG.Taint.Hint VG.X86_64.Taint.T,
    (taint.check (Taint.ofRegs [.rcx]) (AdxTri8.storeHead i lo hi) ht).isSome=true ∧
    (taint.check (Taint.ofRegs [.rbp]) (.block (AdxTri8.rowCore i lo (hi::tail))) hc).isSome=true

def Checks : Nat → Nat → List Reg → Prop
  | 0, _, _ => True
  | n+1, i, rs => RowChecks i rs[0]! rs[1]! (rs.drop 2) ∧ Checks n (i+1) (AdxTri8.rotate rs)

theorem rows_ct (n i : Nat) (rs : List Reg) (hr : Regs rs) (hlen : rs.length=n+1)
    (hi : i+n+1≤8) (hc : Checks n i rs) :
    RelCT isa (Two (Stage n rs)) (AdxTri8.rows n i rs) (fun _ _ => True) := by
  induction n generalizing i rs with
  | zero => exact RelCT.block_nil fun _ _ _ => trivial
  | succ n ih =>
    cases rs with
    | nil => simp only [List.length_nil] at hlen; omega_arith
    | cons lo rs =>
      cases rs with
      | nil => simp only [List.length_cons,List.length_nil] at hlen; omega_arith
      | cons h tail =>
        obtain ⟨⟨ht,hcore,htc,hcc⟩,next⟩ := hc
        change RelCT isa (Two (Stage (n+1) (lo::h::tail)))
          (.seq (AdxTri8.rowStep i lo h tail) (AdxTri8.rows n (i+1) (tail++[lo]))) _
        refine RelCT.seq (two_post (rowStep_ct hr hlen hi htc hcc) (rowStep_stage hr hlen hi)) ?_
        apply ih (i+1) (tail++[lo]) (rotate_regs hr) _ (by omega_arith) next
        simp only [List.length_cons] at hlen
        simp only [List.length_append,List.length_cons,List.length_nil]; omega_arith

theorem checks_six : Checks 6 1 (AdxTri8.rotate AdxTri8.columns) := by
  refine ⟨⟨_,_,by taint_decide,by taint_decide⟩,?_⟩
  refine ⟨⟨_,_,by taint_decide,by taint_decide⟩,?_⟩
  refine ⟨⟨_,_,by taint_decide,by taint_decide⟩,?_⟩
  refine ⟨⟨_,_,by taint_decide,by taint_decide⟩,?_⟩
  refine ⟨⟨_,_,by taint_decide,by taint_decide⟩,?_⟩
  exact ⟨⟨_,_,by taint_decide,by taint_decide⟩,True.intro⟩

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8BlockCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

def BlockState (ps : List (Nat × Nat)) (a : Nat) (L : CtLayout) (s : State) : Prop :=
  HeadState L s ∧ Ops s.mem L.B L.w ps ∧ L.e=slot L.w a+8*L.I

def CoreReady (L : CtLayout) (s : State) : Prop := HeadState L s ∧ s.gpr .rbp=off L.B L.e

theorem setup_ct_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (L : CtLayout) (s : State)
    (h : BlockState ps a L s) : WP isa (.block (AdxTri8.setup ca)) s (CoreReady L) := by
  obtain ⟨⟨mi,hg,hI⟩,hv,he⟩ := h
  refine WP.mono (setup_ok hg.scr hg.rdi L.hZ hv pa hI) fun t ⟨pt,mt,kt⟩ => ?_
  exact ⟨⟨mi,⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,mt ▸ hI⟩,he ▸ pt⟩

/-- `CoreReady` with the output base in `rcx`, as `clearEnds` leaves it. -/
def Ready0 (L : CtLayout) (s : State) : Prop :=
  CoreReady L s ∧ s.gpr .rcx=off L.B (slot L.w aAcc+16*L.I)

/-- The stores of `clearEnds`, at addresses from `rcx`. -/
def EndStores : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0),.store (AdxRotate8.at_ .rcx 16) .rax])
    (.block [.store (AdxRotate8.at_ .rcx 136) .rax])

theorem clearEnds_fw (L : CtLayout) (s : State) (h : CoreReady L s) :
    WP isa AdxTri8.clearEnds s (Ready0 L) := by
  obtain ⟨⟨mi,hg,hI⟩,hp⟩ := h
  have hi := L.hi
  have hZ := L.hZ
  refine WP.mono (clearEnds_ok hg.scr hg.rdi hg.hdr L.hZ hI (by have := slot_le (w := L.w) (show aTmp < 8 by decide); unfold slot aAcc aTmp at *; omega_arith)) fun t ⟨_,_,_,ot,ct,kt⟩ => ?_
  refine ⟨⟨⟨mi,⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ot (by unfold slot; omega_arith)⟩,?_⟩,(kt.gpr (by decide)).trans hp⟩,ct⟩
  rw [ot.word (by unfold slot hdrBytes sFn; omega_arith) (by decide)]; exact hI

theorem clearEnds_ct
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rcx]) EndStores hint).isSome=true) :
    RelCT isa (Two CoreReady) AdxTri8.clearEnds (Two Ready0) := by
  refine two_post ?_ clearEnds_fw
  unfold AdxTri8.clearEnds
  refine RelCT.seq (two_piece (Ψ := fun L s => s.gpr .rcx=off L.B (slot L.w aAcc+16*L.I))
    [.rdi] (fun L s t hs ht => head_pins L s t hs.1 ht.1) (by taint_decide) ?_) (two_taint [.rcx] ?_ hT)
  · rintro L s ⟨⟨mi,hg,hI⟩,_⟩
    exact WP.mono (headBases_ok hg.scr hg.rdi hg.hdr L.hZ hI) fun _ h => h.1
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.trans ht.symm

theorem row0Core_head (L : CtLayout) (s : State) (h : Ready0 L s) :
    WP isa (.block (AdxTri8.row0Core [.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15])) s (Based L) := by
  obtain ⟨⟨⟨mi,hg,hI⟩,hp⟩,hc⟩ := h
  have he := L.he
  have hr := columns_regs
  refine WP.mono (row0Core_ok _ hg.scr hp (by simp only [List.length_cons,List.length_nil]; omega_arith)
    (by decide) hr.1 (fun r h => let q := hr.2 r h; ⟨q.1,q.2.1,q.2.2.1,q.2.2.2.1⟩)) fun t ⟨_,kt⟩ => ?_
  have dr : t.gpr .rdi=s.gpr .rdi := kt.gpr (by decide)
  have cr : t.gpr .rcx=s.gpr .rcx := kt.gpr (by decide)
  exact ⟨⟨mi,⟨hg.scr.congr kt.2.2.2,dr.trans hg.rdi,kt.2.1 ▸ hg.hdr⟩,kt.2.1 ▸ hI⟩,cr.trans hc⟩

theorem rowStep0_ct
    {hint htail : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rcx]) (AdxTri8.storeHead 0 .r8 .r9) htail).isSome=true)
    (hC : (taint.check (Taint.ofRegs [.rbp])
      (.block (AdxTri8.row0Core [.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15])) hint).isSome=true) :
    RelCT isa (Two Ready0) (AdxTri8.rowStep0 .r8 .r9 [.r10,.r11,.r12,.r13,.r14,.r15])
      (fun _ _ => True) := by
  unfold AdxTri8.rowStep0
  refine RelCT.seq (two_piece [.rbp] ?_ hC row0Core_head) ?_
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.1.2.trans ht.1.2.symm
  exact storeHead_ct 0 .r8 .r9 hT

theorem rowStep0_stage (L : CtLayout) (s : State) (h : Ready0 L s) :
    WP isa (AdxTri8.rowStep0 .r8 .r9 [.r10,.r11,.r12,.r13,.r14,.r15]) s
      (Stage 6 (AdxTri8.rotate AdxTri8.columns) L) := by
  obtain ⟨⟨⟨mi,hg,hI⟩,hp⟩,hc⟩ := h
  have he := L.he; have hiL := L.hi; have hZ := L.hZ
  have hr := columns_regs
  have bound : slot L.w aAcc+16*L.I+(16+8*(2*0+2))+8≤L.Z := by
    unfold slot aAcc at *; omega_arith
  refine WP.mono (rowStep0_ok hg.scr hc hp (by simp only [List.length_cons,List.length_nil]; omega_arith)
    bound hr.1 hr.2) fun t ⟨_,ot,kt⟩ => ?_
  have dr : t.gpr .rdi=L.B := (kt.gpr (by decide)).trans hg.rdi
  have pr : t.gpr .rbp=off L.B L.e := (kt.gpr (by decide)).trans hp
  have ht := hg.hdr.of_outside ot (by unfold slot; omega_arith)
  have it : word t.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.I := by
    rw [ot.word (by unfold slot hdrBytes sFn; omega_arith) (by decide)]; exact hI
  have cr : t.gpr .rcx=s.gpr .rcx := kt.gpr (by decide)
  exact ⟨⟨⟨mi,⟨hg.scr.congr kt.2.2,dr,ht⟩,it⟩,pr⟩,cr.trans hc⟩

theorem block_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) hint).isSome=true) :
    RelCT isa (Two (BlockState ps a)) (AdxTri8.block ca) (fun _ _ => True) := by
  unfold AdxTri8.block
  refine RelCT.seq (two_piece [.rdi] ?_ hS (setup_ct_fw pa)) ?_
  · intro L s t hs ht
    exact head_pins L s t hs.1 ht.1
  exact RelCT.seq (clearEnds_ct (by taint_decide))
    (RelCT.seq (two_post (rowStep0_ct (by taint_decide) (by taint_decide)) rowStep0_stage)
      (rows_ct 6 1 (AdxTri8.rotate AdxTri8.columns) (rotate_regs columns_regs) (by decide) (by decide)
        checks_six))

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8BlocksCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout LoopState GoodV)

def AtBlock (ps : List (Nat × Nat)) (p : Layout × Nat) (s : State) : Prop := p.2<p.1.n ∧ LoopState ps p.1 p.2 s

theorem block_loop_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp) (p : Layout × Nat) (s : State) (h : AtBlock ps p s) :
    WP isa (AdxTri8.block ca) s (AtBlock ps p) := by
  obtain ⟨hk,mi,hg,hv,hI⟩ := h
  have wn := p.1.hwN
  refine WP.mono (block_ok hg.scr hg.rdi hg.hdr p.1.hZ hv pa ha ha1 ha2 (by omega_arith) hI)
    fun t ⟨_,ot,kt⟩ => ?_
  refine ⟨hk,mi,⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ot (by unfold slot; omega_arith)⟩,
    hv.of_outside ot (by unfold slot sFn hdrBytes; omega_arith),?_⟩
  rw [ot.word (by unfold slot hdrBytes sFn; omega_arith) (by decide)]; exact hI

theorem block_loop_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) hint).isSome=true) :
    RelCT isa (Two (AtBlock ps)) (AdxTri8.block ca) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨⟨L,k⟩,⟨hk,mi,gs,vs,is⟩,⟨_,mj,gt,vt,it⟩⟩ es et
  dsimp only at hk
  have wn := L.hwN
  have sa := slot_le (w := L.w) ha
  have hi : 8*k+8≤L.w := by omega_arith
  have hZ := L.hZ
  let C : CtLayout := ⟨L.B,L.Z,L.w,8*k,slot L.w a+8*(8*k),L.hZ,hi,by omega_arith⟩
  exact block_ct pa hS s t ts tt s' t' ⟨C,⟨⟨mi,gs,is⟩,vs,rfl⟩,⟨⟨mj,gt,it⟩,vt,rfl⟩⟩ es et

theorem step_loop_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) hint).isSome=true) :
    RelCT isa (Two (AtBlock ps)) (.seq (AdxTri8.block ca) (.block AdxTri8.nextBlock)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (block_loop_ct pa ha hS) (block_loop_fw pa ha ha1 ha2))
    (two_taint [.rdi] ?_ (by taint_decide))
  rintro p s t ⟨_,mi,hs,_⟩ ⟨_,mj,ht,_⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

theorem step_loop_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp) (L : Layout) (k : Nat) (s : State) (hk : k<L.n) (h : LoopState ps L k s) :
    WP isa (.seq (AdxTri8.block ca) (.block AdxTri8.nextBlock)) s fun t =>
      isa.eval .ne t=some (decide (k+1<L.n)) ∧
      (k+1<L.n → LoopState ps L (k+1) t) ∧ (k+1=L.n → GoodV ps L t) := by
  refine WP.seq (WP.mono (block_loop_fw pa ha ha1 ha2 (L,k) s ⟨hk,h⟩) fun u ⟨_,mi,hg,hv,hI⟩ => ?_)
  dsimp only at hg hI
  have wn := L.hwN
  have hw := L.hw
  have nowrap := hg.scr.nowrap
  refine WP.mono (AdxTiledProduct.nextRow_ok hg.scr hg.rdi hg.hdr L.hZ (by omega_arith) (by omega_arith) hI)
    fun t ⟨mt,zt,kt⟩ => ?_
  have ot : Outside L.B (8*sFn 12) 8 u.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by decide)
  have ft : Frm L.B (AdxTiledProduct.ranges L.w) u.mem t.mem := by
    intro x hx
    apply ot x
    have := hx (8*sFn 12,32) (by simp [AdxTiledProduct.ranges]); omega_arith
  have gt : Good t L.B L.Z L.w mi :=
    ⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,AdxTiledProduct.frame_hdr hg.hdr ft⟩
  have vt := AdxTiledProduct.frame_ops hv ft
  refine ⟨?_,fun _ => ⟨mi,gt,vt,?_⟩,fun _ => ⟨⟨mi,gt⟩,vt⟩⟩
  · simp only [eval,zt,Option.map_some]
    by_cases he : k+1=L.n
    · simp only [show 8*k+8=L.w by omega_arith,decide_true,Bool.not_true,show ¬(k+1<L.n) by omega_arith,decide_false]
    · simp only [show ¬(8*k+8=L.w) by omega_arith,decide_false,Bool.not_false,show k+1<L.n by omega_arith,decide_true]
  · rw [mt,word_writeW_self,show 8*(k+1)=8*k+8 by omega_arith]

theorem blocks_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) hint).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTri8.blocks ca) (Two (GoodV ps)) := by
  unfold AdxTri8.blocks
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) AdxTiledProduct.rows_init_fw)
    (two_loop (fun L : Layout => L.n) (step_loop_ct pa ha ha1 ha2 hS) (step_loop_fw pa ha ha1 ha2))
  rintro L s t ⟨⟨mi,hs⟩,_⟩ ⟨⟨mj,ht⟩,_⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTiledSquareRawCrossCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout GoodV pins_goodV setup_fw save_fw)

theorem rawCross_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup ca)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) h₂).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) h₃).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledSquare.rawCross ca) (fun _ _ => True) := by
  unfold AdxTiledSquare.rawCross
  refine RelCT.seq (two_piece (Ψ := GoodV ps) [.rdi] (pins_goodV ps) hS
    fun L s h => WP.mono (setup_fw pa L s h) fun _ ht => ht.1) ?_
  have mapGood : ∀ L s, GoodV ps L s → GoodW ⟨L.B,L.Z,L.w⟩ s := by
    rintro L s ⟨⟨mi,hg⟩,_⟩; exact ⟨mi,hg,L.hZ⟩
  refine RelCT.seq (two_post (two_map (fun L : Layout => (⟨L.B,L.Z,L.w⟩ : Ws)) mapGood AdxHeader.save_ct) save_fw) ?_
  exact RelCT.seq (RelCT.seq (AdxTri8.blocks_ct pa ha ha1 ha2 hT) (rowsChoice_ct pa ha ha1 ha2 hR))
    (two_map (fun L : Layout => (⟨L.B,L.Z,L.w⟩ : Ws)) mapGood AdxHeader.restore_ct)

theorem rawCrossBare_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup ca)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) h₂).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) h₃).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledSquare.rawCrossBare ca) (fun _ _ => True) := by
  unfold AdxTiledSquare.rawCrossBare
  refine RelCT.seq (two_piece (Ψ := GoodV ps) [.rdi] (pins_goodV ps) hS
    fun L s h => WP.mono (setup_fw pa L s h) fun _ ht => ht.1) ?_
  have mapGood : ∀ L s, GoodV ps L s → GoodW ⟨L.B,L.Z,L.w⟩ s := by
    rintro L s ⟨⟨mi,hg⟩,_⟩; exact ⟨mi,hg,L.hZ⟩
  exact RelCT.seq (RelCT.seq (AdxTri8.blocks_ct pa ha ha1 ha2 hT) (rowsChoice_ct pa ha ha1 ha2 hR))
    (two_map (fun L : Layout => (⟨L.B,L.Z,L.w⟩ : Ws)) mapGood AdxHeader.clear_ct)

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

end

end

/-! ## AdxTiledSquareRawCT -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout GoodV pins_goodV)

theorem rawCross_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp) (L : Layout) (s : State) (h : GoodV ps L s) :
    WP isa (AdxTiledSquare.rawCross ca) s (GoodV ps L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact WP.mono (rawCross_ok hg.scr hg.rdi hg.hdr hv pa L.hZ L.hw L.hwN L.hn ha ha1 ha2)
    fun _ ⟨_,_,o,k⟩ => AdxTiledProduct.GoodV.of_outside ⟨⟨mi,hg⟩,hv⟩ o k

def Ready (ps : List (Nat × Nat)) (a : Nat) (L : Layout) (s : State) : Prop :=
  GoodV ps L s ∧ s.gpr .r8=off L.B (slot L.w aAcc+16) ∧
    s.gpr .r9=off L.B (slot L.w a) ∧ s.gpr .rbx=BitVec.ofNat 64 L.w

theorem setup_ready {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (L : Layout) (s : State)
    (h : GoodV ps L s) : WP isa (.block (Adx.setup ca)) s (Ready ps a L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact WP.mono (adxSetupV_ok hg.scr hg.rdi hg.hdr L.hZ (hv.at pa) (hv.lt pa)) fun _ ⟨p9,_,p8,pbx,m,k⟩ =>
    ⟨⟨⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,m ▸ hv⟩,p8,p9,pbx⟩

theorem raw_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup ca)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) h₂).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) h₃).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledSquare.rawSquare ca) (fun _ _ => True) := by
  unfold AdxTiledSquare.rawSquare AdxTiledSquare.diagonal
  refine RelCT.seq (two_post (rawCross_ct pa ha ha1 ha2 hS hR hT) (rawCross_fw pa ha ha1 ha2)) ?_
  refine RelCT.seq (two_piece [.rdi] (pins_goodV ps) hS (setup_ready pa)) ?_
  refine two_taint [.rdi,.r8,.r9,.rbx] ?_ (by taint_decide)
  intro L s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact pins_goodV ps L s t hs.1 ht.1 .rdi (by simp)
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.2.2.1.trans ht.2.2.1.symm
  · exact hs.2.2.2.trans ht.2.2.2.symm

theorem raw_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp) (L : Layout) (s : State) (h : GoodV ps L s) :
    WP isa (AdxTiledSquare.rawSquare ca) s (GoodV ps L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact WP.mono (rawSquare_ok hg.scr hg.rdi hg.hdr L.hZ L.hwN L.hn L.hw hv pa ha ha1 ha2)
    fun _ ⟨_,_,o,k⟩ => AdxTiledProduct.GoodV.of_outside ⟨⟨mi,hg⟩,hv⟩ o k

theorem rawCrossBare_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp) (L : Layout) (s : State) (h : GoodV ps L s) :
    WP isa (AdxTiledSquare.rawCrossBare ca) s (GoodV ps L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  refine WP.mono (rawCrossBare_ok hg.scr hg.rdi hg.hdr hv pa L.hZ L.hw L.hwN L.hn ha ha1 ha2)
    fun _ ⟨_,_,fr,k⟩ => ?_
  obtain ⟨_,o₁,o₂⟩ := AdxHeader.frm_split fr
  exact AdxTiledProduct.GoodV.of_bare ⟨⟨mi,hg⟩,hv⟩ o₁ o₂ k

theorem rawBare_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup ca)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) h₂).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) h₃).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledSquare.rawSquareBare ca) (fun _ _ => True) := by
  unfold AdxTiledSquare.rawSquareBare AdxTiledSquare.diagonal
  refine RelCT.seq (two_post (rawCrossBare_ct pa ha ha1 ha2 hS hR hT) (rawCrossBare_fw pa ha ha1 ha2)) ?_
  refine RelCT.seq (two_piece [.rdi] (pins_goodV ps) hS (setup_ready pa)) ?_
  refine two_taint [.rdi,.r8,.r9,.rbx] ?_ (by taint_decide)
  intro L s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact pins_goodV ps L s t hs.1 ht.1 .rdi (by simp)
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.2.2.1.trans ht.2.2.1.symm
  · exact hs.2.2.2.trans ht.2.2.2.symm

theorem rawBare_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp) (L : Layout) (s : State) (h : GoodV ps L s) :
    WP isa (AdxTiledSquare.rawSquareBare ca) s (GoodV ps L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact WP.mono (rawSquareBare_ok hg.scr hg.rdi hg.hdr L.hZ L.hwN L.hn L.hw hv pa ha ha1 ha2)
    fun _ ⟨_,o₁,_,o₂,k⟩ => AdxTiledProduct.GoodV.of_bare ⟨⟨mi,hg⟩,hv⟩ o₁ o₂ k

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareMontCT -/
section

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
    RelCT isa (Two (GoodV ps)) (AdxTiledSquare.montSquare co ca) (fun _ _ => True) :=
  RelCT.seq (two_post (raw_ct pa ha ha1 ha2 hS hR hT) (raw_fw pa ha ha1 ha2))
    (AdxTiledProduct.redcFinish_ct (P := fun _ => ps) (L := id) (O := fun _ => o) (fun _ => po) hF)

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareDispatchCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.Bignum.X86_64

theorem aligned_ct {o a : Nat} (ho : o<8) (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup a)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a a)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup a)) h₄).isSome=true) :
    RelCT isa (Two fun L s => AdxSquare.GW L s ∧ L.w%8=0)
      (AdxTiledSquare.montSquare o a) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨L,⟨⟨⟨mi,gs,hZ⟩,sz⟩,h8⟩,⟨⟨⟨mj,gt,_⟩,_⟩,_⟩⟩ es et
  have hw := sz.lt
  have hp := sz.2.1
  let R : AdxTiledProduct.Layout := ⟨L.B,L.Z,L.w,L.w/8,hZ,hw,by omega_using [h8],by omega_using [h8, hp]⟩
  exact montSquare_ct (ps := [(o,o),(a,a),(a,a)]) (.head _) (.tail _ (.head _)) ha ha1 ha2 hS hR hF hT
    _ _ _ _ _ _ ⟨R,⟨⟨mi,gs⟩,gs.hdr.ops3 ho ha ha⟩,⟨mj,gt⟩,gt.hdr.ops3 ho ha ha⟩ es et

theorem alignedChoice_ct {o a : Nat} (ho : o<8) (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup a)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a a)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup a)) h₄).isSome=true) :
    RelCT isa (Two AdxSquare.GW) (AdxTiledSquare.alignedChoice o a) (fun _ _ => True) := by
  unfold AdxTiledSquare.alignedChoice
  refine RelCT.seq (two_piece (Ψ := fun L s => AdxSquare.GW L s ∧ s.zf=some (decide (L.w%8=0)))
    [.rdi] AdxSquare.pins_gw (by taint_decide) ?_) ?_
  · intro L s ⟨⟨mi,hg,hZ⟩,sz⟩
    exact WP.mono (AdxSquare.redcTest_ok hg.scr hg.rdi hg.hdr hZ (by have := sz.lt; omega_using [this]))
      fun _ ⟨z,m,k⟩ => ⟨⟨⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,hZ⟩,sz⟩,z⟩
  refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
  · refine two_map id (fun L s ⟨⟨h,z⟩,e⟩ => ⟨h,?_⟩) (aligned_ct ho ha ha1 ha2 hS hR hF hT)
    simp only [eval,z,Option.some.injEq,decide_eq_true_eq] at e
    exact e
  · exact two_map id (fun _ _ h => h.1.1) (AdxSquare.montSquare4_ct ho ha ha1 ha2 hS hF)

theorem choice_ct {o a : Nat} (ho : o<8) (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₀ h₁ h₃ h₄ h₅ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hM : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a a aN aAcc aTmp)) h₀).isSome=true)
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup a)) h₁).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a a)) h₄).isSome=true)
    (hTri : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup a)) h₅).isSome=true) :
    RelCT isa (Two GoodW) (AdxTiledSquare.choice o a) (fun _ _ => True) := by
  unfold AdxTiledSquare.choice
  refine RelCT.seq (two_piece (Ψ := fun L s => GoodW L s ∧ s.zf=some (decide (SizeOk L.w)))
    [.rdi] pins_goodW (by taint_decide) ?_) ?_
  · intro L s ⟨mi,hg,hZ⟩
    exact WP.mono (sizeTest_ok hg.scr hg.rdi hg.hdr hZ) fun _ ⟨z,m,k⟩ =>
      ⟨⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,hZ⟩,z⟩
  refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
  · refine two_map id (fun L s ⟨⟨h,z⟩,e⟩ => ⟨h,?_⟩) (alignedChoice_ct ho ha ha1 ha2 hS hT hF hTri)
    simp only [eval,z,Option.some.injEq,decide_eq_true_eq] at e
    exact e
  · exact two_map id (fun _ _ h => h.1.1) (montMul_ctW (by decide) (by decide) (by decide) ho ha ha hM)

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxSquareBackend -/
section

/-! The ADX Montgomery backend with specialized squaring. -/
namespace VG.Proof.Bignum.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.MlKem.X86_64

theorem tiledDispatch_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa (AdxTiledSquare.dispatch o a b) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledSquare.dispatch
  by_cases hab : a=b
  · rw [ite_eq_left hab]
    subst b
    exact AdxTiledSquare.choice_ok hs hdi hH hZ hw hw' ho ha ho1 ho2 ha1 ha2 hinv hB
  · rw [ite_eq_right hab]
    exact AdxTiledProduct.choice_ok hs hdi hH hZ hw hw' ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hinv hB

theorem tiledDispatch_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    {hc₀ hc₁ hc₂ hc₃ hc₄ hc₅ hc₆ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hM : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a b aN aAcc aTmp)) hc₀).isSome = true)
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup b)) hc₁).isSome = true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) hc₂).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) hc₃).isSome = true)
    (hA : (taint.check (Taint.ofRegs [.rdi]) (.block (setup a)) hc₄).isSome = true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a b)) hc₅).isSome = true)
    (hTri : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup a)) hc₆).isSome = true) :
    RelCT isa (Two GoodW) (AdxTiledSquare.dispatch o a b) (fun _ _ => True) := by
  unfold AdxTiledSquare.dispatch
  by_cases hab : a=b
  · rw [ite_eq_left hab]
    subst b
    exact AdxTiledSquare.choice_ct ho ha ha1 ha2 hM hA hF hT hTri
  · rw [ite_eq_right hab]
    exact AdxTiledProduct.choice_ct ho ha hb ha1 ha2 hb1 hb2 hM hS hR hF hT

/-- Montgomery multiplication with a specialized ADX square. -/
def Mont.adxSquare : Mont where
  mm := AdxTiledSquare.dispatch
  ok hg hZ hw hw' _ _ _ ho ha hb d1 d2 d3 d4 d5 d6 hinv hB :=
    WP.mono (tiledDispatch_ok hg.scr hg.rdi hg.hdr hZ hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hinv hB)
      fun t' ⟨h1, h2, h3, k⟩ => ⟨⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, h3.hdr hg.hdr⟩,
        h1, h2, h3, k⟩
  ct := by
    intro o a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact tiledDispatch_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)

end VG.Proof.Bignum.X86_64

end
