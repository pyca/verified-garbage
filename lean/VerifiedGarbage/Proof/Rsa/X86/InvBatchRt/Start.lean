module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Red
public import VerifiedGarbage.Proof.Weierstrass.X86.InvLoop
import VerifiedGarbage.Proof.Weierstrass.X86.InvMatrix
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Framework.Omega

/-! # The start of a batch at a run-time width

`start_ok`: the window's low words from `[4]` and `[5]`, and the identity matrix.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob wordState atWord)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- The window's low words and identity matrix. -/
theorem start_ok {s : State} (h : Bx L s B Z len N) :
    WP isa (.block (start L)) s fun u =>
      Bx L u B Z len N ∧
      wordState u.mem B win =
        ⟨s.mem.readW (off B win) 32, s.mem.readW (off B (rv (kw len) (a 4))) 32,
          s.mem.readW (off B (rv (kw len) (a 5))) 32, 1, 0, 0, 1⟩ ∧
      Keeps wordClob s u ∧ Outside B (win + 4) 24 s.mem u.mem := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hf16 := h.fits16
  have e16 : win = 16 := rfl
  have r4 := rv_a len 4; have r5 := rv_a len 5
  unfold start
  simp only [List.append_assoc]
  -- `[win + 4] = [a 4]`.
  refine ptr_ok h.ws h.slots hZ (r := .ebx) (t := .edx) (by decide) (by decide) (by decide) (by decide)
    (by intro e; cases e) (by omega) fun s₁ K₁ m₁ p₁ => ?_
  simp only [List.cons_append, List.nil_append]
  have H₁ : Bx L s₁ B Z len N := h.keep K₁ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₁]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega)
  refine wp_movS (readSrc_ptr H₁.ws.rt p₁ (d := 0) (by omega)) fun s₂ U₂ _ => ?_
  have hs₂ := H₁.ws.ws.workspace.of_keeps U₂.keeps (by decide)
  refine wp_storeS (hs₂.ea (by omega)) (hs₂.write (d := win + 4) (n := 4) (by omega)) fun s₃ U₃ => ?_
  have K₃ : Keeps [.eax, .ebx, .edx] s s₃ :=
    ((K₁.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (U₃.keeps _)
  have O₃ : Outside B (win + 4) 4 s.mem s₃.mem := by
    rw [U₃.mem, U₂.mem, m₁]; exact writeW32_outside _ _ _ (by omega)
  have H₃ : Bx L s₃ B Z len N := h.keepLow K₃ (by decide) (by decide) O₃ (by decide)
  have F₃ : w32 s₃.mem B (win + 4) = w32 s.mem B (rv (kw len) (a 4)) := by
    rw [U₃.mem, w32_write_self, U₂.gpr, m₁, Nat.add_zero]
  -- `[win + 8] = [a 5]`.
  refine ptr_ok H₃.ws H₃.slots hZ (r := .ebx) (t := .edx) (x := a 5) (by decide) (by decide) (by decide)
    (by decide) (by intro e; cases e) (by omega) fun s₄ K₄ m₄ p₄ => ?_
  have H₄ : Bx L s₄ B Z len N := H₃.keep K₄ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₄]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega)
  refine wp_movS (readSrc_ptr H₄.ws.rt p₄ (d := 0) (by omega)) fun s₅ U₅ _ => ?_
  have hs₅ := H₄.ws.ws.workspace.of_keeps U₅.keeps (by decide)
  refine wp_storeS (hs₅.ea (by omega)) (hs₅.write (d := win + 8) (n := 4) (by omega)) fun s₆ U₆ => ?_
  have K₆ : Keeps [.eax, .ebx, .edx] s₃ s₆ :=
    ((K₄.mono (by decide)).trans (U₅.keeps.mono (by decide))).trans (U₆.keeps _)
  have O₆ : Outside B (win + 8) 4 s₃.mem s₆.mem := by
    rw [U₆.mem, U₅.mem, m₄]; exact writeW32_outside _ _ _ (by omega)
  have H₆ : Bx L s₆ B Z len N := H₃.keepLow K₆ (by decide) (by decide) O₆ (by decide)
  have G₆ : w32 s₆.mem B (win + 8) = w32 s.mem B (rv (kw len) (a 5)) := by
    rw [U₆.mem, w32_write_self, U₅.gpr, m₄, Nat.add_zero, ← O₃.w32 (d := rv (kw len) (a 5)) (by omega) (by omega)]
  -- The identity matrix.
  refine WP.mono (VG.Proof.Weierstrass.X86.Inv.setMatrix_ok H₆.ws.ws.workspace (dst := win + 12) (by omega))
    fun u ⟨U, V, Q, R, K₇, O₇⟩ => ?_
  have H₇ : Bx L u B Z len N := H₆.keepLow K₇ (by decide) (by decide) O₇ (by decide)
  refine ⟨H₇, ?_, ((K₃.trans K₆).trans (K₇.mono (by decide))).mono (by decide), ?_⟩
  · have D : w32 u.mem B win = w32 s.mem B win := by
      rw [O₇.w32 (by omega) (by omega), O₆.w32 (by omega) (by omega), O₃.w32 (by omega) (by omega)]
    have F : w32 u.mem B (win + 4) = w32 s.mem B (rv (kw len) (a 4)) := by
      rw [O₇.w32 (by omega) (by omega), O₆.w32 (by omega) (by omega), F₃]
    have G : w32 u.mem B (win + 8) = w32 s.mem B (rv (kw len) (a 5)) := by
      rw [O₇.w32 (by omega) (by omega), G₆]
    simp only [wordState, atWord, Divstep.W32.WSt.mk.injEq, Nat.reduceMul, Nat.add_zero]
    refine ⟨BitVec.eq_of_toNat_eq D, BitVec.eq_of_toNat_eq F, BitVec.eq_of_toNat_eq G,
      BitVec.eq_of_toNat_eq U, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem B (win + 16) = 0
      simpa only [Nat.add_assoc, Nat.reduceAdd] using V
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem B (win + 20) = 0
      simpa only [Nat.add_assoc, Nat.reduceAdd] using Q
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem B (win + 24) = 1
      simpa only [Nat.add_assoc, Nat.reduceAdd] using R
  · intro x hx
    rw [O₇ x (by omega), O₆ x (by omega), O₃ x (by omega)]

end VG.Proof.Rsa.X86.InvBatchRt
