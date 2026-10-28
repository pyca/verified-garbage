module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.RowOp
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedWord
import VerifiedGarbage.Proof.Weierstrass.X86.InvShift
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega

/-! # The reduction of a coefficient row at a run-time width

`redSum_ok`: `InvRedSum.redSum_ok`'s numerator, with the inverse word read from the header and the
sign word kept at `signSlot`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- Writes to the header below the slots keep the context. -/
theorem Bx.keepLow {s t : State} (h : Bx L s B Z len N) {rs : List Reg} (K : Keeps rs s t)
    (edi : .edi ∉ rs) (esp : .esp ∉ rs) {o c : Nat} (O : Outside B o c s.mem t.mem)
    (hc : o + c ≤ slotBase) : Bx L t B Z len N := by
  have nw := h.nowrap
  have hZ := h.halfZ
  have e96 : halfSlot = 96 := rfl
  have e52 : slotBase = 52 := rfl
  refine ⟨h.ws.keep K edi esp (O.mono (Nat.zero_le _) (by omega)), ⟨fun j d hd => ?_, ?_, h.slots.small⟩, h.room⟩
  · have := slot_le hd
    rw [O.w32 (.inr (by omega)) (by omega)]
    exact h.slots.addr j d hd
  · rw [O.w32 (.inr (by omega)) (by omega)]
    exact h.slots.half

theorem rv_half (w : Nat) (x : Ref) (hx : x.half = 0) (d : Nat) :
    rv w { x with half := 1, byte := x.byte + d } = rv w x + 2 * w + d := by
  simp only [rv, hx]; omega

/-- `redSum acc`: `[acc] (n + 2 words) = [acc] (n + 1) + q [mo] + 2 ^ (32 (n + 1)) · sign`, with the
digit `q = [acc] · [win + 28]` and the sign of `[acc + 4 n]`, as `InvRedSum.redSum_ok` states it. -/
theorem redSum_ok {s : State} (h : Bx L s B Z len N) {acc : Ref} (hah : acc.half = 0) (hab : acc.byte = 0)
    (haz : rv (kw len) acc + 4 * (nw len + 2) ≤ Z) (hmz : rv (kw len) mo + 4 * nw len ≤ Z)
    (sep : rv (kw len) mo + 4 * nw len ≤ rv (kw len) acc ∨ rv (kw len) acc + 4 * (nw len + 2) ≤ rv (kw len) mo) :
    WP isa (redSum L acc) s fun z =>
      Bx L z B Z len N ∧ Unch B [(rv (kw len) acc, 4 * (nw len + 2)), (signSlot, 4)] s.mem z.mem ∧
      Keeps wordClob s z ∧
      val32 z.mem B (rv (kw len) acc) (nw len + 2) =
        (val32 s.mem B (rv (kw len) acc) (nw len + 1) +
          (w32 s.mem B (rv (kw len) acc) * w32 s.mem B (win + 28) % 2 ^ 32) * val32 s.mem B (rv (kw len) mo) (nw len) +
          2 ^ (32 * (nw len + 1)) *
            (if 2 ^ 31 ≤ w32 s.mem B (rv (kw len) acc + 4 * nw len) then 2 ^ 32 - 1 else 0)) %
          2 ^ (32 * (nw len + 2)) := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have ke := kw_eq len
  have ra := rv_ge (kw len) acc
  have e48 : signSlot = 48 := rfl
  have e16 : win = 16 := rfl
  have r1 : rv (kw len) { acc with half := 1 } = rv (kw len) acc + 4 * nw len := by
    have := rv_half (kw len) acc hah 0; simp only [hab, Nat.add_zero] at this ⊢; rw [this]; omega
  have r2 : rv (kw len) { acc with half := 1, byte := 4 } = rv (kw len) acc + 4 * (nw len + 1) := by
    have := rv_half (kw len) acc hah 4; simp only [hab, Nat.zero_add] at this; rw [this]; omega
  unfold redSum
  simp only [List.append_assoc]
  -- The sign mask, into `esi`.
  refine WP.seq (maskAt_ok h (x := { acc with half := 1 }) (by rw [r1]; omega) fun u₁ K₁ m₁ c₁ => ?_)
  rw [r1] at c₁
  simp only [List.cons_append, List.nil_append]
  refine wp_movS rfl fun s₂ U₂ _ => ?_
  have K₂ : Keeps [.eax, .ebx, .ecx, .edx, .esi] s s₂ := (K₁.mono (by decide)).trans (U₂.keeps.mono (by decide))
  have m₂ : s₂.mem = s.mem := by rw [U₂.mem, m₁]
  have h₂ : Bx L s₂ B Z len N := h.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _) ra haz
  have esi₂ : s₂.gpr .esi = s₂.gpr .esi := rfl
  -- The top word zeroed.
  refine zeroWord_ok h₂ (x := { acc with half := 1, byte := 4 }) (by rw [r2]; omega) fun s₃ h₃ K₃ O₃ z₃ => ?_
  rw [r2] at O₃ z₃
  -- The digit.
  refine ptr_ok h₃.ws h₃.slots hZ (r := .ebx) (t := .edx) (by decide) (by decide) (by decide) (by decide)
    (by intro e; cases e) (by omega) fun s₄ K₄ m₄ p₄ => ?_
  have h₄ : Bx L s₄ B Z len N := h₃.keep K₄ (by decide) (by decide) (by rw [m₄]; exact Outside.refl _ _ _ _) ra haz
  refine wp_movS (readSrc_ptr (h₄.ws.rt) p₄ (d := 0) (by omega)) fun s₅ U₅ _ => ?_
  have hs₅ := h₄.ws.ws.workspace.of_keeps U₅.keeps (by decide)
  refine wp_movS (readSrc_sc hs₅ (d := win + 28) (by omega)) fun s₆ U₆ _ => ?_
  refine wp_mul fun s₇ U₇ => ?_
  refine wp_movS rfl fun s₈ U₈ _ => ?_
  have K₈ : Keeps [.eax, .ecx, .edx] s₄ s₈ :=
    (((U₅.keeps.mono (by decide)).trans (U₆.keeps.mono (by decide))).trans (U₇.keeps.mono (by decide))).trans
      (U₈.keeps.mono (by decide))
  have m₈ : s₈.mem = s₄.mem := by rw [U₈.mem, U₇.mem, U₆.mem, U₅.mem]
  have hs₈ := h₄.ws.ws.workspace.of_keeps K₈ (by decide)
  refine wp_storeS (hs₈.ea (by omega)) (hs₈.write (d := signSlot) (n := 4) (by omega)) fun s₉ U₉ => WP.block_nil ?_
  have K₉ : Keeps [.eax, .ecx, .edx] s₄ s₉ := K₈.trans (U₉.keeps _)
  have O₉ : Outside B signSlot 4 s₄.mem s₉.mem := by
    rw [U₉.mem, m₈]; exact writeW32_outside _ _ _ (by omega)
  have h₉ : Bx L s₉ B Z len N := h₄.keepLow K₉ (by decide) (by decide) O₉ (by decide)
  -- The registers so far.
  have esi₈ : s₈.gpr .esi = s₂.gpr .esi := by
    rw [K₈.1 _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide)]
  have ecx₉ : (s₉.gpr .ecx).toNat =
      w32 s.mem B (rv (kw len) acc) * w32 s.mem B (win + 28) % 2 ^ 32 := by
    rw [U₉.gpr, U₈.gpr, U₇.eax, U₆.other _ (by decide), U₆.gpr, U₅.gpr, BitVec.toNat_ofNat, U₅.mem, m₄]
    have a₃ : w32 s₃.mem B (rv (kw len) acc) = w32 s.mem B (rv (kw len) acc) := by
      rw [O₃.w32 (.inl (by omega)) (by omega), m₂]
    have i₃ : w32 s₃.mem B (win + 28) = w32 s.mem B (win + 28) := by
      rw [O₃.w32 (.inl (by omega)) (by omega), m₂]
    simp only [w32, Nat.add_zero] at a₃ i₃ ⊢
    rw [a₃, i₃]
  -- The memory so far.
  have mo₀ := rv_ge (kw len) mo
  have A₉ : val32 s₉.mem B (rv (kw len) acc) (nw len + 2) = val32 s.mem B (rv (kw len) acc) (nw len + 1) := by
    rw [O₉.val32 (.inr (by omega)) (by omega), m₄, val32_succ, z₃, Nat.mul_zero, Nat.add_zero,
      O₃.val32 (.inl (by omega)) (by omega), m₂]
  have M₉ : val32 s₉.mem B (rv (kw len) mo) (nw len) = val32 s.mem B (rv (kw len) mo) (nw len) := by
    rw [O₉.val32 (.inr (by omega)) (by omega), m₄, O₃.val32 (by omega) (by omega), m₂]
  have S₉ : w32 s₉.mem B signSlot = (s₂.gpr .esi).toNat := by
    rw [U₉.mem, w32_write_self, esi₈]
  -- The row.
  have hlt : val32 s₉.mem B (rv (kw len) acc) (nw len + 0 + 2) +
      (s₉.gpr .ecx).toNat * val32 s₉.mem B (rv (kw len) mo) (nw len + 0) < 2 ^ (32 * (nw len + 0 + 2)) := by
    simp only [Nat.add_zero]
    rw [A₉]
    have a := val32_lt s.mem B (rv (kw len) acc) (nw len + 1)
    have b := val32_lt s₉.mem B (rv (kw len) mo) (nw len)
    have c := (s₉.gpr .ecx).isLt
    have P : (s₉.gpr .ecx).toNat * val32 s₉.mem B (rv (kw len) mo) (nw len) < 2 ^ 32 * 2 ^ (32 * nw len) :=
      Nat.mul_lt_mul'' c b
    rw [show nw len + 2 = (nw len + 1) + 1 by omega, pow32_succ, pow32_succ (nw len)]
    rw [pow32_succ] at a
    have := Nat.mul_le_mul_left (2 ^ 32) (Nat.one_le_two_pow (n := 32 * nw len))
    omega
  refine WP.seq (WP.mono (mulRow_ok h₉ (set := false) (acc := acc) (src := mo) (e := 0) (by decide) rfl
    (by simpa using haz) (by simpa using hmz) (by simpa using sep) fun _ => hlt) fun t ⟨Ht, Ot, Vt, Kt⟩ => ?_)
  simp only [Nat.add_zero, Bool.false_eq_true, ite_false] at Ot Vt
  rw [A₉, M₉, ecx₉] at Vt
  have St : w32 t.mem B signSlot = (s₂.gpr .esi).toNat := by
    rw [Ot.w32 (.inl (by omega)) (by omega), S₉]
  -- The sign word added at the top.
  have r2' := r2
  refine ptr_ok Ht.ws Ht.slots hZ (r := .ebx) (t := .edx) (x := { acc with half := 1, byte := 4 }) (by decide)
    (by decide) (by decide) (by decide) (by intro e; cases e) (by rw [r2]; omega) fun t₁ K₁' m₁' p₁' => ?_
  rw [r2] at p₁'
  have hw₁ := Ht.ws.rt.of_keeps K₁'
  refine wp_movS (readSrc_ptr hw₁ p₁' (d := 0) (by omega)) fun t₂ V₂ _ => ?_
  have hs₂' := (Ht.ws.ws.workspace.of_keeps K₁' (by decide)).of_keeps V₂.keeps (by decide)
  refine wp_addS (readSrc_sc hs₂' (d := signSlot) (by omega)) fun t₃ V₃ _ => ?_
  have hw₃ := (hw₁.of_keeps V₂.keeps).of_keeps V₃.keeps
  have p₃ : PtrAt t₃ B .ebx (rv (kw len) acc + 4 * (nw len + 1)) := by
    rw [PtrAt, V₃.other _ (by decide), V₂.other _ (by decide)]; exact p₁'
  have ea : t₃.ea (at_ .ebx 0) = off B (rv (kw len) acc + 4 * (nw len + 1)) := by
    simpa using ea_ptr hw₃ p₃ (d := 0) (by omega)
  refine wp_storeS ea (ws_write hw₃ (by omega)) fun z Uz => WP.block_nil ?_
  have Kz : Keeps [.eax, .ebx, .edx] t z :=
    ((K₁'.mono (by decide)).trans (V₂.keeps.mono (by decide))).trans ((V₃.keeps.mono (by decide)).trans (Uz.keeps _))
  have Oz : Outside B (rv (kw len) acc + 4 * (nw len + 1)) 4 t.mem z.mem := by
    rw [Uz.mem, V₃.mem, V₂.mem, m₁']; exact writeW32_outside _ _ _ (by omega)
  have Tz : w32 z.mem B (rv (kw len) acc + 4 * (nw len + 1)) =
      (w32 t.mem B (rv (kw len) acc + 4 * (nw len + 1)) + (s₂.gpr .esi).toNat) % 2 ^ 32 := by
    rw [Uz.mem, w32_write_self, V₃.gpr, V₂.gpr, m₁', BitVec.toNat_add, Nat.add_zero, V₂.mem, m₁', ← St]
  refine ⟨Ht.keep Kz (by decide) (by decide) Oz (by omega) (by omega), ?_, ?_, ?_⟩
  · intro x hx
    have hacc := hx (rv (kw len) acc, 4 * (nw len + 2)) (by simp)
    have hsg := hx (signSlot, 4) (by simp)
    rw [Oz x (by omega), Ot x (by simpa using hacc), O₉ x hsg, m₄, O₃ x (by omega), m₂]
  · exact (((((K₂.mono (by decide)).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))).trans
      (K₉.mono (by decide))).trans (Kt.mono (by decide))).trans (Kz.mono (by decide))
  · have E : (s₂.gpr .esi).toNat =
        if 2 ^ 31 ≤ w32 s.mem B (rv (kw len) acc + 4 * nw len) then 2 ^ 32 - 1 else 0 := by
      rw [U₂.gpr, c₁]; split <;> rfl
    rw [val32_succ, Oz.val32 (.inl (by omega)) (by omega), Tz, E]
    have H := VG.Proof.Weierstrass.X86.Inv.add_top_mod (top := w32 t.mem B (rv (kw len) acc + 4 * (nw len + 1)))
      (sign := if 2 ^ 31 ≤ w32 s.mem B (rv (kw len) acc + 4 * nw len) then 2 ^ 32 - 1 else 0)
      (Nat.two_pow_pos (32 * (nw len + 1))) (val32_lt t.mem B (rv (kw len) acc) (nw len + 1))
    rw [H, ← val32_succ, Nat.mul_comm (2 ^ (32 * (nw len + 1))) (2 ^ 32), ← pow32_succ, Vt]

end VG.Proof.Rsa.X86.InvBatchRt
