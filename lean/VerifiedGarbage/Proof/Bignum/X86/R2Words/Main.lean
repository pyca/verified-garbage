module

public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Loop
public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Norm
public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Recip
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.Double
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Stages
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.WordStep32

/-!
# `R2Words` on x86: `2^(10 B) mod M`

`seedX` sets number 4 to `2^(32 (W' - 1))` (`seedX_ok`), and `tail` doubles
it `10 B mod 32` times modulo `M` (`tail_ok`); with `norm`, `recip` and the
steps between them, `run` leaves `2^(10 B) mod M` (`run_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.R2Words

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86.PublicRt VG.Impl.Bignum.X86.R2Words VG.Proof.Bignum.X86.PrecomputeRt

/-- A word of a number that is zero. -/
theorem w32_of_val32_zero {m : Mem} {base : Addr} {d n i : Nat} (h : val32 m base d n = 0) (hi : i < n) :
    w32 m base (d + 4 * i) = 0 := by
  rw [show n = i + (n - i - 1 + 1) by omega, val32_append, Nat.add_comm (n - i - 1), val32_append, val32,
    val32] at h
  have h2 := Nat.two_pow_pos (32 * i)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.add_eq_zero_iff, Nat.mul_eq_zero, Nat.pos_iff_ne_zero.mp h2,
    false_or] at h
  exact h.2.1

/-- `seedX`: number 4 `2^(32 (W' - 1))` over `W'` words, and zero above. -/
theorem seedX_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) :
    WP isa seedX s fun t => val32 t.mem base (numAt len 4) (wp len) = 2 ^ (32 * (wp len - 1)) ∧
      (∀ o, numAt len 4 + 4 * wp len ≤ o → o + 4 ≤ numAt len 5 → (o - numAt len 4) % 4 = 0 →
        w32 t.mem base o = 0) ∧
      Outside base (numAt len 4) (wb len) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have nw' := h.scratch.nowrap
  have dims := h.dimensions
  have f4 := (h.fits (j := 4) (by decide)).1
  have hwp := wp_le_nw (len := len)
  have hl := h.lower
  have hwp16 : 16 ≤ wp len := by simp only [wp]; omega
  have wbe := wb_eq len
  have e45 : numAt len 5 = numAt len 4 + wb len := numAt_succ len 4
  unfold seedX
  refine WP.seq (WP.mono (zero_ok h (j := 4) (by decide)) fun u ⟨O, Z, K⟩ => ?_)
  have hu := h.keep K (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega))
  refine topPtr_ok hu (r := .eax) (t := .ecx) (j := 4) (i := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) fun v Kv mv pv _ => ?_
  refine wp_movS rfl fun v₁ V₁ _ => ?_
  have pv₁ : PtrAt v₁ base .eax (numAt len 4 + 4 * wp len - 4 * 1) := by rw [PtrAt, V₁.other _ (by decide)]; exact pv
  have ws₁ : Ws v₁ base bytes := hu.ws.of_wr (V₁.wr.trans Kv.2.2)
  refine wp_storeS (ea_ptr ws₁ pv₁ (d := 0) (by omega)) (ws_write ws₁ (by omega)) fun t M => WP.block_nil ?_
  have mt : t.mem = u.mem.writeW (off base (numAt len 4 + 4 * (wp len - 1))) (BitVec.ofNat 32 1) := by
    rw [M.mem, V₁.mem, mv, V₁.gpr, show numAt len 4 + 4 * wp len - 4 * 1 + 0 = numAt len 4 + 4 * (wp len - 1) by omega]
    rfl
  have Ot := writeW32_outside u.mem base (d := numAt len 4 + 4 * (wp len - 1)) (BitVec.ofNat 32 1) (by omega)
  rw [← mt] at Ot
  refine ⟨?_, fun o h1 h2 h3 => ?_, O.trans (Ot.mono (by omega) (by omega)),
    (K.mono (by decide)).trans ((Kv.mono (by decide)).trans ((V₁.keeps.mono (by decide)).trans (M.keeps _)))⟩
  · have Zw : val32 u.mem base (numAt len 4) (wp len - 1) = 0 := by
      have := Z
      rw [show nw len = (wp len - 1) + (nw len - (wp len - 1)) by omega, val32_append] at this
      omega
    rw [show wp len = wp len - 1 + 1 by omega, val32_succ, Ot.val32 (.inl (by omega)) (by omega), Zw,
      show wp len - 1 + 1 - 1 = wp len - 1 by omega, mt, w32_write_self]
    simp
  · rw [Ot.w32 (.inr (by omega)) (by omega), show o = numAt len 4 + 4 * ((o - numAt len 4) / 4) by omega]
    exact w32_of_val32_zero Z (by omega)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `add d, src`, and ZF. -/
theorem wp_addZ {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (s.gpr d + v) → t.zf = some (s.gpr d + v == 0) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .add d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

end

/-- `tail`: number 4 times `2^(10 B mod 32) = 2^(16 (B / 8 mod 2))` modulo `M`. -/
theorem tail_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s)
    (hT : val32 s.mem base (numAt len 4) (nw len) < val32 s.mem base (numAt len 0) (nw len)) :
    WP isa tail s fun t => val32 t.mem base (numAt len 4) (nw len) =
        val32 s.mem base (numAt len 4) (nw len) * 2 ^ (16 * (Spec.Rsa.modulusWords len % 2)) %
          val32 s.mem base (numAt len 0) (nw len) ∧
      Outside base (numAt len 4) (2 * wb len + 4) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nw' := h.scratch.nowrap
  have f5 := (h.fits (j := 5) (by decide)).2
  have wbe := wb_eq len
  have hb := wb_le h.upper
  have e45 : numAt len 5 = numAt len 4 + wb len := numAt_succ len 4
  have e04 : numAt len 4 = numAt len 0 + 4 * wb len := by simp only [numAt]; omega
  unfold tail
  refine WP.seq (widthB_ok h.width h.upper fun u₁ K₁ m₁ e₁ => ?_)
  refine wp_shr (by decide) fun u₂ U₂ => wp_logicS (Or.inl rfl) rfl fun u₃ U₃ => ?_
  refine wp_addS rfl fun u₄ U₄ _ => wp_addS rfl fun u₅ U₅ _ => wp_addS rfl fun u₆ U₆ _ =>
    wp_addZ rfl fun u U z => WP.block_nil ?_
  have K : Keeps [.esi] s u := K₁.trans ((((U₂.keeps.trans U₃.keeps).trans U₄.keeps).trans U₅.keeps).trans
    (U₆.keeps.trans U.keeps))
  have mu : u.mem = s.mem := by rw [U.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, m₁]
  have hu := h.keep K (by decide) (by decide) (by rw [mu]; exact Outside.refl _ _ _ _)
  have hw : wb len = 8 * Spec.Rsa.modulusWords len := rfl
  have a₃ : (u₃.gpr .esi).toNat = Spec.Rsa.modulusWords len % 2 := by
    rw [U₃.gpr, ite_eq_left rfl, BitVec.toNat_and, U₂.gpr, BitVec.toNat_ushiftRight, e₁, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod, hw]
    omega
  have hm2 : Spec.Rsa.modulusWords len % 2 < 2 := Nat.mod_lt _ (by decide)
  have a₆ : (u₆.gpr .esi).toNat = 8 * (Spec.Rsa.modulusWords len % 2) := by
    rw [U₆.gpr, BitVec.toNat_add, U₅.gpr, BitVec.toNat_add, U₄.gpr, BitVec.toNat_add, a₃]; omega
  have au : (u.gpr .esi).toNat = 16 * (Spec.Rsa.modulusWords len % 2) := by
    rw [U.gpr, BitVec.toNat_add, a₆]; omega
  have zu : u.zf = some (decide (Spec.Rsa.modulusWords len % 2 = 0)) := by
    have ue : u.gpr .esi = BitVec.ofNat 32 (16 * (Spec.Rsa.modulusWords len % 2)) :=
      BitVec.eq_of_toNat_eq (by rw [au, BitVec.toNat_ofNat]; omega)
    rw [z, ← U.gpr, ue]
    rcases (show Spec.Rsa.modulusWords len % 2 = 0 ∨ Spec.Rsa.modulusWords len % 2 = 1 by omega) with e | e <;>
      rw [e] <;> rfl
  refine WP.ite _ zu (fun e => ?_) (fun e => ?_)
  · simp only [decide_eq_true_eq] at e
    refine WP.block_nil ⟨?_, by rw [mu]; exact Outside.refl _ _ _ _, K.mono (by decide)⟩
    rw [mu, e, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hT]
  · simp only [decide_eq_false_iff_not] at e
    have e1 : Spec.Rsa.modulusWords len % 2 = 1 := by omega
    rw [e1]
    rw [e1] at au
    refine WP.mono (countLoop (N := 16) (by decide) (fun j v => PcIn base bytes len args v ∧
        val32 v.mem base (numAt len 4) (nw len) = val32 s.mem base (numAt len 4) (nw len) * 2 ^ j %
          val32 s.mem base (numAt len 0) (nw len) ∧
        val32 v.mem base (numAt len 0) (nw len) = val32 s.mem base (numAt len 0) (nw len) ∧
        (v.gpr .esi).toNat = 16 - j ∧ Outside base (numAt len 4) (2 * wb len + 4) s.mem v.mem ∧
        Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v) ?_
      ⟨hu, by rw [mu, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hT], by rw [mu], by rw [au],
        by rw [mu]; exact Outside.refl _ _ _ _, K.mono (by decide)⟩) fun t ⟨_, V, _, _, O, Kt⟩ => ⟨V, O, Kt⟩
    rintro j v hj ⟨hv, V, Mv, Ev, Ov, Kv⟩
    refine WP.mono (doubleStep_ok hv (by rw [V, Mv]; exact Nat.mod_lt _ (by omega))) fun w ⟨Ow, Vw, ew, zw, dw, Kw⟩ => ?_
    have Kw' := Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp, .esi]) Kw dw
    obtain ⟨c₁, c₂⟩ := VG.Proof.Bignum.X86.PublicRt.count1_zf (N := 16) (x := v.gpr .esi) Ev hj
    have Mw : val32 w.mem base (numAt len 0) (nw len) = val32 s.mem base (numAt len 0) (nw len) := by
      rw [Ow.val32 (.inl (by omega)) (by omega), Mv]
    refine ⟨⟨hv.keep Kw' (by decide) (by decide) (Ow.mono (by omega) (by omega)), ?_, Mw, by rw [ew, c₁],
      Ov.trans Ow, Kv.trans Kw'⟩, by rw [zw, c₂]⟩
    rw [Vw, V, Mv, ← Nat.two_mul, Nat.mul_mod_mod, Nat.pow_succ]
    congr 1; rw [Nat.mul_comm 2, Nat.mul_assoc]

end VG.Proof.Bignum.X86.R2Words
