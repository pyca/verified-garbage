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

/-- A number of zero words. -/
theorem val32_eq_zero {m : Mem} {base : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ j < k, w32 m base (d + 4 * j) = 0) → val32 m base d k = 0
  | 0, _ => rfl
  | k + 1, h => by rw [val32_succ, val32_eq_zero fun j hj => h j (by omega), h k (by omega)]; rfl

/-- `x = a + G b` with `a, x < G`: `b = 0`. -/
theorem hi_zero {x a G b : Nat} (hx : x = a + G * b) (hxG : x < G) : b = 0 := by
  by_contra hb
  have := Nat.mul_le_mul_left G (show 1 ≤ b by omega)
  omega

/-- What the modulus gives: `M` in number 0 of `n_len` bytes, odd, with its
first byte not zero. -/
structure ModIn (s : State) (base : Addr) (len M : Nat) : Prop where
  val : val32 s.mem base (numAt len 0) (nw len) = M
  lo : 2 ^ (8 * (len - 1)) ≤ M
  hi : M < 2 ^ (8 * len)
  odd : M % 2 = 1

/-- `prep`: what the steps need (`LoopPre`) in the state `s₃` before `count`,
and none of them yet. -/
theorem prep_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat}
    (h : PcIn base bytes len args s) (hmod : ModIn s base len M) :
    WP isa prep s fun u => ∃ s₃ z, LoopPre s₃ base bytes len args M z ∧ StI s₃ base bytes len args M 0 u ∧
      (∀ o, numAt len 0 ≤ o → o + 4 ≤ numAt len 4 → w32 s₃.mem base o = w32 s.mem base o) ∧
      (∀ o, numAt len 4 + 4 * wp len ≤ o → o + 4 ≤ numAt len 5 → (o - numAt len 4) % 4 = 0 →
        w32 s₃.mem base o = 0) ∧
      Outside base oP (numAt len 4 + wb len - oP) s.mem s₃.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s s₃ := by
  obtain ⟨hM, hlo, hhi, hodd⟩ := hmod
  have nw' := h.scratch.nowrap
  have dims := h.dimensions
  have f5 := (h.fits (j := 5) (by decide)).2
  have hwp := wp_le_nw (len := len)
  have hl := h.lower
  have hu := h.upper
  have hwp16 : 16 ≤ wp len := by simp only [wp]; omega
  have hwl : len ≤ 4 * wp len ∧ 4 * wp len ≤ len + 3 := by simp only [wp]; omega
  have wbe := wb_eq len
  have e0 : numAt len 0 = 256 := by simp [numAt, numOff]
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp [numAt, numOff]
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp [numAt, numOff]
  -- `M` over `W'` words, its top two words `T ≠ 0` and `U`.
  have hMW : M < 2 ^ (32 * wp len) := Nat.lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by decide) (by omega))
  have hsplit := val32_append s.mem base (numAt len 0) (wp len) (nw len - wp len)
  rw [Nat.add_sub_cancel' (by omega), hM] at hsplit
  have hhi0 := hi_zero hsplit hMW
  have hMv : val32 s.mem base (numAt len 0) (wp len) = M := by rw [hsplit, hhi0, Nat.mul_zero, Nat.add_zero]
  have hupM : ∀ j < nw len - wp len, w32 s.mem base (numAt len 0 + 4 * wp len + 4 * j) = 0 := fun j hj =>
    w32_of_val32_zero hhi0 hj
  obtain ⟨k, hk⟩ : ∃ k, wp len = k + 2 := ⟨wp len - 2, by omega⟩
  have h2 := val32_top2 s.mem base (numAt len 0) k
  rw [← hk, hMv] at h2
  obtain ⟨T, hT⟩ : ∃ T, T = w32 s.mem base (numAt len 0 + 4 * (k + 1)) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = w32 s.mem base (numAt len 0 + 4 * k) := ⟨_, rfl⟩
  rw [← hT, ← hU] at h2
  have hT' : T < 2 ^ 32 := hT ▸ (s.mem.readW _ 32).isLt
  have hU' : U < 2 ^ 32 := hU ▸ (s.mem.readW _ 32).isLt
  generalize hL : val32 s.mem base (numAt len 0) k = L at h2
  have hLk : L < 2 ^ (32 * k) := hL ▸ val32_lt _ _ _ _
  have hK := Nat.two_pow_pos (32 * k)
  generalize hKd : 2 ^ (32 * k) = K at h2 hLk hK
  rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.add_assoc] at h2
  have hKW : K * 2 ^ 32 = 2 ^ (32 * (wp len - 1)) := by
    rw [← hKd, ← Nat.pow_add, show 32 * k + 32 = 32 * (wp len - 1) by omega]
  have hKW' : K * 2 ^ 32 * 2 ^ 32 = 2 ^ (32 * wp len) := by
    rw [hKW, ← Nat.pow_add, show 32 * (wp len - 1) + 32 = 32 * wp len by omega]
  have hMK : M < K * 2 ^ 32 * (T + 1) := by
    have : K * U + K ≤ K * 2 ^ 32 := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left K hU'
    rw [Nat.mul_add, Nat.mul_one]; omega
  have hlo' : 2 ^ (32 * (wp len - 1)) ≤ M := Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hlo
  have hT0 : 0 < T := by
    by_contra e
    rw [show T = 0 by omega, Nat.zero_add, Nat.mul_one, hKW] at hMK
    omega
  -- `p = 2^z`, `d`.
  obtain ⟨z, hz⟩ : ∃ z, z = lz T := ⟨_, rfl⟩
  have hz31 : z ≤ 31 := by rw [hz]; unfold lz; omega
  obtain ⟨sb1, sb2⟩ := shifted_bounds hT0 hT' (Nat.le_refl (lz T))
  rw [← hz] at sb1 sb2
  rw [ite_eq_left rfl] at sb2
  have hTz : (T + 1) * 2 ^ z ≤ 2 ^ 32 := by
    have e : 2 ^ 32 = 2 ^ (32 - z) * 2 ^ z := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    have hlt : T < 2 ^ (32 - z) := by rw [e] at sb1; exact Nat.lt_of_mul_lt_mul_right sb1
    rw [e]; exact Nat.mul_le_mul_right _ hlt
  have hdeq : T * 2 ^ z + U * 2 ^ z / 2 ^ 32 = M * 2 ^ z / 2 ^ (32 * (wp len - 1)) := by
    rw [h2, ← hKW, VG.Proof.Bignum.WordStep32.shl_div (by omega) hLk]
  have hd1 : 2 ^ 31 ≤ M * 2 ^ z / 2 ^ (32 * (wp len - 1)) := by
    rw [← hdeq]; have := Nat.div_mul_le_self (T * 2 ^ z) (2 ^ 31); omega
  have hMw : M * 2 ^ z < 2 ^ (32 * wp len) := by
    rw [← hKW']
    calc M * 2 ^ z < K * 2 ^ 32 * (T + 1) * 2 ^ z := Nat.mul_lt_mul_of_pos_right hMK (Nat.two_pow_pos z)
      _ = K * 2 ^ 32 * ((T + 1) * 2 ^ z) := by rw [Nat.mul_assoc]
      _ ≤ K * 2 ^ 32 * 2 ^ 32 := Nat.mul_le_mul_left _ hTz
  have hd2 : M * 2 ^ z / 2 ^ (32 * (wp len - 1)) < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← hKW, Nat.mul_comm (2 ^ 32), hKW']; exact hMw
  have hxm : 2 ^ (32 * (wp len - 1)) < M := by
    rcases Nat.lt_or_eq_of_le hlo' with e | e
    · exact e
    · exfalso; rw [← e, show 32 * (wp len - 1) = 32 * (wp len - 1) - 1 + 1 by omega, Nat.pow_succ] at hodd; omega
  -- `p` and `d`, then `v`.
  unfold prep
  simp only [seqs]
  refine WP.seq (WP.mono (norm_ok h (T := T) (U := U)
    (by rw [hT]; congr 1; omega) (by rw [hU]; congr 1; omega) hT0) fun u₁ ⟨P₁, D₁, O₁, K₁⟩ => ?_)
  rw [← hz] at P₁ D₁
  rw [hdeq] at D₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (by omega) (by simp only [oP]; omega))
  refine WP.seq (WP.mono (recip_ok h₁ D₁ hd1 hd2) fun u₂ ⟨V₂, O₂, K₂⟩ => ?_)
  have h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (by omega) (by simp only [oV]; omega))
  -- `x = 2^(32 (W' - 1))`.
  refine WP.seq (WP.mono (seedX_ok h₂) fun u₃ ⟨X₃, Z₃, O₃, K₃⟩ => ?_)
  have h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (by omega) (by omega))
  have hdr₃ : ∀ o, o + 4 ≤ numAt len 4 → w32 u₃.mem base o = w32 u₂.mem base o := fun o ho =>
    O₃.w32 (.inl ho) (by omega)
  -- Number 0 as in `s` up to `u₃`.
  have N₃ : ∀ o, numAt len 0 ≤ o → o + 4 ≤ numAt len 4 → w32 u₃.mem base o = w32 s.mem base o := fun o h1 h2 => by
    rw [hdr₃ o h2, O₂.w32 (.inr (by simp only [oV]; omega)) (by omega), O₁.w32 (.inr (by simp only [oP]; omega)) (by omega)]
  have M₃ : val32 u₃.mem base (numAt len 0) (wp len) = M := by
    rw [← hMv]; exact val32_congr fun j hj => N₃ _ (by omega) (by omega)
  have P₃ : w32 u₃.mem base oP = 2 ^ z := by
    rw [hdr₃ _ (by simp only [oP]; omega), O₂.w32 (.inl (by decide)) (by decide)]; exact P₁
  have L : LoopPre u₃ base bytes len args M z := ⟨h₃, hz31, P₃, hMw,
    by rw [hdr₃ _ (by simp only [oD]; omega), O₂.w32 (.inl (by decide)) (by decide)]; exact D₁, hd1,
    by rw [hdr₃ _ (by simp only [oV]; omega)]; exact V₂, M₃, X₃, hxm⟩
  refine WP.mono (count_start L) fun u I₀ => ⟨u₃, z, L, I₀, N₃, Z₃, ?_, ?_⟩
  · exact ((O₁.mono (by omega) (by simp only [oP]; omega)).trans (O₂.mono (by simp only [oP, oV]; omega)
      (by simp only [oP, oV]; omega))).trans (O₃.mono (by simp only [oP]; omega) (by simp only [oP]; omega))
  · exact (K₁.mono (by decide)).trans ((K₂.mono (by decide)).trans (K₃.mono (by decide)))

/-- `tail` after the steps: `2^(10 B) mod M`. -/
theorem fin_ok {s₃ u₄ : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M z : Nat}
    (L : LoopPre s₃ base bytes len args M z) (I₄ : StI s₃ base bytes len args M (nSteps len) u₄)
    (hM₃ : val32 s₃.mem base (numAt len 0) (nw len) = M)
    (Z₃ : ∀ o, numAt len 4 + 4 * wp len ≤ o → o + 4 ≤ numAt len 5 → (o - numAt len 4) % 4 = 0 →
      w32 s₃.mem base o = 0) :
    WP isa tail u₄ fun t =>
      val32 t.mem base (numAt len 4) (nw len) = 2 ^ (80 * Spec.Rsa.modulusWords len) % M ∧
      val32 t.mem base (numAt len 0) (nw len) = M ∧ Outside base oMask (bytes - oMask) s₃.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₃ t := by
  have h := L.pi
  have nw' := h.scratch.nowrap
  have dims := h.dimensions
  have f5 := (h.fits (j := 5) (by decide)).2
  have hwp := wp_le_nw (len := len)
  have hl := h.lower
  have hxm := L.hxm
  have wbe := wb_eq len
  have e0 : numAt len 0 = 256 := by simp [numAt, numOff]
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp [numAt, numOff]
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp [numAt, numOff]
  -- `x` and `M` over all their words.
  have M₄ : val32 u₄.mem base (numAt len 0) (nw len) = M := by
    rw [← hM₃]; exact val32_congr fun j hj => I₄.mid _ (by simp only [oQ]; omega) (by omega)
  have X₄ : val32 u₄.mem base (numAt len 4) (nw len) = val32 u₄.mem base (numAt len 4) (wp len) := by
    rw [show nw len = wp len + (nw len - wp len) by omega, val32_append,
      val32_eq_zero (d := numAt len 4 + 4 * wp len) (k := nw len - wp len) (fun j hj => by
        rw [I₄.up _ (by omega) (by omega)]; exact Z₃ _ (by omega) (by omega) (by omega)),
      Nat.mul_zero, Nat.add_zero]
  have hx₄ : val32 u₄.mem base (numAt len 4) (nw len) < val32 u₄.mem base (numAt len 0) (nw len) := by
    rw [X₄, I₄.x, M₄]; exact Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hxm)
  refine WP.mono (tail_ok I₄.pi hx₄) fun t ⟨V₅, O₅, K₅⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [V₅, X₄, I₄.x, M₄, Nat.mod_mul_mod, ← Nat.pow_add]
    congr 2
    simp only [nSteps, wb, Spec.Rsa.modulusWords, wp] at *
    omega
  · rw [O₅.val32 (.inl (by omega)) (by omega), M₄]
  · exact (I₄.out.mono (by omega) (by simp only [oMask]; omega)).trans
      (O₅.mono (by simp only [oMask]; omega) (by simp only [oMask]; omega))
  · exact (I₄.keep.mono (by decide)).trans K₅

/-- `run`: number 4 set to `2^(10 B) mod M`. -/
theorem run_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat}
    (h : PcIn base bytes len args s) (hmod : ModIn s base len M) :
    WP isa run s fun t => val32 t.mem base (numAt len 4) (nw len) = 2 ^ (80 * Spec.Rsa.modulusWords len) % M ∧
      val32 t.mem base (numAt len 0) (nw len) = M ∧ Outside base oP (bytes - oP) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nw' := h.scratch.nowrap
  have f4 := (h.fits (j := 4) (by decide)).1
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp [numAt, numOff]
  unfold run
  have dims := h.dimensions
  have wbe := wb_eq len
  refine WP.seq (WP.mono (prep_ok h hmod) fun u ⟨s₃, z, L, I₀, N₃, Z₃, O₃, K₃⟩ => ?_)
  have hM₃ : val32 s₃.mem base (numAt len 0) (nw len) = M := by
    rw [← hmod.val]; exact val32_congr fun j hj => N₃ _ (by omega) (by simp [numAt, numOff] at *; omega)
  refine WP.seq (WP.mono (stepLoop_ok L I₀) fun u₄ I₄ => ?_)
  refine WP.mono (fin_ok L I₄ hM₃ Z₃) fun t ⟨V, Mt, O, K⟩ => ⟨V, Mt, ?_, K₃.trans K⟩
  exact (O₃.mono (by omega) (by simp only [oP]; omega)).trans
    (O.mono (by simp only [oP, oMask]; omega) (by simp only [oP, oMask]; omega))

end VG.Proof.Bignum.X86.R2Words
