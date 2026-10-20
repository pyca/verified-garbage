module
public import VerifiedGarbage.Proof.Dsa.Arm.RandomFrame
public import VerifiedGarbage.Proof.Dsa.RandomBytes

import VerifiedGarbage.Proof.Dsa.Arm.RandomScan
import VerifiedGarbage.Proof.Dsa.RandomEncoding

/-!
# Preparing to sample (32-bit ARM)

`prepare` clears the 32 bytes of the nonce, scans q, and stores the address
of its significant bytes (`oQ`), their count (`oWidth`) and the leading
byte's mask (`oMask`, `mask_ok`); `r0 = 1` exactly when q > 1 (`Prepared`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp op2_imm op2_reg op2_lsr eval_eq eval_ne
  ofNat_beq_zero toNat_shr)
open VG.Proof.Dsa (maskValue)

/-! ## The mask -/

theorem shr_beq_zero (x : BitVec 32) (k : Nat) : (x >>> k == 0) = decide (x.toNat < 2 ^ k) := by
  have e : ∀ z : BitVec 32, z = 0 ↔ z.toNat = 0 :=
    fun z => ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, e, toNat_shr, Nat.div_eq_zero_iff]
  have := Nat.two_pow_pos k
  omega

/-- One threshold of the mask. -/
theorem maskStep_ok {k bits n : Nat} (hk : 1 ≤ k ∧ k ≤ 31) (hb : encodable (BitVec.ofNat 32 bits) = true)
    {s u : State} {Q : State → Prop} (hd : (u.gpr .r4).toNat = n) (R : Rest [.r0, .r5] s u) (hm : u.mem = s.mem)
    (cont : ∀ t, t.gpr .r5 = (if n < 2 ^ k then BitVec.ofNat 32 bits else u.gpr .r5) →
      (t.gpr .r4).toNat = n → Rest [.r0, .r5] s t → t.mem = s.mem → Q t) :
    WP isa (maskStep k bits) u Q := by
  unfold maskStep
  refine WP.seq (wp_mov (op2_lsr hk) fun u₀ v₀ => wp_cmp0 fun u₁ f₁ z₁ => WP.block_nil ?_)
  rw [v₀.gpr, shr_beq_zero, hd] at z₁
  have R₁ : Rest [.r0, .r5] s u₁ := R.trans ((v₀.rest (by decide)).trans (f₁.rest _))
  have d₁ : (u₁.gpr .r4).toNat = n := by rw [f₁.gpr, v₀.other _ (by decide), hd]
  have m₁ : u₁.mem = s.mem := by rw [f₁.mem, v₀.mem, hm]
  by_cases h : n < 2 ^ k
  · refine WP.ite true (by rw [eval_eq, z₁, decide_eq_true h]) (fun _ =>
      wp_mov (op2_imm hb) fun u₂ v₂ => WP.block_nil ?_) (fun e => Bool.noConfusion e)
    exact cont u₂ (by rw [v₂.gpr]; simp only [h, ↓reduceIte]) (by rw [v₂.other _ (by decide), d₁])
      (R₁.trans (v₂.rest (by decide))) (by rw [v₂.mem, m₁])
  · refine WP.ite false (by rw [eval_eq, z₁, decide_eq_false h]) (fun e => Bool.noConfusion e)
      (fun _ => WP.block_nil ?_)
    exact cont u₁ (by simp only [h, ↓reduceIte]; rw [f₁.gpr, v₀.other _ (by decide)]) d₁ R₁ m₁

theorem mask_ok {s : State} {n : Nat} (hd : (s.gpr .r4).toNat = n) :
    WP isa mask s fun t => t.gpr .r5 = maskValue n ∧ t.mem = s.mem ∧ Rest [.r0, .r5] s t := by
  unfold mask
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₀ u₀ => WP.block_nil ?_)
  have d₀ : (s₀.gpr .r4).toNat = n := by rw [u₀.other _ (by decide), hd]
  refine WP.seq (maskStep_ok (by decide) (by decide) d₀ (u₀.rest (by decide)) u₀.mem fun s₁ e₁ d₁ k₁ m₁ =>
    WP.seq (maskStep_ok (by decide) (by decide) d₁ k₁ m₁ fun s₂ e₂ d₂ k₂ m₂ =>
    WP.seq (maskStep_ok (by decide) (by decide) d₂ k₂ m₂ fun s₃ e₃ d₃ k₃ m₃ =>
    WP.seq (maskStep_ok (by decide) (by decide) d₃ k₃ m₃ fun s₄ e₄ d₄ k₄ m₄ =>
    WP.seq (maskStep_ok (by decide) (by decide) d₄ k₄ m₄ fun s₅ e₅ d₅ k₅ m₅ =>
    WP.seq (maskStep_ok (by decide) (by decide) d₅ k₅ m₅ fun s₆ e₆ d₆ k₆ m₆ =>
    maskStep_ok (by decide) (by decide) d₆ k₆ m₆ fun s₇ e₇ _ k₇ m₇ => ?_))))))
  refine ⟨?_, m₇, k₇⟩
  rw [e₇, e₆, e₅, e₄, e₃, e₂, e₁, u₀.gpr]
  rfl

theorem or_shr_beq (x y : BitVec 32) :
    ((x >>> 1) ||| (y >>> 1) == 0) = decide (x.toNat < 2 ∧ y.toNat < 2) := by
  have e : ∀ z : BitVec 32, z = 0 ↔ z.toNat = 0 :=
    fun z => ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, e, BitVec.toNat_or, Nat.or_eq_zero_iff, toNat_shr, toNat_shr]
  omega

/-- Store the mask, and set `r0 = 1` exactly when the scan's width or
leading byte is at least two. -/
theorem prepareFinish_ok {s₀ t : State} (h : RReady s₀ t) {w : Nat} {b : Byte} (hw : w < 2 ^ 32)
    (h3 : t.gpr .r3 = BitVec.ofNat 32 w) (h4 : t.gpr .r4 = b.setWidth 32) :
    WP isa prepareFinish t fun u =>
      u.gpr .r0 = (if 2 ≤ w ∨ 2 ≤ b.toNat then 1 else 0) ∧
      u.mem = t.mem.writeW (off (rBase s₀) oMask) (maskValue b.toNat) ∧ RReady s₀ u ∧
      Rest [.r0, .r5, .r7] t u := by
  unfold prepareFinish
  refine WP.seq (WP.mono (mask_ok (n := b.toNat) (by rw [h4, VG.Proof.Dsa.toNat_setWidth8]))
    fun s₁ ⟨e₁, m₁, k₁⟩ => ?_)
  have h₁ := h.congr k₁ (by rw [m₁]; exact Frame.refl _ _)
  refine WP.seq (wp_st h₁ (by decide) fun s₂ u₂ h₂ => wp_mov (op2_lsr (by decide)) fun s₃ u₃ =>
    wp_mov (op2_lsr (by decide)) fun s₄ u₄ => wp_dp (op2_reg _ _) fun s₅ u₅ =>
    wp_cmp0 fun s₆ f₆ z₆ => WP.block_nil ?_)
  have e3 : s₂.gpr .r3 = BitVec.ofNat 32 w := by rw [u₂.gpr, k₁.gpr _ (by decide), h3]
  have e4 : s₂.gpr .r4 = b.setWidth 32 := by rw [u₂.gpr, k₁.gpr _ (by decide), h4]
  rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide),
    show VG.Proof.X25519.Arm.dpVal .orr (s₂.gpr .r3 >>> 1) (s₂.gpr .r4 >>> 1) =
      (s₂.gpr .r3 >>> 1) ||| (s₂.gpr .r4 >>> 1) from rfl, or_shr_beq, e3, e4, VG.Proof.Dsa.toNat_setWidth8,
    VG.Proof.X25519.Arm.toNat_imm hw] at z₆
  have R₆ : Rest [.r0, .r5, .r7] t s₆ := (k₁.mono (by decide)).trans ((u₂.rest _).trans
    ((u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans (f₆.rest _)))))
  have m₆ : s₆.mem = t.mem.writeW (off (rBase s₀) oMask) (maskValue b.toNat) := by
    rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, e₁, m₁]
  have h₆ : RReady s₀ s₆ :=
    (((h₂.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide)).fupd f₆
  by_cases hs : w < 2 ∧ b.toNat < 2
  · refine WP.ite true (by rw [eval_eq, z₆, decide_eq_true hs]) (fun _ =>
      wp_mov (op2_imm (by decide)) fun s₇ u₇ => WP.block_nil ?_) (fun e => Bool.noConfusion e)
    exact ⟨by rw [u₇.gpr]; exact (ite_eq_right_of_eq_false _ _ (eq_false (by omega))).symm, by rw [u₇.mem, m₆], h₆.upd u₇, R₆.trans (u₇.rest (by decide))⟩
  · refine WP.ite false (by rw [eval_eq, z₆, decide_eq_false hs]) (fun e => Bool.noConfusion e) (fun _ =>
      wp_mov (op2_imm (by decide)) fun s₇ u₇ => WP.block_nil ?_)
    exact ⟨by rw [u₇.gpr]; exact (ite_eq_left_of_eq_true _ _ (eq_true (by omega))).symm, by rw [u₇.mem, m₆], h₆.upd u₇, R₆.trans (u₇.rest (by decide))⟩

/-! ## Clearing the nonce -/

/-- The memory after clearing the first `k` words of the nonce. -/
def clearMem (m : Mem) (B : Addr) : Nat → Mem
  | 0 => m
  | k + 1 => (clearMem m B k).writeW (off B (oNonce + 4 * k)) (0 : BitVec 32)

theorem zeroWord_at (m : Mem) (B : Addr) (d i : Nat) (hi : i < 4) :
    (m.writeW (off B d) (0 : BitVec 32)) (off B (d + i)) = 0 := by
  have he : off B (d + i) = off B d + BitVec.ofNat 64 i := by
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  rw [he]
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq, Mem.sub_ofNat_toNat (off B d) (i := i) (by omega),
    show 32 / 8 = 4 from rfl, hi, ite_true]
  exact BitVec.extractLsb'_zero

theorem clearMem_outside (m : Mem) (B : Addr) : ∀ k, k ≤ 8 → Outside B oNonce 32 m (clearMem m B k)
  | 0, _ => Outside.refl _ _ _ _
  | k + 1, hk => (clearMem_outside m B k (by omega)).trans
      ((writeW32_outside _ B (d := oNonce + 4 * k) 0 (by unfold oNonce; omega)).mono
        (by unfold oNonce; omega) (by unfold oNonce; omega))

theorem clearMem_zero (m : Mem) (B : Addr) : ∀ k, k ≤ 8 → ∀ i < 4 * k, clearMem m B k (off B (oNonce + i)) = 0
  | 0, _, i, hi => absurd hi (by omega)
  | k + 1, hk, i, hi => by
    by_cases hlo : i < 4 * k
    · rw [clearMem, writeW32_outside _ B (d := oNonce + 4 * k) 0 (by unfold oNonce; omega) _
        (by rw [ofs_off0 B (by unfold oNonce; omega)]; omega)]
      exact clearMem_zero m B k (by omega) i hlo
    · rw [clearMem, show oNonce + i = oNonce + 4 * k + (i - 4 * k) by omega]
      exact zeroWord_at _ B _ _ (by omega)

theorem clearWords_ok {s₀ t : State} (h : RReady s₀ t) (h0 : t.gpr .r0 = 0) : ∀ k ≤ 8,
    WP isa (.block ((List.range k).map fun i => st .r0 (oNonce + 4 * i))) t fun u =>
      RReady s₀ u ∧ u.mem = clearMem t.mem (rBase s₀) k ∧ Rest [] t u
  | 0, _ => WP.block_nil ⟨h, rfl, Rest.refl _ _⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine VG.Proof.X25519.Arm.WP.append (clearWords_ok h h0 k (by omega)) fun u ⟨hu, mu, Ru⟩ =>
      wp_st hu (by unfold oNonce frameBytes; omega) fun v mv hv => WP.block_nil ⟨hv, ?_, Ru.trans (mv.rest _)⟩
    rw [mv.mem, mu, Ru.gpr _ (by simp), h0]
    rfl

theorem clearNonce_ok {s₀ t : State} (h : RReady s₀ t) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, RReady s₀ u → u.mem = clearMem t.mem (rBase s₀) 8 → Rest [.r0] t u → u.gpr .r0 = 0 →
      WP isa (.block is) u Q) :
    WP isa (.block (clearNonce ++ is)) t Q := by
  unfold clearNonce
  rw [List.cons_append]
  refine wp_mov (op2_imm (by decide)) fun u₀ v₀ =>
    VG.Proof.X25519.Arm.WP.append (clearWords_ok (h.upd v₀) v₀.gpr 8 (Nat.le_refl _)) fun u ⟨hu, mu, Ru⟩ =>
      k u hu (by rw [mu, v₀.mem]) ((v₀.rest (by simp)).trans (Ru.mono (by simp))) (by rw [Ru.gpr _ (by simp), v₀.gpr])

/-! ## Preparing -/

/-- What `prepare` leaves, with q > 1. -/
structure Prepared (s₀ u : State) : Prop where
  ready : RReady s₀ u
  q : slot u.mem (rBase s₀) oQ = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀)
  width : slot u.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀)
  mask : slot u.mem (rBase s₀) oMask = maskValue (rLead s₀).toNat
  nonce : ∀ i < 32, u.mem (off (rBase s₀) (oNonce + i)) = 0

theorem add_ofNat_sub32 (a : BitVec 32) {k d : Nat} (hd : d ≤ k) (hk : k < 2 ^ 32) :
    a + BitVec.ofNat 32 k - BitVec.ofNat 32 d = a + BitVec.ofNat 32 (k - d) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := a.isLt
  rw [Nat.mod_eq_of_lt (a := k) hk, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (a := k - d) (by omega)]
  omega

abbrev prepareRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r7]

theorem prepare_ok {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t)
    (hk : slot t.mem (rBase s₀) oKey = s₀.gpr .r3) :
    WP isa prepare t fun u =>
      u.gpr .r0 = (if 1 < rq s₀ then 1 else 0) ∧ (1 < rq s₀ → Prepared s₀ u) ∧ RReady s₀ u ∧
      Outs (rBase s₀) [(oQ, 12), (oNonce, 32)] t.mem u.mem ∧ Rest prepareRegs t u := by
  have hfit := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have e2 : stackArg s₀ 2 = BitVec.ofNat 32 (rQBytes s₀).length := by
    rw [hqn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold prepare
  refine WP.seq (clearNonce_ok h fun t₁ h₁ m₁ k₁ _ => ?_)
  have hk₁ : slot t₁.mem (rBase s₀) oKey = s₀.gpr .r3 := by
    rw [m₁, slot_outs (Outs.of_outside (clearMem_outside t.mem _ 8 (by decide)) (List.mem_singleton_self _))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; decide), hk]
  refine wp_ld h₁ (by decide) fun t₂ u₂ => wp_ldArg A (h₁.upd u₂) (j := 1) (by decide) fun t₃ u₃ =>
    wp_dp (op2_reg _ _) fun t₄ u₄ => wp_ldArg A ((h₁.upd u₂).upd u₃ |>.upd u₄) (j := 2) (by decide)
      fun t₅ u₅ => WP.block_nil ?_
  have h₅ := (((h₁.upd u₂).upd u₃).upd u₄).upd u₅
  have r1₅ : t₅.gpr .r1 = rQ s₀ := by
    rw [u₅.other _ (by decide), u₄.gpr]
    show t₃.gpr .r1 + t₃.gpr .r0 = _
    rw [u₃.other _ (by decide), u₃.gpr, u₂.gpr, hk₁]; rfl
  have r2₅ : t₅.gpr .r2 = BitVec.ofNat 32 (rQBytes s₀).length := by rw [u₅.gpr, e2]
  have R₅ : Rest prepareRegs t t₅ := (k₁.mono (by decide)).trans ((u₂.rest (by decide)).trans
    ((u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans (u₅.rest (by decide)))))
  have m₅ : t₅.mem = clearMem t.mem (rBase s₀) 8 := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  refine WP.seq (WP.mono (significant_ok r1₅ r2₅ (h₅.q A) (rQBytes_pos A) (by omega))
    fun t₆ ⟨r3₆, r4₆, m₆, k₆⟩ => ?_)
  have h₆ : RReady s₀ t₆ := h₅.congr k₆ (by rw [m₆]; exact Frame.refl _ _)
  have hk₆ : slot t₆.mem (rBase s₀) oKey = s₀.gpr .r3 := by rw [m₆, m₅, ← m₁]; exact hk₁
  refine WP.seq (wp_ld h₆ (by decide) fun t₇ u₇ => wp_ldArg A (h₆.upd u₇) (j := 1) (by decide) fun t₈ u₈ =>
    wp_dp (op2_reg _ _) fun t₉ u₉ => wp_ldArg A (((h₆.upd u₇).upd u₈).upd u₉) (j := 2) (by decide)
      fun t₁₀ u₁₀ => wp_dp (op2_reg _ _) fun t₁₁ u₁₁ => wp_dp (op2_reg _ _) fun t₁₂ u₁₂ => ?_)
  have h₁₂ := (((((h₆.upd u₇).upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂
  have r3₁₂ : t₁₂.gpr .r3 = BitVec.ofNat 32 (rWidth s₀) := by
    rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), r3₆]
  have r4₁₂ : t₁₂.gpr .r4 = (rLead s₀).setWidth 32 := by
    rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), r4₆]
  have r1₁₂ : t₁₂.gpr .r1 = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀) := by
    rw [u₁₂.gpr]
    show t₁₁.gpr .r1 - t₁₁.gpr .r3 = _
    rw [u₁₁.gpr, u₁₁.other .r3 (by decide)]
    show t₁₀.gpr .r1 + t₁₀.gpr .r0 - t₁₀.gpr .r3 = _
    rw [u₁₀.gpr, u₁₀.other .r1 (by decide), u₁₀.other .r3 (by decide), u₉.gpr, u₉.other .r3 (by decide)]
    show t₈.gpr .r1 + t₈.gpr .r0 + stackArg s₀ 2 - t₈.gpr .r3 = _
    rw [u₈.gpr, u₈.other .r1 (by decide), u₈.other .r3 (by decide), u₇.gpr, u₇.other .r3 (by decide), hk₆, r3₆,
      e2, add_ofNat_sub32 _ hfit (by omega)]
    rfl
  refine wp_st h₁₂ (by decide) fun t₁₃ v₁₃ h₁₃ => wp_st h₁₃ (by decide) fun t₁₄ v₁₄ h₁₄ => WP.block_nil ?_
  have e3 : t₁₄.gpr .r3 = BitVec.ofNat 32 (rWidth s₀) := by rw [v₁₄.gpr, v₁₃.gpr, r3₁₂]
  have e4 : t₁₄.gpr .r4 = (rLead s₀).setWidth 32 := by rw [v₁₄.gpr, v₁₃.gpr, r4₁₂]
  refine WP.mono (prepareFinish_ok h₁₄ (w := rWidth s₀) (b := rLead s₀)
    (show (VG.Proof.Dsa.significant (rQBytes s₀)).1 < 2 ^ 32 by omega) e3 e4) fun u ⟨ax, mu, hu, ku⟩ => ?_
  -- Memory.
  have m₁₂ : t₁₂.mem = clearMem t.mem (rBase s₀) 8 := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, m₆, m₅]
  have mu' : u.mem = (((clearMem t.mem (rBase s₀) 8).writeW (off (rBase s₀) oQ)
      (rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀))).writeW (off (rBase s₀) oWidth)
      (BitVec.ofNat 32 (rWidth s₀))).writeW (off (rBase s₀) oMask) (maskValue (rLead s₀).toNat) := by
    rw [mu, v₁₄.mem, v₁₃.mem, v₁₃.gpr, r1₁₂, r3₁₂, m₁₂]
  have kregs : Rest prepareRegs t u := by
    refine (R₅.trans (k₆.mono (by decide))).trans ?_
    refine (((((((u₇.rest (by decide)).trans (u₈.rest (by decide))).trans (u₉.rest (by decide))).trans
      (u₁₀.rest (by decide))).trans (u₁₁.rest (by decide))).trans (u₁₂.rest (by decide))).trans
      ((v₁₃.rest _).trans (v₁₄.rest _))).trans (ku.mono (by decide))
  have e := VG.Proof.Dsa.random_valid_scan_ge (rQBytes s₀)
  refine ⟨by simp only [ax, e], fun _ => ⟨hu, ?_, ?_, ?_, ?_⟩, hu, ?_, kregs⟩
  · rw [mu', slot_write_ne _ _ _ (by unfold oQ oMask; omega) (by decide) (by decide),
      slot_write_ne _ _ _ (by unfold oQ oWidth; omega) (by decide) (by decide), slot_write_self]
  · rw [mu', slot_write_ne _ _ _ (by unfold oWidth oMask; omega) (by decide) (by decide), slot_write_self]
  · rw [mu', slot_write_self]
  · intro i hi
    have ho : ∀ d, d + 4 ≤ oNonce → ofs (rBase s₀) (off (rBase s₀) (oNonce + i)) < d ∨
        d + 4 ≤ ofs (rBase s₀) (off (rBase s₀) (oNonce + i)) := fun d hd => by
      rw [ofs_off0 _ (by unfold oNonce; omega)]; omega
    rw [mu', writeW32_outside _ _ (d := oMask) _ (by decide) _ (ho _ (by decide)),
      writeW32_outside _ _ (d := oWidth) _ (by decide) _ (ho _ (by decide)),
      writeW32_outside _ _ (d := oQ) _ (by decide) _ (ho _ (by decide))]
    exact clearMem_zero _ _ 8 (by decide) i (by omega)
  · rw [mu']
    exact (((Outs.of_outside (clearMem_outside t.mem (rBase s₀) 8 (by decide)) (by decide)).trans
      (store_in _ _ (d := oQ) _ (o := oQ) (n := 12) (by decide) (by decide) (by decide) (by decide))).trans
      (store_in _ _ (d := oWidth) _ (o := oQ) (n := 12) (by decide) (by decide) (by decide) (by decide))).trans
      (store_in _ _ (d := oMask) _ (o := oQ) (n := 12) (by decide) (by decide) (by decide) (by decide))

end VG.Proof.Dsa.Arm
