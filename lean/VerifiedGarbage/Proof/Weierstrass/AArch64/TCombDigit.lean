import VerifiedGarbage.Impl.Weierstrass.AArch64.TComb
import VerifiedGarbage.Proof.Weierstrass.CombW
import VerifiedGarbage.Proof.Weierstrass.AArch64.CombDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb

/-!
# The comb from tables in memory on AArch64: digits

Iteration `j` reads window `j` (of `w` bits) of the scalar from its table of
bits: `x16` points at it (`winIndex_ok`), Horner's rule adds its bits
(`hornerBits_ok`, `hornerVal_eq`), and `|k_j - H|` is its magnitude
(`magnitudeH_ok`); `digitW_ok` is all three. The sign of the digit is the
complement of the window's top bit (`signMaskW_ok`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- `x16 = x0 + w x19`. -/
theorem winIndex_ok (s : State) {base : Addr} {size : Nat} (hs : Scr s base size) {w j : Nat}
    (hw : w < 65536) (hb : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block (winIndex w)) s fun t => t.gpr .x16 = off base (w * j) ∧ Keeps [.x16] s t := by
  apply WP.of_runBlock
  simp only [winIndex, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits from by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq,
    ite_false, reduceCtorEq, hb, hs.x0, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [off]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      Nat.shiftLeft_eq, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
    simp only [Size.bits, Nat.mod_eq_of_lt (show w < 2 ^ 16 by omega), Nat.mod_mod]
    rw [← Nat.mul_mod, Nat.mul_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

/-- `Σ_{i<k} v (d + i) 2^i`. -/
def hornerVal (v : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | d, k + 1 => 2 * hornerVal v (d + 1) k + v d

theorem hornerVal_lt {v : Nat → Nat} (hv : ∀ i, v i ≤ 1) : ∀ d k, hornerVal v d k < 2 ^ k
  | _, 0 => Nat.one_pos
  | d, k + 1 => by
    have := hornerVal_lt hv (d + 1) k
    have := hv d
    simp only [hornerVal, Nat.pow_succ]; omega

/-- `x2 = Σ_{i<k} b_i 2^i` for the bytes `b_i` (0 or 1) at `x16 + d + i`. -/
theorem hornerBits_ok {v : Nat → Nat} (hv : ∀ i, v i ≤ 1) :
    ∀ (k d : Nat) {s : State}, k < 64 → d + k ≤ 4096 →
      (∀ i < k, InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (d + i)) 1 ∧
        s.mem (s.gpr .x16 + BitVec.ofNat 64 (d + i)) = BitVec.ofNat 8 (v (d + i))) →
      WP isa (.block (hornerBits d k)) s fun t =>
        t.gpr .x2 = BitVec.ofNat 64 (hornerVal v d k) ∧ Keeps [.x2, .x4] s t
  | 0, d, s, _, _, _ => by
    apply WP.of_runBlock
    simp only [hornerBits, runBlock_cons, runStep_some, runBlock_nil, exec,
      show 16 * 0 < Size.x.bits from by decide, ite_true, RegUpd.gpr_write_self,
      BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨by rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr.1
  | k + 1, d, s, hk, hd, hb => by
    rw [hornerBits, WP.block_append_iff]
    refine WP.mono (hornerBits_ok hv k (d + 1) (by omega) (by omega) fun i hi => by
      rw [show d + 1 + i = d + (i + 1) by omega]; exact hb (i + 1) (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
    have h16 : s₁.gpr .x16 = s.gpr .x16 := k₁.gpr _ (by decide)
    obtain ⟨hr, hm⟩ := hb 0 (by omega)
    rw [Nat.add_zero] at hr hm
    have hlt := hornerVal_lt hv (d + 1) k
    have hk2 : 2 ^ k < 2 ^ 63 := Nat.pow_lt_pow_right (by decide) (by omega)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, State.load, addr,
      Size.bits, Nat.mod_one, show d < 4096 * 1 by omega, and_self, ite_true, h16,
      k₁.rd, k₁.wr, k₁.mem, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
      hr, read1_zext, hm, BitVec.setWidth_eq, ite_false, reduceCtorEq, e₁, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r hr' => ?_, k₁.mem, k₁.rd, k₁.wr, k₁.sp⟩⟩
    · apply BitVec.eq_of_toNat_eq
      have := hv d
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, hornerVal]
      rw [Nat.mod_eq_of_lt (by omega : v d % 2 ^ 8 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : v d < 2 ^ 8),
        Nat.mod_eq_of_lt (by omega : hornerVal v (d + 1) k < 2 ^ 64)]
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [RegUpd.gpr_write, hr'.1, hr'.2, ite_false]
      exact k₁.gpr r (by simpa using hr')

/-- The window from its bits. -/
theorem hornerVal_eq (k w j : Nat) :
    ∀ i ≤ w, hornerVal (fun t => (k.testBit t).toNat) (w * j + (w - i)) i =
      k / 2 ^ (w * j + (w - i)) % 2 ^ i := by
  intro i
  induction i with
  | zero => intro _; simp [hornerVal, Nat.mod_one]
  | succ i ih =>
    intro hi
    have e := ih (by omega)
    rw [show w * j + (w - i) = w * j + (w - (i + 1)) + 1 by omega] at e
    simp only [hornerVal, e]
    generalize w * j + (w - (i + 1)) = t
    have hq : k / 2 ^ (t + 1) = k / 2 ^ t / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    have hb : (k.testBit t).toNat = k / 2 ^ t % 2 := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ t) with h | h <;> simp [h]
    rw [hq, hb, Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, Nat.mod_mul]
    omega

/-- `|v - H|`, the magnitude of the digit of the window `v`. -/
def magH (H v : Nat) : Nat := if H ≤ v then v - H else H - v

private theorem magH_fact : ∀ w < 9, ∀ v < 2 ^ w,
    (BitVec.ofNat 64 v - BitVec.ofNat 64 (2 ^ (w - 1)) ^^^
        (((0 : BitVec 16).setWidth 64 <<< (16 * 0)) -
          (BitVec.ofNat 64 v - BitVec.ofNat 64 (2 ^ (w - 1))) >>> 63)) -
      (((0 : BitVec 16).setWidth 64 <<< (16 * 0)) -
        (BitVec.ofNat 64 v - BitVec.ofNat 64 (2 ^ (w - 1))) >>> 63) =
      BitVec.ofNat 64 (magH (2 ^ (w - 1)) v) := by
  decide +kernel

/-- `x2 = |v - H|` from the window `v` in `x2`, for `H = 2^(w-1)`, `w ≤ 8`. -/
theorem magnitudeH_ok (s : State) {w v : Nat} (hw : w < 9) (hv : v < 2 ^ w)
    (hx : s.gpr .x2 = BitVec.ofNat 64 v) :
    WP isa (.block (magnitudeH (2 ^ (w - 1)))) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (magH (2 ^ (w - 1)) v) ∧ Keeps [.x2, .x3, .x4, .x9] s t := by
  have hH : 2 ^ (w - 1) < 4096 := Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide)
    (show w - 1 ≤ 7 by omega)) (by decide)
  apply WP.of_runBlock
  simp only [magnitudeH, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits, hH,
    show (63 : Nat) < 64 from by decide, show 16 * 0 < 64 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨magH_fact w hw v hv, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- The window's top bit says whether its digit is not negative. -/
theorem testBit_top (k w j : Nat) (hw : 1 ≤ w) :
    k.testBit (w * j + (w - 1)) = decide (2 ^ (w - 1) ≤ combWin w k j) := by
  have hl := combWin_lt w k j
  rw [Nat.add_comm, ← Nat.testBit_div_two_pow, combWin]
  rw [show k / 2 ^ (w * j) = k / 2 ^ (w * j) % 2 ^ w + 2 ^ w * (k / 2 ^ (w * j) / 2 ^ w) from
    (Nat.mod_add_div _ _).symm]
  rw [combWin] at hl
  generalize k / 2 ^ (w * j) % 2 ^ w = r at hl ⊢
  generalize k / 2 ^ (w * j) / 2 ^ w = q
  have hw' : 2 ^ w = 2 ^ (w - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  rw [Nat.testBit_eq_decide_div_mod_eq, hw', Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
  have h2 : r / 2 ^ (w - 1) < 2 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
  rw [Nat.add_mul_mod_self_left]
  have hr : (r + 2 ^ (w - 1) * (2 * q)) % (2 ^ (w - 1) * 2) = r := by
    rw [← Nat.mul_assoc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [hr]
  by_cases h : 2 ^ (w - 1) ≤ r
  · have : r / 2 ^ (w - 1) = 1 := by
      have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by omega : 1 * 2 ^ (w - 1) ≤ r)
      omega
    simp [this, h]
  · have : r / 2 ^ (w - 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [this, h]

/-- `x3` all ones if digit `j = x19` is negative: the top bit of its window is
clear. -/
theorem signMaskW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (w bits : Nat) {k j N : Nat} (hw1 : 1 ≤ w) (hw : w < 65536) (hj : w * j + w ≤ N)
    (hN : bits + N ≤ size) (hbw : bits + w - 1 < 4096) (hx : s.gpr .x19 = BitVec.ofNat 64 j)
    (hbits : ∀ t < N, s.mem (off base (bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block (signMaskW w bits)) s fun t =>
      t.gpr .x3 = bmask (decide (combWin w k j < 2 ^ (w - 1))) ∧ Keeps [.x3, .x16] s t := by
  have hn := hs.nowrap
  rw [signMaskW, WP.block_append_iff]
  refine WP.mono (winIndex_ok s hs hw hx) fun a ⟨a16, ka⟩ => ?_
  have hr : InRegions (a.rd ++ a.wr) (off base (bits + (w * j + (w - 1)))) 1 :=
    ⟨_, List.mem_append_right _ (ka.wr ▸ hs.wr), hs.contains (by omega) (by decide)⟩
  have he : a.gpr .x16 + BitVec.ofNat 64 (bits + w - 1) = off base (bits + (w * j + (w - 1))) := by
    rw [a16, off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact congrArg (base + ·) (congrArg _ (by omega))
  have hv : ((a.mem.read (off base (bits + (w * j + (w - 1)))) 1).setWidth 32).setWidth 64 =
      (((if k.testBit (w * j + (w - 1)) then 1 else 0 : BitVec 8)).setWidth 32).setWidth 64 := by
    rw [read1_zext, ka.mem, hbits _ (by omega)]
    rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.load, addr, Size.bits, RegUpd.gpr_write, BitVec.setWidth_eq, Nat.mod_one,
    show bits + w - 1 < 4096 * 1 by omega, show (1 : Nat) < 4096 by decide,
    and_self, he, hr, hv, ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, ka.mem, ka.rd, ka.wr, ka.sp⟩⟩
  · rw [sign_byte, testBit_top k w j hw1]
    by_cases h : 2 ^ (w - 1) ≤ combWin w k j
    · simp [h, show ¬ combWin w k j < 2 ^ (w - 1) by omega]
    · simp [h, show combWin w k j < 2 ^ (w - 1) by omega]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, ite_false]
    exact ka.gpr r (by simpa using hr.2)

theorem hornerVal_congr {v v' : Nat → Nat} : ∀ {d d' k : Nat}, (∀ i < k, v (d + i) = v' (d' + i)) →
    hornerVal v d k = hornerVal v' d' k
  | _, _, 0, _ => rfl
  | d, d', k + 1, h => by
    simp only [hornerVal]
    rw [hornerVal_congr (d := d + 1) (d' := d' + 1) (k := k) fun i hi => by
      rw [show d + 1 + i = d + (i + 1) by omega, show d' + 1 + i = d' + (i + 1) by omega]
      exact h (i + 1) (by omega)]
    have := h 0 (by omega)
    simp only [Nat.add_zero] at this
    rw [this]

/-- The magnitude of digit `j = x19` into `x2`: `|k_j - H|` of window `j` of
`k`, from its table of bits at `bits`. -/
theorem digitW_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {k j N : Nat} (hw1 : 1 ≤ K.w) (hw : K.w < 9) (hj : K.w * j + K.w ≤ N) (hN : K.bits + N ≤ size)
    (hbw : K.bits + K.w ≤ 4096) (hx : s.gpr .x19 = BitVec.ofNat 64 j)
    (hbits : ∀ t < N, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block K.digit) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (magH K.H (combWin K.w k j)) ∧ Keeps [.x2, .x3, .x4, .x9, .x16] s t := by
  have hn := hs.nowrap
  rw [TCombCfg.digit, List.append_assoc, WP.block_append_iff]
  refine WP.mono (winIndex_ok s hs (by omega) hx) fun a ⟨a16, ka⟩ => ?_
  rw [WP.block_append_iff]
  have hv : ∀ i, (fun t => (k.testBit (K.w * j + (t - K.bits))).toNat) i ≤ 1 := fun _ => Bool.toNat_le _
  refine WP.mono (hornerBits_ok hv K.w K.bits (s := a) (by omega) hbw fun i hi => ?_)
    fun b ⟨b2, kb⟩ => ?_
  · have he : a.gpr .x16 + BitVec.ofNat 64 (K.bits + i) = off base (K.bits + (K.w * j + i)) := by
      rw [a16, off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact congrArg (base + ·) (congrArg _ (by omega))
    refine ⟨by rw [he]; exact ⟨_, List.mem_append_right _ (ka.wr ▸ hs.wr), hs.contains (by omega) (by decide)⟩, ?_⟩
    rw [he, ka.mem, hbits _ (by omega), show K.bits + i - K.bits = i by omega]
    cases k.testBit (K.w * j + i) <;> rfl
  · have hw' : hornerVal (fun t => (k.testBit (K.w * j + (t - K.bits))).toNat) K.bits K.w = combWin K.w k j := by
      have := hornerVal_eq k K.w j K.w (Nat.le_refl _)
      rw [Nat.sub_self, Nat.add_zero] at this
      rw [combWin, ← this]
      exact hornerVal_congr fun i _ => by simp only [show K.bits + i - K.bits = i by omega]
    have hlt := combWin_lt K.w k j
    refine WP.mono (magnitudeH_ok b hw hlt (by rw [b2, hw'])) fun t ⟨t2, kt⟩ =>
      ⟨t2, ((Keeps.regs ka).mono (by decide)).trans ((Keeps.regs kb).mono (by decide)) |>.trans
        ((Keeps.regs kt).mono (by decide)) |> fun h => ⟨h.gpr, kt.mem.trans (kb.mem.trans ka.mem), h.rd, h.wr, h.sp⟩⟩

end VG.Proof.Weierstrass.AArch64
