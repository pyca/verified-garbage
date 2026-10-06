import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Spec.Rsa.Contract

/-!
# RSA on AArch64: BoringSSL's limits on the public exponent

`expCheck` leaves 1 in `x9` exactly when `e` is within BoringSSL's limits
(`Spec.Rsa.exponentValid`), and 0 if not, keeping memory and every register
but `x9`–`x17` and the flags (`expCheck_ok`); `failOut` writes zeros to
`out` and returns 0 (`failOut_ok`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Checked
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep read_one count_loop)
open VG.WriteBytes (writeW8_apply)

/-! ## Arithmetic -/

/-- `x`, saturated at `2^34 - 1` from `2^33`. -/
def sat (x : Nat) : Nat := if x < 2 ^ 33 then x else 2 ^ 34 - 1

theorem sat_lt (x : Nat) : sat x < 2 ^ 34 := by unfold sat; split <;> omega

theorem sat_step (x b : Nat) (hb : b < 256) : sat (256 * sat x + b) = sat (256 * x + b) := by
  unfold sat; split <;> (try split) <;> (try split) <;> omega

theorem exponentValid_sat (x : Nat) : Spec.Rsa.exponentValid (sat x) = Spec.Rsa.exponentValid x := by
  unfold sat
  split
  · rfl
  · rename_i h
    rw [show Spec.Rsa.exponentValid (2 ^ 34 - 1) = false from by decide]
    simp only [Spec.Rsa.exponentValid, h, decide_false, Bool.and_false]

theorem exec_cselc_x' (s : State) {d n m : Reg} {cond : CondCode} :
    exec (.cselc .x d n m cond) s = some (s.write .x d (if cond.holds s then s.gpr n else s.gpr m)) := rfl

theorem zf_awc (s : State) (d : Reg) (a b : BitVec 64) (c : Bool) :
    (s.addWithCarry .x d a b c).zf = decide (a + b + BitVec.ofNat 64 c.toNat = 0) := rfl

/-- The next byte shifted in. -/
theorem step_v {x : Nat} (hx : x < 2 ^ 34) (b : Byte) :
    BitVec.ofNat 64 x <<< 8 + BitVec.setWidth 64 (BitVec.setWidth 32 b) = BitVec.ofNat 64 (256 * x + b.toNat) := by
  have hb := b.isLt
  have hx' := hx
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, byte_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega)]
  omega

theorem shr33 {v : Nat} (hv : v < 2 ^ 64) : BitVec.ofNat 64 v >>> 33 = BitVec.ofNat 64 (v / 2 ^ 33) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem zero_test {q : Nat} (hq : q < 2 ^ 64) :
    decide (BitVec.ofNat 64 q + 0 + BitVec.ofNat 64 false.toNat = 0) = decide (q = 0) := by
  have e : BitVec.ofNat 64 q + 0 + BitVec.ofNat 64 false.toNat = BitVec.ofNat 64 q := by simp
  rw [e]
  apply decide_eq_decide.mpr
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  rfl

/-! ## `expCheck` -/

/-- One byte of `e`: `sat x` becomes `sat (256 x + b)`. -/
theorem expStep_ok {t : State} {ep : Addr} {L j x : Nat} {b : Byte} (h4 : t.gpr .x4 = ep)
    (h5 : t.gpr .x5 = BitVec.ofNat 64 L) (h11 : t.gpr .x11 = BitVec.ofNat 64 j)
    (h10 : t.gpr .x10 = BitVec.ofNat 64 (sat x)) (h16 : t.gpr .x16 = BitVec.ofNat 64 (2 ^ 34 - 1))
    (h17 : t.gpr .x17 = 0) (hj : j < L) (hL : L < 2 ^ 63)
    (ha : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 j) 1) (hb : t.mem (ep + BitVec.ofNat 64 j) = b) :
    WP isa (.block expStep) t fun t' => t'.gpr .x10 = BitVec.ofNat 64 (sat (256 * x + b.toNat)) ∧
      t'.gpr .x11 = BitVec.ofNat 64 (j + 1) ∧ ((t'.gpr .x14).toNat ≠ 0 ↔ j + 1 ≠ L) ∧ t'.mem = t.mem ∧
      Keep [.x10, .x11, .x12, .x13, .x14] t t' := by
  have hv : 256 * sat x + b.toNat < 2 ^ 64 := by have := sat_lt x; have := b.isLt; omega
  rw [show expStep = ([.lsl .x .x10 .x10 8, .add .x .x12 .x4 .x11, .ldrb .x12 .x12 0, .add .x .x10 .x10 .x12,
      .lsr .x .x13 .x10 33] : List Instr) ++ ([.adds .x .x13 .x13 .x17] : List Instr) ++
      ([.cselc .x .x10 .x10 .x16 .eq] : List Instr) ++ ([.addImm .x .x11 .x11 1, .sub .x .x14 .x5 .x11] : List Instr)
      from rfl, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.x10, .x12, .x13] (Q := fun t₁ =>
      t₁.gpr .x10 = BitVec.ofNat 64 (256 * sat x + b.toNat) ∧
      t₁.gpr .x13 = BitVec.ofNat 64 ((256 * sat x + b.toNat) / 2 ^ 33) ∧ t₁.mem = t.mem) (by
    brun [h4, h10, h11, ha, read_one, hb, step_v (sat_lt x), shr33 hv]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h10₁, h13₁, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (WP.keep [.x13] (Q := fun t₂ =>
      t₂.zf = decide ((256 * sat x + b.toNat) / 2 ^ 33 = 0) ∧ t₂.mem = t₁.mem) (by
    brun [h13₁, (k₁.gpr .x17 (by decide)).trans h17, zf_awc, zero_test (show (256 * sat x + b.toNat) / 2 ^ 33 < 2 ^ 64
      by omega)]) (by decide) (by decide) (by decide +kernel))
    fun t₂ ⟨⟨hz₂, hm₂⟩, k₂⟩ => ?_
  refine WP.mono (WP.keep [.x10] (Q := fun t₃ =>
      t₃.gpr .x10 = BitVec.ofNat 64 (sat (256 * x + b.toNat)) ∧ t₃.mem = t₂.mem) (by
    brun [exec_cselc_x', CondCode.holds, hz₂, (k₂.gpr .x10 (by decide)).trans h10₁,
      (k₂.gpr .x16 (by decide)).trans ((k₁.gpr .x16 (by decide)).trans h16)]
    rw [← sat_step x _ b.isLt]
    generalize 256 * sat x + b.toNat = v at *
    unfold sat
    by_cases h : v < 2 ^ 33
    · have h' : v / 2 ^ 33 = 0 := by omega
      simp only [h', decide_true, ite_true, h]
    · have h' : ¬ v / 2 ^ 33 = 0 := by omega
      simp only [h', decide_false, Bool.false_eq_true, ite_false, h]) (by decide) (by decide) (by decide +kernel))
    fun t₃ ⟨⟨h10₃, hm₃⟩, k₃⟩ => ?_
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.mono (WP.keep [.x11, .x14] (Q := fun t' => t'.gpr .x11 = BitVec.ofNat 64 (j + 1) ∧
      t'.gpr .x14 = BitVec.ofNat 64 L - BitVec.ofNat 64 (j + 1) ∧ t'.mem = t₃.mem) (by
    brun [(k13.gpr .x11 (by decide)).trans h11, (k13.gpr .x5 (by decide)).trans h5, BitVec.ofNat_add_ofNat])
    (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨h11', h14', hm'⟩, k₄⟩ => ⟨(k₄.gpr .x10 (by decide)).trans h10₃, h11',
      by rw [h14']; exact ofNat_sub_ne (by omega) (by omega), by rw [hm', hm₃, hm₂, hm₁],
      (k13.trans k₄).mono (by decide)⟩

theorem exec_movk_x' (s : State) {d : Reg} {imm : BitVec 16} {hw : Nat} (h : 16 * hw < 64) :
    exec (.movk .x d imm hw) s = some (s.write .x d ((s.gpr d &&& ~~~((0xFFFF : BitVec 64) <<< (16 * hw))) |||
      (imm.setWidth 64 <<< (16 * hw)))) := by
  simp [exec, h, State.read, Size.bits]

/-- `expTest`: `x9` is 1 iff `v` is within BoringSSL's limits, else 0. -/
theorem expTest_ok {t : State} {v : Nat} (hv : v < 2 ^ 64) (h10 : t.gpr .x10 = BitVec.ofNat 64 v)
    (h15 : t.gpr .x15 = 1) (h17 : t.gpr .x17 = 0) :
    WP isa (.block expTest) t fun t' => t'.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.exponentValid v).toNat ∧
      t'.mem = t.mem ∧ Keep [.x9, .x12, .x13, .x14] t t' := by
  rw [show expTest = ([.lsr .x .x13 .x10 33, .adds .x .x13 .x13 .x17] : List Instr) ++
      ([.cselc .x .x13 .x15 .x17 .eq] : List Instr) ++
      ([.logic .and .x .x14 .x10 .x15, movi .x12 3, .subs .x .x12 .x10 .x12, .csel .x .x12 .x15 .x17] : List Instr) ++
      ([.logic .and .x .x9 .x13 .x14, .logic .and .x .x9 .x9 .x12] : List Instr) from rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.x13] (Q := fun t₁ => t₁.zf = decide (v / 2 ^ 33 = 0) ∧ t₁.mem = t.mem) (by
    brun [h10, h17, shr33 hv, zf_awc, zero_test (show v / 2 ^ 33 < 2 ^ 64 by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hz₁, hm₁⟩, k₁⟩ => ?_
  have h15₁ := (k₁.gpr .x15 (by decide)).trans h15
  have h17₁ := (k₁.gpr .x17 (by decide)).trans h17
  have h10₁ := (k₁.gpr .x10 (by decide)).trans h10
  refine WP.mono (WP.keep [.x13] (Q := fun t₂ => t₂.gpr .x13 = BitVec.ofNat 64 (decide (v < 2 ^ 33)).toNat ∧
      t₂.mem = t₁.mem) (by
    brun [exec_cselc_x', CondCode.holds, hz₁, h15₁, h17₁]
    by_cases h : v < 2 ^ 33
    · have h' : v / 2 ^ 33 = 0 := by omega
      simp only [h', decide_true, ite_true, h]; rfl
    · have h' : ¬ v / 2 ^ 33 = 0 := by omega
      simp only [h', decide_false, Bool.false_eq_true, ite_false, h]; rfl)
    (by decide) (by decide) (by decide +kernel)) fun t₂ ⟨⟨h13₂, hm₂⟩, k₂⟩ => ?_
  refine WP.mono (WP.keep [.x12, .x14] (Q := fun t₃ => t₃.gpr .x14 = BitVec.ofNat 64 (v % 2) ∧
      t₃.gpr .x12 = BitVec.ofNat 64 (decide (3 ≤ v)).toNat ∧ t₃.mem = t₂.mem) (by
    brun [(k₂.gpr .x10 (by decide)).trans h10₁, (k₂.gpr .x15 (by decide)).trans h15₁,
      (k₂.gpr .x17 (by decide)).trans h17₁, and1_mod2]
    exact ⟨by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv],
      ge_sel (x := v) (c := 3) (by decide) (by decide) _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv])⟩)
    (by decide) (by decide) (by decide +kernel)) fun t₃ ⟨⟨h14₃, h12₃, hm₃⟩, k₃⟩ => ?_
  refine WP.mono (WP.keep [.x9] (Q := fun t' => t'.gpr .x9 = t₃.gpr .x13 &&& t₃.gpr .x14 &&& t₃.gpr .x12 ∧
      t'.mem = t₃.mem) (by brun) (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h9, hm⟩, k₄⟩ => ?_
  refine ⟨?_, by rw [hm, hm₃, hm₂, hm₁], (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  rw [h9, k₃.gpr .x13 (by decide), h13₂, h14₃, h12₃, mod2_bit, and_bits, and_bits]
  congr 2
  simp only [Spec.Rsa.exponentValid]
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> by_cases h3 : 3 ≤ v <;> by_cases h33 : v < 2 ^ 33 <;>
    simp [h, h3, h33]

/-- After `j` bytes of `e`. -/
structure ExpInv (s : State) (ep : Addr) (L : Nat) (eb : List Byte) (j : Nat) (t : State) : Prop where
  x4 : t.gpr .x4 = ep
  x5 : t.gpr .x5 = BitVec.ofNat 64 L
  x11 : t.gpr .x11 = BitVec.ofNat 64 j
  x10 : t.gpr .x10 = BitVec.ofNat 64 (sat (pre eb j))
  x15 : t.gpr .x15 = 1
  x16 : t.gpr .x16 = BitVec.ofNat 64 (2 ^ 34 - 1)
  x17 : t.gpr .x17 = 0
  mem : t.mem = s.mem
  keep : Keep [.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s t

/-- `expCheck`: `x9` is 1 exactly when the `L` bytes `eb` of `e` at `x4` are
within BoringSSL's limits, else 0. -/
theorem expCheck_ok {s : State} {ep : Addr} {L : Nat} {eb : List Byte} (h4 : s.gpr .x4 = ep)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hL : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 i) 1) (heb : eb = Spec.Rsa.bytesAt s.mem ep L) :
    WP isa expCheck s fun t => t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)).toNat ∧
      t.mem = s.mem ∧ Keep [.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s t := by
  have hlen : eb.length = L := by rw [heb]; simp [Spec.Rsa.bytesAt]
  unfold expCheck
  refine WP.seq (WP.mono (WP.keep [.x10, .x11, .x15, .x16, .x17] (Q := fun t => t.gpr .x10 = BitVec.ofNat 64 0 ∧
      t.gpr .x11 = BitVec.ofNat 64 0 ∧ t.gpr .x15 = 1 ∧ t.gpr .x16 = BitVec.ofNat 64 (2 ^ 34 - 1) ∧
      t.gpr .x17 = 0 ∧ t.mem = s.mem) (by
    unfold consts
    brun [exec_movk_x' _ (show 16 * 1 < 64 by decide), exec_movk_x' _ (show 16 * 2 < 64 by decide)])
    (by decide) (by decide) (by decide +kernel))
    fun t₀ ⟨⟨h10, h11, h15, h16, h17, hm⟩, k₀⟩ => ?_)
  refine WP.seq (WP.mono (count_loop (cr := .x14) (n := L) (by omega) (ExpInv s ep L eb) ?_
    ⟨(k₀.gpr .x4 (by decide)).trans h4, (k₀.gpr .x5 (by decide)).trans h5, h11, by rw [h10]; rfl, h15, h16, h17,
      hm, k₀.mono (by decide)⟩) fun t₁ hI => ?_)
  · intro j hj t hI
    have hb : t.mem (ep + BitVec.ofNat 64 j) = eb[j]'(by omega) := by
      rw [hI.mem]; subst heb; simp [Spec.Rsa.bytesAt]
    refine WP.mono (expStep_ok hI.x4 hI.x5 hI.x11 hI.x10 hI.x16 hI.x17 hj hL
      (by rw [hI.keep.rd, hI.keep.wr]; exact hrd j hj) hb)
      fun t' ⟨h10', h11', h14', hm', k'⟩ => ⟨⟨(k'.gpr .x4 (by decide)).trans hI.x4, (k'.gpr .x5 (by decide)).trans hI.x5,
        h11', ?_, (k'.gpr .x15 (by decide)).trans hI.x15, (k'.gpr .x16 (by decide)).trans hI.x16,
        (k'.gpr .x17 (by decide)).trans hI.x17, hm'.trans hI.mem, (hI.keep.trans k').mono (by decide)⟩, h14'⟩
    rw [h10', pre_succ eb (by omega)]
  · have hv : sat (pre eb L) < 2 ^ 64 := by have := sat_lt (pre eb L); omega
    refine WP.mono (expTest_ok hv hI.x10 hI.x15 hI.x17) fun t ⟨h9, hm', k⟩ => ⟨?_, hm'.trans hI.mem,
      (hI.keep.trans k).mono (by decide)⟩
    rw [h9, exponentValid_sat, ← hlen, pre_len]

/-! ## `failOut` -/

/-- After `j` zero bytes from `s₀`. -/
structure FInv (s₀ : State) (op : Addr) (j : Nat) (t : State) : Prop where
  keep : Keep [.x10, .x11] s₀ t
  x10 : t.gpr .x10 = op + BitVec.ofNat 64 j
  bytes : ∀ i < j, t.mem (op + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s₀.mem x

theorem fStep_ok {s₀ : State} {op : Addr} {N : Nat} (hN : N < 2 ^ 63) (h12 : s₀.gpr .x12 = 0)
    (hwr : ∀ j < N, InRegions s₀.wr (op + BitVec.ofNat 64 j) 1) {j : Nat} (hj : j < N) {t : State}
    (hI : FInv s₀ op j t) :
    WP isa (.block ([.strb .x12 .x10 0, .addImm .x .x10 .x10 1] ++ ([.subImm .x .x11 .x11 1] : List Instr))) t
      fun t' => FInv s₀ op (j + 1) t' ∧ t'.gpr .x11 = t.gpr .x11 - BitVec.ofNat 64 1 := by
  have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by rw [hI.keep.wr]; exact hwr j hj
  have h12' : t.gpr .x12 = 0 := (hI.keep.gpr .x12 (by decide)).trans h12
  have hw8 : ∀ (m : Mem) (a : Addr) (v : BitVec 8), m.write a 1 v = m.writeW a v := fun _ _ _ => rfl
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x10] (Q := fun t₁ => t₁.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
      t₁.gpr .x10 = op + BitVec.ofNat 64 (j + 1)) (by
    brun [hI.x10, hst, h12', hw8, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl) (by decide) (by decide)
      (by decide +kernel))
    fun t₁ ⟨⟨hm, h10⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x11) fun t' ⟨⟨h11, hm', _⟩, k'⟩ => ⟨?_, by rw [h11, k₁.gpr .x11 (by decide)]⟩
  refine ⟨((hI.keep.trans k₁).trans k').mono (by decide), by rw [k'.gpr .x10 (by decide), h10], fun i hi => ?_,
    fun x hx => ?_⟩
  · rw [hm', hm, writeW8_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
      exact hI.bytes i (by omega)
  · rw [hm', hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
    exact hI.frame x fun i hi => hx i (by omega)

/-- `failOut`: zeros to the `k` (at least 1) bytes of `out` (`x0`, `k` in
`x1`), and 0 returned. -/
theorem failOut_ok {s : State} {op : Addr} {k : Nat} (h0 : s.gpr .x0 = op) (h1 : s.gpr .x1 = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk : k < 2 ^ 63) (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa failOut s fun t => Spec.Rsa.bytesAt t.mem op k = List.replicate k 0 ∧ t.gpr .x0 = 0 ∧
      (∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.x0, .x10, .x11, .x12] s t := by
  unfold failOut
  refine WP.seq (WP.mono (WP.keep [.x10, .x11, .x12] (Q := fun t => t.gpr .x10 = op + BitVec.ofNat 64 0 ∧
      t.gpr .x11 = BitVec.ofNat 64 k ∧ t.gpr .x12 = 0 ∧ t.mem = s.mem) (by brun [h0, h1])
      (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h10, h11, h12, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_countdown (N := k) (by omega) (by omega) (FInv s₁ op)
    (fun j hj t hI _ => fStep_ok (by omega) h12 (fun i hi => by rw [k₁.wr]; exact hout i hi) hj hI)
    ⟨Keep.refl _ _, h10, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ h11) fun t₂ hI => ?_)
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = t₂.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨hx, hm⟩, k₃⟩ => ⟨?_, hx, fun x hx' => ?_, ((k₁.trans hI.keep).trans k₃).mono
      (by decide)⟩
  · rw [bytesAt_eq, List.eq_replicate_iff]
    refine ⟨by simp, fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hm]
    exact hI.bytes i (List.mem_range.mp hi)
  · rw [hm, hI.frame x hx', hm₁]

end VG.Proof.Rsa.AArch64
