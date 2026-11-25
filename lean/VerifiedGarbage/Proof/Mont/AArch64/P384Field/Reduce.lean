module

public import VerifiedGarbage.Proof.Mont.AArch64.P384Field.Chains
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# P-384's field arithmetic on AArch64: the reduction

`round2_ok`: a round makes `T` into `(T + M p) / 2^128` for some `M < 2^128`.
`reduce_ok`: three of them and the high half of `T`.
-/

@[expose] public section

set_option exponentiation.threshold 1024

namespace VG.Proof.Mont.AArch64.P384Field

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P384Field
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.addCarry_value)

/-- P-384's `p`. -/
abbrev p : Nat := 2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1

theorem ext_arith {o n g l : Nat} (hl : l < 2 ^ 32 ∧ g < 2 ^ 32 ∧ n < 2 ^ 32) :
    ((2 ^ 32 * o + n) * 2 ^ 64 + (2 ^ 32 * g + l)) / 2 ^ 32 % 2 ^ 64 = 2 ^ 32 * n + g := by
  rw [show (2 ^ 32 * o + n) * 2 ^ 64 + (2 ^ 32 * g + l) = 2 ^ 32 * (2 ^ 32 * n + g + 2 ^ 64 * o) + l by omega,
    Nat.mul_add_div (by decide), Nat.div_eq_of_lt hl.1]
  omega

/-- The multiplier `M = m₀ + 2^64 m₁` of the words `t₀`, `t₁`: `b` is the
carry of `m₀`, and `v`, `u₀`, `u₁` the shifts of `M`. The low words of `M (1 - 2^32 + 2^96)` are
`t₀` (with the borrow `b`) and `t₁`. -/
theorem mult_arith {t0 t1 a s b m0 m1 v u0 u1 : Nat} (h0 : t0 < 2 ^ 64) (h1 : t1 < 2 ^ 64)
    (ha : a = t0 * 2 ^ 32 % 2 ^ 64) (hs : s = (t1 * 2 ^ 64 + t0) / 2 ^ 32 % 2 ^ 64)
    (hm0 : m0 + 2 ^ 64 * b = t0 + a) (hm0' : m0 < 2 ^ 64)
    (hm1 : m1 = ((t1 + s + b) % 2 ^ 64 + t0) % 2 ^ 64)
    (hv : v = m0 * 2 ^ 32 % 2 ^ 64) (hu0 : u0 = (m1 * 2 ^ 64 + m0) / 2 ^ 32 % 2 ^ 64) (hu1 : u1 = m1 / 2 ^ 32) :
    v = a ∧ (u0 + 2 ^ 64 * u1) * 2 ^ 32 + m0 % 2 ^ 32 = m0 + 2 ^ 64 * m1 ∧ v = 2 ^ 32 * (m0 % 2 ^ 32) ∧
      (u0 + b + t1) % 2 ^ 64 = (m1 + v) % 2 ^ 64 := by
  obtain ⟨l0, hl0, k0, hk0, rfl⟩ : ∃ l < 2 ^ 32, ∃ k < 2 ^ 32, t0 = 2 ^ 32 * k + l :=
    ⟨t0 % 2 ^ 32, by omega, t0 / 2 ^ 32, by omega, by omega⟩
  obtain ⟨l1, hl1, k1, hk1, rfl⟩ : ∃ l < 2 ^ 32, ∃ k < 2 ^ 32, t1 = 2 ^ 32 * k + l :=
    ⟨t1 % 2 ^ 32, by omega, t1 / 2 ^ 32, by omega, by omega⟩
  obtain ha' : a = 2 ^ 32 * l0 := by omega
  obtain hs' : s = 2 ^ 32 * l1 + k0 := by rw [hs, ext_arith ⟨hl0, hk0, hl1⟩]
  clear ha hs
  subst ha' hs'
  obtain hb : b ≤ 1 := by omega
  obtain ⟨g, hg, rfl⟩ : ∃ g < 2 ^ 32, m0 = 2 ^ 32 * g + l0 := ⟨m0 / 2 ^ 32, by omega, by omega⟩
  obtain hgb : g + 2 ^ 32 * b = k0 + l0 := by omega
  obtain hv' : v = 2 ^ 32 * l0 := by omega
  obtain ⟨j, hj⟩ : ∃ j, m1 + 2 ^ 64 * j = 2 ^ 32 * k1 + l1 + (2 ^ 32 * l1 + k0) + b + (2 ^ 32 * k0 + l0) := by
    rw [Nat.mod_add_mod] at hm1
    exact ⟨_, hm1 ▸ Nat.mod_add_div _ _⟩
  obtain hm1l : m1 < 2 ^ 64 := by rw [hm1]; exact Nat.mod_lt _ (by decide)
  clear hm1
  obtain ⟨n, hn, o, ho, rfl⟩ : ∃ l < 2 ^ 32, ∃ k < 2 ^ 32, m1 = 2 ^ 32 * k + l :=
    ⟨m1 % 2 ^ 32, by omega, m1 / 2 ^ 32, by omega, by omega⟩
  rw [ext_arith (by omega)] at hu0
  obtain hu1' : u1 = o := by rw [hu1, Nat.mul_add_div (by decide), Nat.div_eq_of_lt hn, Nat.add_zero]
  clear hu1 hv hm0 hm0' h0 h1
  subst hu0 hu1' hv'
  refine ⟨rfl, by omega, by omega, ?_⟩
  have hn' : 2 ^ 32 * n + 2 ^ 64 * u1 + 2 ^ 64 * (2 ^ 32 * j) = 2 ^ 32 * (2 ^ 32 * k1 + l1 + (2 ^ 32 * l1 + k0) + b +
      (2 ^ 32 * k0 + l0)) := by omega
  have e : 2 ^ 32 * n + g + b + (2 ^ 32 * k1 + l1) + 2 ^ 64 * (u1 + 2 ^ 32 * j) =
      2 ^ 32 * u1 + n + 2 ^ 32 * l0 + 2 ^ 64 * (k1 + l1 + k0 + j) := by omega
  have := congrArg (· % 2 ^ 64) e
  simpa only [Nat.add_mul_mod_self_left] using this

/-- `D = M + ⌊M / 2^32⌋ - ⌊M / 2^96⌋ + ka - kb`, the words `y16`, `y24`, `y25`, is
`(M (2^128 + 2^96 - 2^32 + 1) - T₀) / 2^128`. -/
theorem quot_arith {t0 t1 b m0 m1 v u0 u1 l x25 w b0 y3 E c4 y25 : Nat}
    (h0 : t0 < 2 ^ 64) (h1 : t1 < 2 ^ 64) (hm0 : m0 + 2 ^ 64 * b = t0 + v) (hl : v = 2 ^ 32 * l)
    (hu : (u0 + 2 ^ 64 * u1) * 2 ^ 32 + l = m0 + 2 ^ 64 * m1)
    (ht1 : (u0 + b + t1) % 2 ^ 64 = (m1 + v) % 2 ^ 64)
    (hw : w + v = m0 + 2 ^ 64 * b0) (hw' : w < 2 ^ 64)
    (hY : y3 + 2 ^ 64 * E + (u0 + 2 ^ 64 * u1) + b0 + 2 ^ 192 * x25 =
      (m1 + 2 ^ 64 * m0 + 2 ^ 128 * m1) + (v + 2 ^ 64 * u0 + 2 ^ 128 * u1) + 2 ^ 192 * c4)
    (hy3 : y3 < 2 ^ 64) (hE : E < 2 ^ 128) (hc4 : c4 ≤ 1) (f25 : y25 = (2 ^ 64 + x25 - c4) % 2 ^ 64)
    (hx25 : x25 ≤ 1) :
    2 ^ 128 * (E + 2 ^ 128 * y25) + (t0 + 2 ^ 64 * t1) + 2 ^ 32 * (m0 + 2 ^ 64 * m1) =
      (2 ^ 128 + 2 ^ 96 + 1) * (m0 + 2 ^ 64 * m1) := by
  obtain rfl : b0 = b := by omega_using [hm0, hw, hw', h0]
  obtain rfl : w = t0 := by omega_using [hm0, hw]
  obtain hy : y3 = t1 := by
    have : (u0 + b0 + y3) % 2 ^ 64 = (m1 + v) % 2 ^ 64 := by omega_using [hY]
    have : (u0 + b0 + y3) % 2 ^ 64 = (u0 + b0 + t1) % 2 ^ 64 := this.trans ht1.symm
    omega_using [this, hy3, h1]
  subst hy
  have hZ : 2 ^ 128 * (E + 2 ^ 128 * x25) + (w + 2 ^ 64 * y3) + 2 ^ 32 * (m0 + 2 ^ 64 * m1) =
      (2 ^ 128 + 2 ^ 96 + 1) * (m0 + 2 ^ 64 * m1) + 2 ^ 256 * c4 := by
    omega_using [hY, hm0, hl, hu]
  have hle : c4 ≤ x25 := by omega_using [hZ, hc4, hx25, hE, h0, hy3]
  rw [show y25 = x25 - c4 by omega_using [f25, hle, hx25]]
  omega_using [hZ, hle]

/-! ## The round's instructions -/

theorem lsl_ok (s : State) (d n : Reg) : WP isa (.block [.lsl .x d n 32]) s fun t =>
    (t.gpr d).toNat = (s.gpr n).toNat * 2 ^ 32 % 2 ^ 64 ∧ Keeps [d] s t ∧ t.c = s.c := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show 32 < Size.x.bits from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩, rfl⟩
  rw [RegUpd.gpr_write_self]
  simp only [BitVec.setWidth_eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Size.bits]

theorem lsr_ok (s : State) (d n : Reg) : WP isa (.block [.lsr .x d n 32]) s fun t =>
    (t.gpr d).toNat = (s.gpr n).toNat / 2 ^ 32 ∧ Keeps [d] s t ∧ t.c = s.c := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show 32 < Size.x.bits from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩, rfl⟩
  rw [RegUpd.gpr_write_self]
  simp only [BitVec.setWidth_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem extr_ok (s : State) (d n m : Reg) : WP isa (.block [.extr .x d n m 32]) s fun t =>
    (t.gpr d).toNat = ((s.gpr n).toNat * 2 ^ 64 + (s.gpr m).toNat) / 2 ^ 32 % 2 ^ 64 ∧ Keeps [d] s t ∧ t.c = s.c := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show 32 < Size.x.bits from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩, rfl⟩
  rw [RegUpd.gpr_write_self]
  rw [BitVec.setWidth_eq, BitVec.extractLsb'_toNat, BitVec.toNat_append, Nat.shiftRight_eq_div_pow,
    ← Nat.shiftLeft_add_eq_or_of_lt (s.gpr m).isLt, Nat.shiftLeft_eq]

theorem add_ok (s : State) (d n m : Reg) : WP isa (.block [.add .x d n m]) s fun t =>
    (t.gpr d).toNat = ((s.gpr n).toNat + (s.gpr m).toNat) % 2 ^ 64 ∧ Keeps [d] s t ∧ t.c = s.c := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩, rfl⟩
  rw [RegUpd.gpr_write_self]
  simp only [BitVec.setWidth_eq]
  exact BitVec.toNat_add ..

/-- `d = n - m - b`, its borrow dropped. -/
theorem sbc_ok (s : State) (d n m : Reg) : WP isa (.block [.sbc .x d n m]) s fun t =>
    (t.gpr d).toNat = (2 ^ 64 + (s.gpr n).toNat - (s.gpr m).toNat - (!s.c).toNat) % 2 ^ 64 ∧ Keeps [d] s t ∧
      t.c = s.c := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩, rfl⟩
  rw [RegUpd.gpr_write_self]
  have hn := (s.gpr n).isLt
  have hm := (s.gpr m).isLt
  simp only [BitVec.setWidth_eq, BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_ofNat, Size.bits]
  cases s.c <;> simp only [Bool.toNat_true, Bool.toNat_false, Bool.not_true, Bool.not_false] <;> omega_using [hn, hm]

/-- The registers of a round. -/
def RoundOk (t0 t1 t2 t3 t4 t5 m0 m1 v : Reg) : Prop :=
  (∀ r ∈ [t0, t1, t2, t3, t4, t5, m0, m1, v], r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x16 ∧ r ≠ .x24 ∧ r ≠ .x25 ∧ r ≠ .x7) ∧
  (t2 ≠ t3 ∧ t2 ≠ t4 ∧ t2 ≠ t5 ∧ t2 ≠ m0 ∧ t2 ≠ m1 ∧ t2 ≠ v) ∧ (t3 ≠ t4 ∧ t3 ≠ t5 ∧ t3 ≠ m0 ∧ t3 ≠ m1 ∧ t3 ≠ v) ∧
  (t4 ≠ t5 ∧ t4 ≠ m0 ∧ t4 ≠ m1 ∧ t4 ≠ v) ∧ (t5 ≠ m0 ∧ t5 ≠ m1 ∧ t5 ≠ v) ∧ (m0 ≠ m1 ∧ m0 ≠ v ∧ m1 ≠ v) ∧
  t0 ≠ m0 ∧ t1 ≠ m0

instance (t0 t1 t2 t3 t4 t5 m0 m1 v : Reg) : Decidable (RoundOk t0 t1 t2 t3 t4 t5 m0 m1 v) := by
  unfold RoundOk; infer_instance

/-- The registers a round writes. -/
abbrev roundW (t2 t3 t4 t5 m0 m1 v : Reg) : List Reg :=
  [.x1, .x2, .x3, .x16, .x24, .x25, v, m0, m1, t2, t3, t4, t5]

theorem final_arith {T0 TH M D R b : Nat} (hD : 2 ^ 128 * D + T0 + 2 ^ 32 * M = (2 ^ 128 + 2 ^ 96 + 1) * M)
    (hM : M < 2 ^ 128) (hR : R < 2 ^ 384) (hD' : D < 2 ^ 192) (hTH : TH < 2 ^ 256)
    (e : R + D = TH + 2 ^ 256 * M + 2 ^ 384 * b) : 2 ^ 128 * R = (T0 + 2 ^ 128 * TH) + M * p := by
  obtain rfl : b = 0 := by
    by_cases hM0 : M = 0
    · subst hM0
      have : D = 0 := by omega_using [hD]
      subst this
      omega_using [e, hR, hTH]
    · have : 1 ≤ M := Nat.pos_of_ne_zero hM0
      omega_using [e, hD', this, hR, hM, hTH]
  rw [p, Nat.mul_comm M]
  omega_using [hD, e]

/-- A round: `T` becomes `(T + M p) / 2^128`. -/
theorem round2_ok {s : State} {t0 t1 t2 t3 t4 t5 m0 m1 v : Reg} (h : RoundOk t0 t1 t2 t3 t4 t5 m0 m1 v)
    (hz : s.gpr .x7 = 0) :
    WP isa (.block (round2 t0 t1 t2 t3 t4 t5 m0 m1 v)) s fun t =>
      (∃ M < 2 ^ 128, 2 ^ 128 * regsVal t [t2, t3, t4, t5, m0, m1] = regsVal s [t0, t1, t2, t3, t4, t5] + M * p) ∧
      Keeps (roundW t2 t3 t4 t5 m0 m1 v) s t := by
  obtain ⟨hP, ⟨n23, n24, n25, n2m, n2n, n2v⟩, ⟨n34, n35, n3m, n3n, n3v⟩, ⟨n45, n4m, n4n, n4v⟩, ⟨n5m, n5n, n5v⟩,
    ⟨nmn, nmv, nnv⟩, n0m, n1m⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hP
  obtain ⟨p0, p1, p2, p3, p4, p5, pm, pn, pv⟩ := hP
  simp only [round2, List.cons_append, List.nil_append]
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (lsl_ok s m0 t0) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (extr_ok s₁ .x1 t1 t0) fun s₂ ⟨e₂, k₂, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addc_ok s₂ m0 t0 m0 true rfl) fun s₃ ⟨e₃, c₃, k₃⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (adc_ok s₃ .x1 t1 .x1) fun s₄ ⟨e₄, k₄, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (add_ok s₄ m1 .x1 t0) fun s₅ ⟨e₅, k₅, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (lsl_ok s₅ v m0) fun s₆ ⟨e₆, k₆, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (extr_ok s₆ .x1 m1 m0) fun s₇ ⟨e₇, k₇, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (lsr_ok s₇ .x2 m1) fun s₈ ⟨e₈, k₈, _⟩ => ?_
  rw [show ∀ is : List Instr, Instr.adds .x .x3 m1 v :: .adcs .x .x16 m0 .x1 :: .adcs .x .x24 m1 .x2 :: is =
    adds true [.x3, .x16, .x24] [m1, m0, m1] [v, .x1, .x2] ++ is from fun _ => rfl, WP.block_append_iff]
  refine WP.mono (adds_ok true [.x3, .x16, .x24] [m1, m0, m1] [v, .x1, .x2] (s := s₈) (.inr (by simp)) rfl rfl
    (by simp [ChainOk, Ne.symm, pm, pn])) fun s₉ ⟨e₉, k₉⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (adc_ok s₉ .x25 .x7 .x7) fun s₁₀ ⟨e₁₀, k₁₀, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (subc_ok s₁₀ v m0 v true rfl) fun s₁₁ ⟨e₁₁, c₁₁, k₁₁⟩ => ?_
  rw [show ∀ is : List Instr, Instr.sbcs .x .x3 .x3 .x1 :: .sbcs .x .x16 .x16 .x2 :: .sbcs .x .x24 .x24 .x7 :: is =
    subs false [.x3, .x16, .x24] [.x3, .x16, .x24] [.x1, .x2, .x7] ++ is from fun _ => rfl, WP.block_append_iff]
  refine WP.mono (subs_ok false [.x3, .x16, .x24] [.x3, .x16, .x24] [.x1, .x2, .x7] (s := s₁₁) (.inl rfl) rfl rfl
    (by decide)) fun s₁₂ ⟨e₁₂, k₁₂⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (sbc_ok s₁₂ .x25 .x25 .x7) fun s₁₃ ⟨e₁₃, k₁₃, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subs_ok true [t2, t3, t4, t5, m0] [t2, t3, t4, t5, m0] [.x16, .x24, .x25, .x7, .x7] (s := s₁₃)
    (.inr (by simp)) rfl rfl (by simp [ChainOk, *, Ne.symm])) fun s₁₄ ⟨e₁₄, k₁₄⟩ => ?_
  refine WP.mono (sbc_ok s₁₄ m1 m1 .x7) fun t ⟨e₁₅, k₁₅, _⟩ => ?_
  have K₈ : Keeps [.x1, .x2, v, m0, m1] s s₈ :=
    (k₁.mono (by simp)).trans <| (k₂.mono (by simp)).trans <| (k₃.mono (by simp)).trans <|
      (k₄.mono (by simp)).trans <| (k₅.mono (by simp)).trans <| (k₆.mono (by simp)).trans <|
      (k₇.mono (by simp)).trans (k₈.mono (by simp))
  have K₁₃ : Keeps [.x1, .x2, .x3, .x16, .x24, .x25, v, m0, m1] s s₁₃ :=
    (K₈.mono (by simp)).trans <| (k₉.mono (by simp)).trans <| (k₁₀.mono (by simp)).trans <|
      (k₁₁.mono (by simp)).trans <| (k₁₂.mono (by simp)).trans (k₁₃.mono (by simp))
  refine ⟨?_, (K₁₃.mono (by simp)).trans <| (k₁₄.mono (by simp)).trans (k₁₅.mono (by simp))⟩
  have hz₈ : s₈.gpr .x7 = 0 := by rw [K₈.gpr _ (by simp [pv.2.2.2.2.2.2.symm, pm.2.2.2.2.2.2.symm, pn.2.2.2.2.2.2.symm]), hz]
  -- The registers of the chains, from where they were last written.
  have m0₈ : s₈.gpr m0 = s₃.gpr m0 := by
    rw [k₈.gpr _ (by simp [pm]), k₇.gpr _ (by simp [pm]), k₆.gpr _ (by simp [nmv]), k₅.gpr _ (by simp [nmn]),
      k₄.gpr _ (by simp [pm])]
  have m1₈ : s₈.gpr m1 = s₅.gpr m1 := by
    rw [k₈.gpr _ (by simp [pn]), k₇.gpr _ (by simp [pn]), k₆.gpr _ (by simp [nnv])]
  have v₈ : s₈.gpr v = s₆.gpr v := by rw [k₈.gpr _ (by simp [pv]), k₇.gpr _ (by simp [pv])]
  have x1₈ : s₈.gpr .x1 = s₇.gpr .x1 := k₈.gpr _ (by simp)
  have t1₃ : s₃.gpr t1 = s.gpr t1 := by
    rw [k₃.gpr _ (by simp [n1m]), k₂.gpr _ (by simp [p1]), k₁.gpr _ (by simp [n1m])]
  have t0₄ : s₄.gpr t0 = s.gpr t0 := by
    rw [k₄.gpr _ (by simp [p0]), k₃.gpr _ (by simp [n0m]), k₂.gpr _ (by simp [p0]), k₁.gpr _ (by simp [n0m])]
  have t0₂ : s₂.gpr t0 = s.gpr t0 := by rw [k₂.gpr _ (by simp [p0]), k₁.gpr _ (by simp [n0m])]
  have m0₅ : s₅.gpr m0 = s₃.gpr m0 := by rw [k₅.gpr _ (by simp [nmn]), k₄.gpr _ (by simp [pm])]
  -- The multiplier.
  rw [k₁.gpr t1 (by simp [n1m]), k₁.gpr t0 (by simp [n0m])] at e₂
  have a₃ := Word64.addCarry_value (s₂.gpr t0) (s₂.gpr m0) false
  simp only [ite_true] at e₃ c₃
  rw [← e₃, ← c₃, t0₂, k₂.gpr m0 (by simp [pm]), e₁, Bool.toNat_false, Nat.add_zero] at a₃
  rw [t1₃, k₃.gpr .x1 (by simp [Ne.symm pm.1]), e₂] at e₄
  rw [t0₄, e₄] at e₅
  rw [m0₅] at e₆
  rw [k₆.gpr m1 (by simp [nnv]), k₆.gpr m0 (by simp [nmv]), m0₅] at e₇
  rw [k₇.gpr m1 (by simp [pn]), k₆.gpr m1 (by simp [nnv])] at e₈
  obtain ⟨hva, hu, hl, ht1⟩ := mult_arith (s.gpr t0).isLt (s.gpr t1).isLt rfl rfl a₃ (s₃.gpr m0).isLt e₅ e₆ e₇ e₈
  rw [← hva] at a₃
  -- The quotient.
  have hz₁₀ : s₉.gpr .x7 = 0 := by rw [k₉.gpr _ (by decide), hz₈]
  have hz₁₁ : s₁₁.gpr .x7 = 0 := by rw [k₁₁.gpr _ (by simp [pv.2.2.2.2.2.2.symm]), k₁₀.gpr _ (by decide), hz₁₀]
  have hz₁₂ : s₁₂.gpr .x7 = 0 := by rw [k₁₂.gpr _ (by decide), hz₁₁]
  have hz₁₃ : s₁₃.gpr .x7 = 0 := by rw [k₁₃.gpr _ (by decide), hz₁₂]
  have hz₁₄ : s₁₄.gpr .x7 = 0 := by
    rw [k₁₄.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨p2.2.2.2.2.2.2.symm,
      p3.2.2.2.2.2.2.symm, p4.2.2.2.2.2.2.symm, p5.2.2.2.2.2.2.symm, pm.2.2.2.2.2.2.symm⟩), hz₁₃]
  have z0 : (0 : BitVec 64).toNat = 0 := rfl
  simp only [regsVal, hz₁₀, z0, ite_true, Bool.toNat_false, Nat.add_zero, Nat.mul_zero, m0₈, m1₈, v₈, x1₈,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at e₉ e₁₀
  have hb := sub_borrow (s₁₀.gpr m0) (s₁₀.gpr v) true
  simp only [ite_true] at e₁₁ c₁₁
  rw [← e₁₁, ← c₁₁, k₁₀.gpr m0 (by simp [pm]), k₉.gpr m0 (by simp [pm]), k₁₀.gpr v (by simp [pv]),
    k₉.gpr v (by simp [pv]), m0₈, v₈] at hb
  have f1 : s₁₁.gpr .x1 = s₇.gpr .x1 := by
    rw [k₁₁.gpr _ (by simp [pv.1.symm]), k₁₀.gpr _ (by decide), k₉.gpr _ (by decide), x1₈]
  have f2 : s₁₁.gpr .x2 = s₈.gpr .x2 := by
    rw [k₁₁.gpr _ (by simp [pv.2.1.symm]), k₁₀.gpr _ (by decide), k₉.gpr _ (by decide)]
  have f3 : regsVal s₁₁ [.x3, .x16, .x24] = regsVal s₉ [.x3, .x16, .x24] := by
    rw [regsVal_keep k₁₁ (by simp [pv.2.2.1.symm, pv.2.2.2.1.symm, pv.2.2.2.2.1.symm]),
      regsVal_keep k₁₀ (by decide)]
  rw [f3] at e₁₂
  simp only [regsVal, f1, f2, hz₁₁, z0, Nat.add_zero, Nat.mul_zero, Bool.false_eq_true, ite_false, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceMul] at e₁₂
  have f25 : s₁₂.gpr .x25 = s₁₀.gpr .x25 := by
    rw [k₁₂.gpr _ (by decide), k₁₁.gpr _ (by simp [pv.2.2.2.2.2.1.symm])]
  have hc9 := Bool.toNat_le s₉.c
  rw [hz₁₂, z0, Nat.sub_zero, f25, e₁₀, Nat.zero_add, Nat.mod_eq_of_lt (a := s₉.c.toNat) (by omega_using [hc9])] at e₁₃
  have hq := quot_arith (E := (s₁₂.gpr .x16).toNat + 2 ^ 64 * (s₁₂.gpr .x24).toNat) (y3 := (s₁₂.gpr .x3).toNat)
    (x25 := s₉.c.toNat) (c4 := (!s₁₂.c).toNat) (b0 := (!s₁₁.c).toNat)
    (s.gpr t0).isLt (s.gpr t1).isLt a₃ hl hu ht1 (by simpa using hb) (s₁₁.gpr v).isLt
    (by omega_using [e₉, e₁₂]) (s₁₂.gpr .x3).isLt
    (by have a := (s₁₂.gpr .x16).isLt; have b := (s₁₂.gpr .x24).isLt; omega_using [a, b]) (Bool.toNat_le _) e₁₃ hc9
  -- The subtraction.
  have g16 : s₁₃.gpr .x16 = s₁₂.gpr .x16 := k₁₃.gpr _ (by decide)
  have g24 : s₁₃.gpr .x24 = s₁₂.gpr .x24 := k₁₃.gpr _ (by decide)
  have up : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x16 → r ≠ .x24 → r ≠ .x25 → r ≠ v → r ≠ m0 → r ≠ m1 →
      s₁₃.gpr r = s.gpr r := fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => K₁₃.gpr r (by simp [*])
  have hm0₁₃ : s₁₃.gpr m0 = s₃.gpr m0 := by
    rw [k₁₃.gpr _ (by simp [pm]), k₁₂.gpr _ (by simp [pm]), k₁₁.gpr _ (by simp [nmv]), k₁₀.gpr _ (by simp [pm]),
      k₉.gpr _ (by simp [pm]), m0₈]
  have hm1₁₄ : s₁₄.gpr m1 = s₅.gpr m1 := by
    rw [k₁₄.gpr _ (by simp [n2n.symm, n3n.symm, n4n.symm, n5n.symm, nmn.symm]), k₁₃.gpr _ (by simp [pn]),
      k₁₂.gpr _ (by simp [pn]), k₁₁.gpr _ (by simp [nnv]), k₁₀.gpr _ (by simp [pn]), k₉.gpr _ (by simp [pn]), m1₈]
  simp only [regsVal, g16, g24, hz₁₃, hm0₁₃, z0, ite_true, Bool.not_true, Bool.toNat_false, Nat.add_zero, Nat.mul_zero,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
    up t2 p2.1 p2.2.1 p2.2.2.1 p2.2.2.2.1 p2.2.2.2.2.1 p2.2.2.2.2.2.1 n2v n2m n2n,
    up t3 p3.1 p3.2.1 p3.2.2.1 p3.2.2.2.1 p3.2.2.2.2.1 p3.2.2.2.2.2.1 n3v n3m n3n,
    up t4 p4.1 p4.2.1 p4.2.2.1 p4.2.2.2.1 p4.2.2.2.2.1 p4.2.2.2.2.2.1 n4v n4m n4n,
    up t5 p5.1 p5.2.1 p5.2.2.1 p5.2.2.2.1 p5.2.2.2.2.1 p5.2.2.2.2.2.1 n5v n5m n5n] at e₁₄
  rw [hz₁₄, z0, Nat.sub_zero, hm1₁₄] at e₁₅
  have fin : ∀ r ∈ [t2, t3, t4, t5, m0], t.gpr r = s₁₄.gpr r := fun r hr => k₁₅.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
  have hR := regsVal_lt t [t2, t3, t4, t5, m0, m1]
  have hb14 := Bool.toNat_le (!s₁₄.c)
  have m1lt := (s₅.gpr m1).isLt
  have m0lt := (s₃.gpr m0).isLt
  have m15 : ∃ b, (t.gpr m1).toNat + (!s₁₄.c).toNat = (s₅.gpr m1).toNat + 2 ^ 64 * b := 
    ⟨if (s₅.gpr m1).toNat < (!s₁₄.c).toNat then 1 else 0, by rw [e₁₅]; split <;> omega_using [hb14, m1lt, ‹_›]⟩
  obtain ⟨b, hb⟩ := m15
  have l2 := (s.gpr t2).isLt
  have l3 := (s.gpr t3).isLt
  have l4 := (s.gpr t4).isLt
  have l5 := (s.gpr t5).isLt
  have d16 := (s₁₂.gpr .x16).isLt
  have d24 := (s₁₂.gpr .x24).isLt
  have d25 := (s₁₃.gpr .x25).isLt
  refine ⟨(s₃.gpr m0).toNat + 2 ^ 64 * (s₅.gpr m1).toNat, by omega_using [m0lt, m1lt], ?_⟩
  simp only [regsVal, Nat.mul_zero, Nat.add_zero, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
    fin t2 (by simp), fin t3 (by simp), fin t4 (by simp), fin t5 (by simp), fin m0 (by simp)] at hR ⊢
  refine (final_arith (T0 := (s.gpr t0).toNat + 2 ^ 64 * (s.gpr t1).toNat)
    (TH := (s.gpr t2).toNat + 2 ^ 64 * ((s.gpr t3).toNat + 2 ^ 64 * ((s.gpr t4).toNat + 2 ^ 64 * (s.gpr t5).toNat)))
    (b := b) hq (by omega_using [m0lt, m1lt]) hR (by omega_using [d16, d24, d25])
    (by omega_using [l2, l3, l4, l5]) (by omega_using [e₁₄, hb])).trans ?_
  omega_using []

/-- The registers `reduce` writes. -/
abbrev redW : List Reg := [.x1, .x2, .x3, .x16, .x24, .x25, .x17, .x22, .x23, .x8, .x9, .x10, .x11, .x12, .x13]

/-- Three rounds, two words each, are Montgomery's reduction. -/
theorem rounds_arith {L R₁ R₂ R₃ M₁ M₂ M₃ H V : Nat} (h₁ : 2 ^ 128 * R₁ = L + M₁ * p)
    (h₂ : 2 ^ 128 * R₂ = R₁ + M₂ * p) (h₃ : 2 ^ 128 * R₃ = R₂ + M₃ * p) (hM₁ : M₁ < 2 ^ 128) (hM₂ : M₂ < 2 ^ 128)
    (hM₃ : M₃ < 2 ^ 128) (hT : L + 2 ^ 384 * H < 2 ^ 384 * p) (hV : V = R₃ + H) :
    V < 2 * p ∧ V * 2 ^ (64 * 6) % p = (L + 2 ^ 384 * H) % p := by
  have e : V * 2 ^ (64 * 6) = L + 2 ^ 384 * H + (M₁ + 2 ^ 128 * M₂ + 2 ^ 256 * M₃) * p := by
    rw [hV]
    simp only [Nat.add_mul, Nat.mul_assoc]
    omega_using [h₁, h₂, h₃]
  refine ⟨?_, by rw [e, Nat.add_mul_mod_self_right]⟩
  have hM : (M₁ + 2 ^ 128 * M₂ + 2 ^ 256 * M₃) * p ≤ (2 ^ 384 - 1) * p :=
    Nat.mul_le_mul_right _ (by omega_using [hM₁, hM₂, hM₃])
  have : V * 2 ^ (64 * 6) < 2 ^ 384 * (2 * p) := by
    rw [e]
    omega_using [hM, hT]
  exact Nat.lt_of_mul_lt_mul_left (a := 2 ^ 384) (by rw [Nat.mul_comm (2 ^ 384) V]; exact this)

/-- The reduction of `T`, below `2^384 p`. -/
theorem reduce_ok {s : State} (hz : s.gpr .x7 = 0) (hT : regsVal s (tl ++ th) < 2 ^ 384 * p) :
    WP isa (.block reduce) s fun t =>
      (∃ V, regsVal t rs + 2 ^ 384 * (t.gpr .x13).toNat = V ∧ V < 2 * p ∧
        V * 2 ^ (64 * 6) % p = regsVal s (tl ++ th) % p) ∧
      Keeps redW s t := by
  simp only [reduce, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (round2_ok (by decide) hz) fun s₁ ⟨⟨M₁, hM₁, e₁⟩, k₁⟩ => ?_
  have K₁ : Keeps redW s s₁ := k₁.mono (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (round2_ok (by decide) (by rw [K₁.gpr _ (by decide), hz])) fun s₂ ⟨⟨M₂, hM₂, e₂⟩, k₂⟩ => ?_
  have K₂ : Keeps redW s s₂ := K₁.trans (k₂.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (round2_ok (by decide) (by rw [K₂.gpr _ (by decide), hz])) fun s₃ ⟨⟨M₃, hM₃, e₃⟩, k₃⟩ => ?_
  have K₃ : Keeps redW s s₃ := K₂.trans (k₃.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (adds_ok true rs rs th (s := s₃) (.inr (by simp)) rfl rfl (by decide)) fun s₄ ⟨e₄, k₄⟩ => ?_
  have K₄ : Keeps redW s s₄ := K₃.trans (k₄.mono (by decide))
  refine WP.mono (adc_ok s₄ .x13 .x7 .x7) fun t ⟨e₅, k₅, _⟩ => ?_
  refine ⟨?_, K₄.trans (k₅.mono (by decide))⟩
  rw [K₄.gpr .x7 (by decide), hz] at e₅
  have hc := Bool.toNat_le s₄.c
  simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add] at e₅
  rw [Nat.mod_eq_of_lt (by omega_using [hc])] at e₅
  rw [regsVal_append] at hT ⊢
  have hV : regsVal t rs + 2 ^ 384 * (t.gpr .x13).toNat = regsVal s₃ rs + regsVal s th := by
    rw [regsVal_keep k₅ (by decide), e₅, ← regsVal_keep (rs := th) K₃ (by decide)]
    simpa using e₄
  refine ⟨_, hV, rounds_arith e₁ e₂ e₃ hM₁ hM₂ hM₃ hT rfl⟩

end VG.Proof.Mont.AArch64.P384Field
