import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Impl.Bignum.X86_64.R2Words

/-!
# `R² mod m` by word steps on x86-64: the estimate of the quotient

`quot` divides `N = u₂ 2^64 + u₁` by `d ≥ 2^63` for `u₂ < d` by the
reciprocal `v` of `d` (`quotMG_ok`, Möller and Granlund's division,
`mg_quot`); with `u₂ = d` its result is all ones, `2^64 - 1` (`quot_ok`): `q̂`.
`recip` computes `v` once, by restoring division, a bit at a time
(`divBit_ok`, `divLoop_ok`, `recip_ok`).
-/

namespace VG.Proof.Bignum.X86_64.R2w

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Words
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.WordStep

theorem sxm1 : BitVec.signExtend 64 (-1 : BitVec 32) = BitVec.allOnes 64 := by decide

theorem sxp1 : BitVec.signExtend 64 (1 : BitVec 32) = 1#64 := by decide

theorem ofNat_sub_ofNat64 {x d : Nat} (h : d ≤ x) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 d = BitVec.ofNat 64 (x - d) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem msb_toNat (a : BitVec 64) : (decide (2 ^ 64 ≤ a.toNat + a.toNat)).toNat = a.toNat / 2 ^ 63 := by
  have := a.isLt
  by_cases h : 2 ^ 64 ≤ a.toNat + a.toNat <;> simp only [h, decide_true, decide_false, Bool.toNat_true,
    Bool.toNat_false] <;> omega

theorem ofNat_beq_zero {j : Nat} (hj : j < 2 ^ 64) : (BitVec.ofNat 64 j == 0) = decide (j = 0) := by
  by_cases h : j = 0
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj] at this

/-- `add rax, rax; adc rdx, rdx`: the top bit `b` of `rax` into `rdx = 2 r + b`
(modulo `2^64`), with the carry. -/
theorem dbl2_ok {t : State} {a : BitVec 64} {r : Nat} (hax : t.gpr .rax = a)
    (hdx : t.gpr .rdx = BitVec.ofNat 64 r) (hr : r < 2 ^ 64) :
    WP isa (.block [.alu .add .rax (.reg .rax), .alu .adc .rdx (.reg .rdx)]) t fun t' =>
      t'.gpr .rax = a + a ∧ t'.gpr .rdx = BitVec.ofNat 64 (2 * r + a.toNat / 2 ^ 63) ∧
      t'.cf = some (decide (2 ^ 64 ≤ 2 * r + a.toNat / 2 ^ 63)) ∧ t'.mem = t.mem ∧ Keep [.rax, .rdx] t t' := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t' => t'.gpr .rax = a + a ∧
      t'.gpr .rdx = BitVec.ofNat 64 (2 * r + a.toNat / 2 ^ 63) ∧
      t'.cf = some (decide (2 ^ 64 ≤ 2 * r + a.toNat / 2 ^ 63)) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  xrun [hax, hdx]
  have hb := msb_toNat a
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool, hb]
    omega
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, hb, show r + r = 2 * r by omega]

/-- `sbb r11, r11`: the carry `c` as a mask. -/
theorem sbbMask_ok {t : State} {c : Bool} (hcf : t.cf = some c) :
    WP isa (.block [.alu .sbb .r11 (.reg .r11)]) t fun t' =>
      t'.gpr .r11 = mask c ∧ t'.mem = t.mem ∧ Keep [.r11] t t' := by
  refine WP.mono (WP.keep [.r11] (Q := fun t' => t'.gpr .r11 = mask c ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  xrun [hcf]
  rfl

/-- `mov r14, rdx; sub r14, rsi; sbb r15, r15; xor r15, -1`: `r14 = rdx - d`
and `r15` the mask of `d ≤ rdx`. -/
theorem cmpD_ok {t : State} {x d : Nat} (hdx : t.gpr .rdx = BitVec.ofNat 64 x)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 d) (hx : x < 2 ^ 64) (hd : d < 2 ^ 64) :
    WP isa (.block [.mov .r14 (.reg .rdx), .alu .sub .r14 (.reg .rsi), .alu .sbb .r15 (.reg .r15),
        .alu .xor .r15 (.imm (-1))]) t fun t' =>
      t'.gpr .r14 = BitVec.ofNat 64 x - BitVec.ofNat 64 d ∧ t'.gpr .r15 = mask (decide (d ≤ x)) ∧
      t'.mem = t.mem ∧ Keep [.r14, .r15] t t' := by
  refine WP.mono (WP.keep [.r14, .r15] (Q := fun t' => t'.gpr .r14 = BitVec.ofNat 64 x - BitVec.ofNat 64 d ∧
      t'.gpr .r15 = mask (decide (d ≤ x)) ∧ t'.mem = t.mem) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [hdx, hsi, sxm1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hd]
  unfold mask
  by_cases h : d ≤ x
  · simp only [h, show ¬ x < d by omega, decide_true, decide_false]; decide
  · simp only [h, show x < d by omega, decide_true, decide_false]; decide

/-- `or r15, r11; test r15, r15`: the mask of `p ∨ c`, and ZF clear iff it is
set. -/
theorem orTest_ok {t : State} {p c : Bool} (h15 : t.gpr .r15 = mask p) (h11 : t.gpr .r11 = mask c) :
    WP isa (.block [.alu .or .r15 (.reg .r11), .alu .test .r15 (.reg .r15)]) t fun t' =>
      t'.gpr .r15 = mask (p || c) ∧ t'.zf = some (!(p || c)) ∧ t'.mem = t.mem ∧ Keep [.r15] t t' := by
  refine WP.mono (WP.keep [.r15] (Q := fun t' => t'.gpr .r15 = mask (p || c) ∧ t'.zf = some (!(p || c)) ∧
      t'.mem = t.mem) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [h15, h11]
  cases p <;> cases c <;> decide

/-- `cmovne d, r`: `d := r` iff ZF is clear. -/
theorem cmovne_ok {t : State} {d r : Reg} {z : Bool} (hz : t.zf = some z) :
    WP isa (.block [.cmov .ne d (.reg r)]) t fun t' =>
      t'.gpr d = (if z then t.gpr d else t.gpr r) ∧ t'.mem = t.mem ∧ Keep [d] t t' := by
  refine WP.mono (WP.keep [d] (Q := fun t' => t'.gpr d = (if z then t.gpr d else t.gpr r) ∧ t'.mem = t.mem)
    ?_ (by cases d <;> rfl)) fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  apply WP.of_runBlock
  cases z <;> simp [runBlock_cons, runStep_some, runBlock_nil, exec, execCmov, readSrc, eval, hz,
    setReg_gpr, setReg_mem]

/-- `add rcx, rcx; sub rcx, r15; sub r13, 1`: `rcx := 2 q + p` for the mask
of `p` in `r15`, and the count down. -/
theorem qbit_ok {t : State} {q n : Nat} {p : Bool} (hcx : t.gpr .rcx = BitVec.ofNat 64 q)
    (h15 : t.gpr .r15 = mask p) (h13 : t.gpr .r13 = BitVec.ofNat 64 n) (hn : 1 ≤ n)
    (hn' : n < 2 ^ 64) :
    WP isa (.block [.alu .add .rcx (.reg .rcx), .alu .sub .rcx (.reg .r15), .alu .sub .r13 (.imm 1)]) t fun t' =>
      t'.gpr .rcx = BitVec.ofNat 64 (2 * q + p.toNat) ∧ t'.gpr .r13 = BitVec.ofNat 64 (n - 1) ∧
      t'.zf = some (decide (n - 1 = 0)) ∧ t'.mem = t.mem ∧ Keep [.rcx, .r13] t t' := by
  refine WP.mono (WP.keep [.rcx, .r13] (Q := fun t' => t'.gpr .rcx = BitVec.ofNat 64 (2 * q + p.toNat) ∧
      t'.gpr .r13 = BitVec.ofNat 64 (n - 1) ∧ t'.zf = some (decide (n - 1 = 0)) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  xrun [hcx, h15, h13]
  refine ⟨?_, ofNat64_pred hn hn', ?_⟩
  · unfold mask
    apply BitVec.eq_of_toNat_eq
    cases p <;> simp [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  · rw [ofNat64_pred hn hn']
    exact ofNat_beq_zero (by omega)

theorem ofNat_mod64 (x : Nat) : BitVec.ofNat 64 x = BitVec.ofNat 64 (x % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, Nat.mod_mod]

/-- A bit of the division: the top bit `b` of `rax` appended to the
remainder `r < d` in `rdx`, `d` subtracted if `2 r + b ≥ d`, and the bit
into the quotient `rcx`; the count `r13` down. -/
theorem divBit_ok {t : State} {a : BitVec 64} {r q d n : Nat}
    (hax : t.gpr .rax = a) (hdx : t.gpr .rdx = BitVec.ofNat 64 r) (hsi : t.gpr .rsi = BitVec.ofNat 64 d)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 q) (h13 : t.gpr .r13 = BitVec.ofNat 64 n)
    (hr : r < d) (hd : d < 2 ^ 64) (hn : 1 ≤ n) (hn' : n < 2 ^ 64) :
    WP isa (.block divBit) t fun t' =>
      t'.gpr .rax = a + a ∧
      t'.gpr .rdx = BitVec.ofNat 64 (if d ≤ 2 * r + a.toNat / 2 ^ 63 then 2 * r + a.toNat / 2 ^ 63 - d
        else 2 * r + a.toNat / 2 ^ 63) ∧
      t'.gpr .rcx = BitVec.ofNat 64 (2 * q + if d ≤ 2 * r + a.toNat / 2 ^ 63 then 1 else 0) ∧
      t'.gpr .r13 = BitVec.ofNat 64 (n - 1) ∧ t'.zf = some (decide (n - 1 = 0)) ∧ t'.mem = t.mem ∧
      Keep [.rax, .rdx, .r11, .r14, .r15, .rcx, .r13] t t' := by
  have hb : a.toNat / 2 ^ 63 < 2 := by have := a.isLt; omega
  generalize hx : 2 * r + a.toNat / 2 ^ 63 = x
  have hx2 : x < 2 * d := by omega
  rw [show divBit = [.alu .add .rax (.reg .rax), .alu .adc .rdx (.reg .rdx)] ++
      ([.alu .sbb .r11 (.reg .r11)] ++ ([.mov .r14 (.reg .rdx), .alu .sub .r14 (.reg .rsi),
        .alu .sbb .r15 (.reg .r15), .alu .xor .r15 (.imm (-1))] ++
      ([.alu .or .r15 (.reg .r11), .alu .test .r15 (.reg .r15)] ++ ([.cmov .ne .rdx (.reg .r14)] ++
      [.alu .add .rcx (.reg .rcx), .alu .sub .rcx (.reg .r15), .alu .sub .r13 (.imm 1)])))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (dbl2_ok hax hdx (by omega)) fun t₁ ⟨h1ax, h1dx, h1cf, h1m, k₁⟩ => ?_
  rw [hx] at h1dx h1cf
  rw [WP.block_append_iff]
  refine WP.mono (sbbMask_ok h1cf) fun t₂ ⟨h211, h2m, k₂⟩ => ?_
  rw [WP.block_append_iff]
  have h2dx : t₂.gpr .rdx = BitVec.ofNat 64 (x % 2 ^ 64) := by
    rw [k₂.gpr (by decide), h1dx, ← ofNat_mod64]
  have h2si : t₂.gpr .rsi = BitVec.ofNat 64 d := by rw [k₂.gpr (by decide), k₁.gpr (by decide), hsi]
  refine WP.mono (cmpD_ok h2dx h2si (Nat.mod_lt _ (by decide)) hd) fun t₃ ⟨h314, h315, h3m, k₃⟩ => ?_
  rw [WP.block_append_iff]
  have h311 : t₃.gpr .r11 = mask (decide (2 ^ 64 ≤ x)) := by rw [k₃.gpr (by decide), h211]
  refine WP.mono (orTest_ok h315 h311) fun t₄ ⟨h415, h4z, h4m, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cmovne_ok (d := .rdx) (r := .r14) h4z) fun t₅ ⟨h5dx, h5m, k₅⟩ => ?_
  -- Whether `d` is subtracted: `2 r + b ≥ d`.
  have htake : (decide (d ≤ x % 2 ^ 64) || decide (2 ^ 64 ≤ x)) = decide (d ≤ x) := by
    by_cases h : 2 ^ 64 ≤ x
    · simp only [h, decide_true, Bool.or_true, show d ≤ x by omega]
    · simp only [h, decide_false, Bool.or_false, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega)]
  rw [htake] at h415 h5dx
  have h5cx : t₅.gpr .rcx = BitVec.ofNat 64 q := by
    rw [k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide), hcx]
  have h513 : t₅.gpr .r13 = BitVec.ofNat 64 n := by
    rw [k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide), h13]
  have h515 : t₅.gpr .r15 = mask (decide (d ≤ x)) := by rw [k₅.gpr (by decide), h415]
  refine WP.mono (qbit_ok h5cx h515 h513 hn hn') fun t' ⟨hcx', h13', hz', hm', k'⟩ => ?_
  refine ⟨?_, ?_, ?_, h13', hz', by rw [hm', h5m, h4m, h3m, h2m, h1m], ?_⟩
  · rw [k'.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), h1ax]
  · rw [k'.gpr (by decide), h5dx]
    by_cases h : d ≤ x
    · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      rw [k₄.gpr (by decide), h314]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · simp only [h, decide_false, Bool.not_false, ite_true, ite_false]
      rw [k₄.gpr (by decide), k₃.gpr (by decide), h2dx, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega)]
  · rw [hcx']
    by_cases h : d ≤ x <;> simp [h]
  · exact ((((k₁.trans k₂).trans k₃).trans k₄).trans (k₅.trans k')).mono (by decide)

/-! ## The loop -/

theorem shl_mod {A j : Nat} (hj : j ≤ 64) : A * 2 ^ j % 2 ^ 64 = A % 2 ^ (64 - j) * 2 ^ j := by
  rw [show 2 ^ 64 = 2 ^ (64 - j) * 2 ^ j by rw [← Nat.pow_add]; congr 1; omega, Nat.mul_mod_mul_right]

theorem top_bit {A j : Nat} (hj : j < 64) :
    A * 2 ^ j % 2 ^ 64 / 2 ^ 63 = A % 2 ^ (64 - j) / 2 ^ (63 - j) := by
  rw [shl_mod (by omega), show 2 ^ 63 = 2 ^ (63 - j) * 2 ^ j by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mul_div_mul_right _ _ (Nat.two_pow_pos j)]

theorem div_split (A k : Nat) : A / 2 ^ k = 2 * (A / 2 ^ (k + 1)) + A % 2 ^ (k + 1) / 2 ^ k := by
  have e : 2 ^ (k + 1) * (A / 2 ^ (k + 1)) = 2 ^ k * (2 * (A / 2 ^ (k + 1))) := by
    rw [Nat.pow_succ, Nat.mul_assoc]
  conv => lhs; rw [← Nat.div_add_mod A (2 ^ (k + 1)), e, Nat.mul_add_div (Nat.two_pow_pos k)]

/-- After `j` bits of the division of `U 2^64 + A` by `d`. -/
def DivInv (t : State) (A U d : Nat) (j : Nat) (t' : State) : Prop :=
  ∃ q r : Nat, t'.gpr .rax = BitVec.ofNat 64 (A * 2 ^ j % 2 ^ 64) ∧ t'.gpr .rdx = BitVec.ofNat 64 r ∧
    t'.gpr .rcx = BitVec.ofNat 64 q ∧ t'.gpr .r13 = BitVec.ofNat 64 (64 - j) ∧
    U * 2 ^ j + A / 2 ^ (64 - j) = q * d + r ∧ r < d ∧ t'.mem = t.mem ∧
    Keep [.rax, .rdx, .r11, .r14, .r15, .rcx, .r13] t t'

/-- The 64 bits of the division: `rcx := ⌊(U 2^64 + A) / d⌋`, for `U < d`. -/
theorem divLoop_ok {t : State} {A U d : Nat} (hax : t.gpr .rax = BitVec.ofNat 64 A) (hA : A < 2 ^ 64)
    (hdx : t.gpr .rdx = BitVec.ofNat 64 U) (hU : U < d) (hsi : t.gpr .rsi = BitVec.ofNat 64 d)
    (hd : d < 2 ^ 64) (hcx : t.gpr .rcx = BitVec.ofNat 64 0) (h13 : t.gpr .r13 = BitVec.ofNat 64 64) :
    WP isa (.loop (.block divBit) .ne) t fun t' => t'.gpr .rcx = BitVec.ofNat 64 ((U * 2 ^ 64 + A) / d) ∧
      t'.mem = t.mem ∧ Keep [.rax, .rdx, .r11, .r14, .r15, .rcx, .r13] t t' := by
  refine wp_upto (a := 0) (N := 64) (by decide) (DivInv t A U d) ?_ ?_
    ⟨0, U, by rw [hax, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hA], hdx, hcx, h13,
      by rw [Nat.pow_zero, Nat.mul_one, Nat.div_eq_of_lt (show A < 2 ^ (64 - 0) from hA)]; omega, hU, rfl,
      Keep.refl _ _⟩
  · rintro j - hj t₁ ⟨q, r, h1ax, h1dx, h1cx, h113, hP, hr, hm, k⟩
    have hsi₁ : t₁.gpr .rsi = BitVec.ofNat 64 d := (k.gpr (by decide)).trans hsi
    refine WP.mono (divBit_ok h1ax h1dx hsi₁ h1cx h113 hr hd (by omega) (by omega))
      fun t' ⟨hax', hdx', hcx', h13', hz', hm', k'⟩ => ⟨?_, ?_⟩
    · rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega)
    have hbit : (BitVec.ofNat 64 (A * 2 ^ j % 2 ^ 64)).toNat / 2 ^ 63 = A % 2 ^ (64 - j) / 2 ^ (63 - j) := by
      rw [BitVec.toNat_ofNat, Nat.mod_mod, top_bit hj]
    rw [hbit] at hdx' hcx'
    have hb2 : A % 2 ^ (64 - j) / 2 ^ (63 - j) < 2 := by
      have h1 : 2 ^ (64 - j) = 2 ^ (63 - j) * 2 := by rw [show 64 - j = 63 - j + 1 by omega, Nat.pow_succ]
      apply Nat.div_lt_of_lt_mul
      rw [← h1]
      exact Nat.mod_lt A (Nat.two_pow_pos (64 - j))
    obtain ⟨hP', hr'⟩ := WordStep.divBit_inv hP hr hb2
    refine ⟨_, _, ?_, hdx', hcx', ?_, ?_, hr', by rw [hm', hm], (k.trans k').mono (by decide)⟩
    · rw [hax']
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show A * 2 ^ (j + 1) = A * 2 ^ j * 2 by rw [Nat.pow_succ, Nat.mul_assoc]]
      generalize A * 2 ^ j = p
      omega
    · rw [h13']; congr 1
    · rw [← hP', show 64 - (j + 1) = 63 - j by omega, div_split A (63 - j), show 63 - j + 1 = 64 - j by omega,
        Nat.pow_succ]
      grind
  · rintro t' ⟨q, r, -, -, hcx', -, hP, hr, hm, k⟩
    refine ⟨?_, hm, k⟩
    rw [hcx']
    congr 1
    rw [Nat.sub_self, Nat.pow_zero, Nat.div_one] at hP
    rw [hP, Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]

/-! ## The estimate -/

/-- `b + 8 i - 16` for `i = j ≥ 2`. -/
theorem addrm16 {b i p : Addr} {e j : Nat} (hb : b = off p e) (hi : i = BitVec.ofNat 64 j) (hj : 2 ≤ j) :
    b + i * BitVec.ofNat 64 8 + BitVec.ofInt 64 (-16) = off p (e + 8 * (j - 2)) := by
  have h8 : BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 (-16) = BitVec.ofNat 64 (8 * (j - 2)) := by
    rw [show (-16 : Int) = - ((16 : Nat) : Int) by rfl, BitVec.ofInt_neg, BitVec.ofInt_natCast,
      ← BitVec.sub_eq_add_neg, show 8 * j = 8 * (j - 2) + 16 by omega, BitVec.ofNat_add,
      BitVec.add_sub_cancel]
  subst hb hi
  rw [ofNat_mul8, off, BitVec.add_assoc, BitVec.add_assoc, h8, ← BitVec.ofNat_add]

/-- `mov r9, rsi; sub r9, rdx; cmp r9, 1; sbb r9, r9; mov r11, r9; xor r11, -1;
and rdx, r11`: `r9` the mask of `u₂ = d`, and then `rdx` zero, for `u₂ ≤ d`. -/
theorem eqMask_ok {t : State} {u d : Nat} (hdx : t.gpr .rdx = BitVec.ofNat 64 u)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 d) (hu : u ≤ d) (hd : d < 2 ^ 64) :
    WP isa (.block [.mov .r9 (.reg .rsi), .alu .sub .r9 (.reg .rdx), .alu .cmp .r9 (.imm 1),
        .alu .sbb .r9 (.reg .r9), .mov .r11 (.reg .r9), .alu .xor .r11 (.imm (-1)), .alu .and .rdx (.reg .r11)])
      t fun t' =>
      t'.gpr .r9 = mask (decide (u = d)) ∧ t'.gpr .rdx = BitVec.ofNat 64 (if u = d then 0 else u) ∧
      t'.mem = t.mem ∧ Keep [.r9, .r11, .rdx] t t' := by
  refine WP.mono (WP.keep [.r9, .r11, .rdx] (Q := fun t' =>
      t'.gpr .r9 = mask (decide (u = d)) ∧ t'.gpr .rdx = BitVec.ofNat 64 (if u = d then 0 else u) ∧
      t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [hdx, hsi, sxm1]
  have hu' : u < 2 ^ 64 := by omega
  rw [ofNat_sub_ofNat64 hu, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d - u < 2 ^ 64 by omega)]
  by_cases h : u = d
  · subst h
    simp only [Nat.sub_self, show (1 : BitVec 64).toNat = 1 from rfl, show 0 < 1 from Nat.one_pos,
      decide_true, ite_true]
    exact ⟨rfl, by rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool true) ^^^ BitVec.allOnes 64) = 0#64 by
      decide, BitVec.and_zero]⟩
  · simp only [show ¬ d - u < (1 : BitVec 64).toNat by
      rw [show (1 : BitVec 64).toNat = 1 from rfl]; omega, decide_false, h, ite_false]
    exact ⟨rfl, by rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool false) ^^^ BitVec.allOnes 64) =
      BitVec.allOnes 64 by decide, BitVec.and_allOnes]⟩

/-- `d = m[w - 1]`, `u₂ = x[w - 1]` and `u₁ = x[w - 2]` into `rsi`, `rdx`
and `rax`, for `x` at `rbx` and `m` at `r10`. -/
theorem divLoads_ok {t : State} {B : Addr} {Z w ex em : Nat} (hs : Scr t B Z)
    (hbx : t.gpr .rbx = off B ex) (h10 : t.gpr .r10 = off B em) (h12 : t.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 2 ≤ w) (hX : ex + 8 * w ≤ Z) (hM : em + 8 * w ≤ Z) :
    WP isa (.block [.mov .rsi (.mem (ix .r10 .r12 (-8))), .mov .rdx (.mem (ix .rbx .r12 (-8))),
        .mov .rax (.mem (ix .rbx .r12 (-16)))]) t fun t' =>
      t'.gpr .rsi = word t.mem B (em + 8 * (w - 1)) ∧ t'.gpr .rdx = word t.mem B (ex + 8 * (w - 1)) ∧
      t'.gpr .rax = word t.mem B (ex + 8 * (w - 2)) ∧ t'.mem = t.mem ∧ Keep [.rsi, .rdx, .rax] t t' := by
  refine WP.mono (WP.keep [.rsi, .rdx, .rax] (Q := fun t' =>
      t'.gpr .rsi = word t.mem B (em + 8 * (w - 1)) ∧ t'.gpr .rdx = word t.mem B (ex + 8 * (w - 1)) ∧
      t'.gpr .rax = word t.mem B (ex + 8 * (w - 2)) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  xrun [State.ea, ix, addrm8 h10 h12 (by omega), addrm8 hbx h12 (by omega), addrm16 hbx h12 hw,
    hs.ld (show em + 8 * (w - 1) + 8 ≤ Z by omega), hs.ld (show ex + 8 * (w - 1) + 8 ≤ Z by omega),
    hs.ld (show ex + 8 * (w - 2) + 8 ≤ Z by omega)]

/-! ## Division by the reciprocal -/

/-- `mov r14, rax; mov r13, rdx; mov rax, [rbp]; mul r13; add rax, r14;
adc rdx, r13`: `(rdx, rax) = v u + (u, a)`, for `v` at `rbp`. -/
theorem mgMul_ok {t : State} {u a vv : Nat} {pv : Addr} (hdx : t.gpr .rdx = BitVec.ofNat 64 u)
    (hax : t.gpr .rax = BitVec.ofNat 64 a) (hbp : t.gpr .rbp = pv) (hld : InRegions (t.rd ++ t.wr) pv 8)
    (hv : (t.mem.readW pv 64).toNat = vv) (hu : u < 2 ^ 64) (ha : a < 2 ^ 64)
    (hP : vv * u + a + 2 ^ 64 * u < 2 ^ 128) :
    WP isa (.block [.mov .r14 (.reg .rax), .mov .r13 (.reg .rdx), .mov .rax (.mem (at0 .rbp)), .mul .r13,
        .alu .add .rax (.reg .r14), .alu .adc .rdx (.reg .r13)]) t fun t' =>
      (t'.gpr .rax).toNat + 2 ^ 64 * (t'.gpr .rdx).toNat = vv * u + a + 2 ^ 64 * u ∧
      t'.gpr .r14 = BitVec.ofNat 64 a ∧ t'.mem = t.mem ∧ Keep [.r14, .r13, .rax, .rdx] t t' := by
  refine WP.mono (WP.keep [.r14, .r13, .rax, .rdx] (Q := fun t' =>
      (t'.gpr .rax).toNat + 2 ^ 64 * (t'.gpr .rdx).toNat = vv * u + a + 2 ^ 64 * u ∧
      t'.gpr .r14 = BitVec.ofNat 64 a ∧ t'.mem = t.mem) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [State.ea, at0, hbp, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hld, hdx, hax]
  have hU : (BitVec.ofNat 64 u).toNat = u := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu]
  have hl : vv * u ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
    rw [← hv]; exact Nat.mul_le_mul (by have := (t.mem.readW pv 64).isLt; omega) (by omega)
  rw [hU, hv]
  have e := VG.Proof.Poly1305.Limbs64.add_adc_toNat (BitVec.ofNat 64 (vv * u)) (BitVec.ofNat 64 a) (BitVec.ofNat 64 (vv * u / 2 ^ 64))
    (BitVec.ofNat 64 u) (by simp only [BitVec.toNat_ofNat]; omega)
  rw [e]; simp only [BitVec.toNat_ofNat]; omega

/-- `mov rcx, rdx; add rcx, 1; mov r13, rax; mov rax, rcx; mul rsi; sub r14, rax`:
the candidate `Q = q₁ + 1` and its remainder `a - Q d` modulo `2^64`. -/
theorem mgCand_ok {t : State} {q1 q0 a d : Nat} (hdx : t.gpr .rdx = BitVec.ofNat 64 q1)
    (hax : t.gpr .rax = BitVec.ofNat 64 q0) (h14 : t.gpr .r14 = BitVec.ofNat 64 a)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 d) (hq1 : q1 < 2 ^ 64) (ha : a < 2 ^ 64) (hd : d < 2 ^ 64) :
    WP isa (.block [.mov .rcx (.reg .rdx), .alu .add .rcx (.imm 1), .mov .r13 (.reg .rax), .mov .rax (.reg .rcx),
        .mul .rsi, .alu .sub .r14 (.reg .rax)]) t fun t' =>
      t'.gpr .rcx = BitVec.ofNat 64 ((q1 + 1) % 2 ^ 64) ∧ t'.gpr .r13 = BitVec.ofNat 64 q0 ∧
      t'.gpr .r14 = BitVec.ofNat 64 ((a + (2 ^ 64 - (q1 + 1) % 2 ^ 64 * d % 2 ^ 64)) % 2 ^ 64) ∧
      t'.mem = t.mem ∧ Keep [.rcx, .r13, .rax, .rdx, .r14] t t' := by
  refine WP.mono (WP.keep [.rcx, .r13, .rax, .rdx, .r14] (Q := fun t' =>
      t'.gpr .rcx = BitVec.ofNat 64 ((q1 + 1) % 2 ^ 64) ∧ t'.gpr .r13 = BitVec.ofNat 64 q0 ∧
      t'.gpr .r14 = BitVec.ofNat 64 ((a + (2 ^ 64 - (q1 + 1) % 2 ^ 64 * d % 2 ^ 64)) % 2 ^ 64) ∧
      t'.mem = t.mem) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  xrun [hdx, hax, h14, hsi, sxp1]
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt hq1, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt ha, Nat.mod_mod]
    omega

/-- `cmp r13, r14; sbb r15, r15; add rcx, r15; and r15, rsi; add r14, r15`:
the candidate one less, and its remainder `d` more, if `r > q₀`. -/
theorem mgFix1_ok {t : State} {Q r q0 d : Nat} (h13 : t.gpr .r13 = BitVec.ofNat 64 q0)
    (h14 : t.gpr .r14 = BitVec.ofNat 64 r) (hcx : t.gpr .rcx = BitVec.ofNat 64 Q)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 d) (hq0 : q0 < 2 ^ 64) (hr : r < 2 ^ 64) :
    WP isa (.block [.alu .cmp .r13 (.reg .r14), .alu .sbb .r15 (.reg .r15), .alu .add .rcx (.reg .r15),
        .alu .and .r15 (.reg .rsi), .alu .add .r14 (.reg .r15)]) t fun t' =>
      t'.gpr .rcx = BitVec.ofNat 64 ((Q + if q0 < r then 2 ^ 64 - 1 else 0) % 2 ^ 64) ∧
      t'.gpr .r14 = BitVec.ofNat 64 ((r + if q0 < r then d else 0) % 2 ^ 64) ∧
      t'.mem = t.mem ∧ Keep [.rcx, .r14, .r15, .r13] t t' := by
  refine WP.mono (WP.keep [.rcx, .r14, .r15, .r13] (Q := fun t' =>
      t'.gpr .rcx = BitVec.ofNat 64 ((Q + if q0 < r then 2 ^ 64 - 1 else 0) % 2 ^ 64) ∧
      t'.gpr .r14 = BitVec.ofNat 64 ((r + if q0 < r then d else 0) % 2 ^ 64) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [h13, h14, hcx, hsi]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  by_cases h : q0 < r
  · have em : (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (q0 < r)))) = BitVec.allOnes 64 := by
      rw [decide_eq_true h]; decide
    rw [em, BitVec.allOnes_and, ite_eq_left h, ite_eq_left h,
      show BitVec.allOnes 64 = BitVec.ofNat 64 (2 ^ 64 - 1) from rfl, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
      ← ofNat_mod64, ← ofNat_mod64]
    exact ⟨rfl, rfl⟩
  · have em : (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (q0 < r)))) = 0#64 := by
      rw [decide_eq_false h]; decide
    rw [em, BitVec.zero_and, ite_eq_right h, ite_eq_right h, Nat.add_zero, Nat.add_zero, BitVec.add_zero,
      BitVec.add_zero, ← ofNat_mod64, ← ofNat_mod64]
    exact ⟨rfl, rfl⟩

/-- `mov r15, rsi; sub r15, 1; cmp r15, r14; adc rcx, 0`: the candidate one
more if its remainder `r ≥ d`. -/
theorem mgFix2_ok {t : State} {Q r d : Nat} (h14 : t.gpr .r14 = BitVec.ofNat 64 r)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 Q) (hsi : t.gpr .rsi = BitVec.ofNat 64 d) (hr : r < 2 ^ 64)
    (hd : d < 2 ^ 64) (hd1 : 1 ≤ d) :
    WP isa (.block [.mov .r15 (.reg .rsi), .alu .sub .r15 (.imm 1), .alu .cmp .r15 (.reg .r14),
        .alu .adc .rcx (.imm 0)]) t fun t' =>
      t'.gpr .rcx = BitVec.ofNat 64 ((Q + if d - 1 < r then 1 else 0) % 2 ^ 64) ∧
      t'.mem = t.mem ∧ Keep [.rcx, .r15] t t' := by
  refine WP.mono (WP.keep [.rcx, .r15] (Q := fun t' =>
      t'.gpr .rcx = BitVec.ofNat 64 ((Q + if d - 1 < r then 1 else 0) % 2 ^ 64) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  xrun [h14, hcx, hsi, sxp1, sx0]
  have e : (BitVec.ofNat 64 d - 1).toNat = d - 1 := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_sub_ofNat64 hd1, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  apply BitVec.eq_of_toNat_eq
  by_cases h : d - 1 < r
  · rw [ite_eq_left h, decide_eq_true h]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
      Bool.toNat_true, show (0 : BitVec 64).toNat = 0 from rfl]
    omega
  · rw [ite_eq_right h, decide_eq_false h]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
      Bool.toNat_false, show (0 : BitVec 64).toNat = 0 from rfl]
    omega

/-- `⌊(u₂ 2^64 + u₁) / d⌋` into `rcx`, for `u₂ < d` in `rdx`, `u₁` in `rax`,
`d ≥ 2^63` in `rsi` and `v = ⌊(2^128 - 1) / d⌋ - 2^64` at `rbp`. -/
theorem quotMG_ok {t : State} {u a d : Nat} {pv : Addr} (hdx : t.gpr .rdx = BitVec.ofNat 64 u)
    (hax : t.gpr .rax = BitVec.ofNat 64 a) (hsi : t.gpr .rsi = BitVec.ofNat 64 d) (hbp : t.gpr .rbp = pv)
    (hld : InRegions (t.rd ++ t.wr) pv 8) (hv : (t.mem.readW pv 64).toNat = (2 ^ 128 - 1) / d - 2 ^ 64)
    (hd : 2 ^ 63 ≤ d) (hd' : d < 2 ^ 64) (hu : u < d) (ha : a < 2 ^ 64) :
    WP isa (.block quotMG) t fun t' => t'.gpr .rcx = BitVec.ofNat 64 ((u * 2 ^ 64 + a) / d) ∧
      t'.mem = t.mem ∧ Keep [.r14, .r13, .rax, .rdx, .rcx, .r15] t t' := by
  have hd0 : 0 < d := by omega
  -- `V = ⌊(2^128 - 1) / d⌋ ≥ 2^64` and `V u + a < 2^128`.
  have hVd : (2 ^ 128 - 1) / d * d ≤ 2 ^ 128 - 1 := Nat.div_mul_le_self _ _
  have hVB : 2 ^ 64 ≤ (2 ^ 128 - 1) / d := by
    rw [Nat.le_div_iff_mul_le hd0]
    have := Nat.mul_le_mul_left (2 ^ 64) (show d ≤ 2 ^ 64 - 1 by omega)
    omega
  generalize hV : (2 ^ 128 - 1) / d = V at hVd hVB hv
  have hVu : V * u + V ≤ V * d := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hu
  have hVd' : V * d = d * V := Nat.mul_comm _ _
  have hPe : (V - 2 ^ 64) * u + a + 2 ^ 64 * u = V * u + a := by
    rw [Nat.sub_mul]; have := Nat.mul_le_mul_right u hVB; omega
  have hPB : V * u + a < 2 ^ 128 := by rw [Nat.mul_comm d V] at hVd'; omega
  rw [show quotMG = [.mov .r14 (.reg .rax), .mov .r13 (.reg .rdx), .mov .rax (.mem (at0 .rbp)), .mul .r13,
      .alu .add .rax (.reg .r14), .alu .adc .rdx (.reg .r13)] ++ ([.mov .rcx (.reg .rdx), .alu .add .rcx (.imm 1),
      .mov .r13 (.reg .rax), .mov .rax (.reg .rcx), .mul .rsi, .alu .sub .r14 (.reg .rax)] ++
      ([.alu .cmp .r13 (.reg .r14), .alu .sbb .r15 (.reg .r15), .alu .add .rcx (.reg .r15),
      .alu .and .r15 (.reg .rsi), .alu .add .r14 (.reg .r15)] ++ ([.mov .r15 (.reg .rsi), .alu .sub .r15 (.imm 1),
      .alu .cmp .r15 (.reg .r14), .alu .adc .rcx (.imm 0)] : List Instr))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (mgMul_ok hdx hax hbp hld hv (by omega) ha (by rw [hPe]; exact hPB))
    fun t₁ ⟨hP₁, h14₁, hm₁, k₁⟩ => ?_
  rw [hPe] at hP₁
  have h1dx : t₁.gpr .rdx = BitVec.ofNat 64 ((V * u + a) / 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul (by decide)]; omega)]
    have := (t₁.gpr .rax).isLt; omega
  have h1ax : t₁.gpr .rax = BitVec.ofNat 64 ((V * u + a) % 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_mod]
    have := (t₁.gpr .rax).isLt; omega
  have h1si : t₁.gpr .rsi = BitVec.ofNat 64 d := (k₁.gpr (by decide)).trans hsi
  have hq1 : (V * u + a) / 2 ^ 64 < 2 ^ 64 := by rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
  rw [WP.block_append_iff]
  refine WP.mono (mgCand_ok h1dx h1ax h14₁ h1si hq1 ha hd')
    fun t₂ ⟨h2cx, h213, h214, hm₂, k₂⟩ => ?_
  have h2si : t₂.gpr .rsi = BitVec.ofNat 64 d := (k₂.gpr (by decide)).trans h1si
  rw [WP.block_append_iff]
  refine WP.mono (mgFix1_ok h213 h214 h2cx h2si (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))) fun t₃ ⟨h3cx, h314, hm₃, k₃⟩ => ?_
  have h3si : t₃.gpr .rsi = BitVec.ofNat 64 d := (k₃.gpr (by decide)).trans h2si
  refine WP.mono (mgFix2_ok h314 h3cx h3si (Nat.mod_lt _ (by decide)) hd' (by omega))
    fun t' ⟨hcx', hm', k'⟩ => ⟨?_, by rw [hm', hm₃, hm₂, hm₁], ((k₁.trans k₂).trans (k₃.trans k')).mono (by decide)⟩
  rw [hcx']
  congr 1
  exact mg_quot hd' hd hu ha hV.symm rfl rfl rfl rfl rfl

/-- The estimate of the quotient of `x 2^64` by `m`:
`q̂ = min(⌊(u₂ 2^64 + u₁) / d⌋, 2^64 - 1)` into `rcx`, for `x` at `rbx` and `m`
at `r10` of `w` words, `u₂ ≤ d`, `d ≥ 2^63`, and `v` at `rbp`. -/
theorem quot_ok {t : State} {B : Addr} {Z w ex em ev : Nat} (hs : Scr t B Z)
    (hbx : t.gpr .rbx = off B ex) (h10 : t.gpr .r10 = off B em) (h12 : t.gpr .r12 = BitVec.ofNat 64 w)
    (hbp : t.gpr .rbp = off B ev) (hw : 2 ≤ w) (hX : ex + 8 * w ≤ Z) (hM : em + 8 * w ≤ Z) (hE : ev + 8 ≤ Z)
    (hu : (word t.mem B (ex + 8 * (w - 1))).toNat ≤ (word t.mem B (em + 8 * (w - 1))).toNat)
    (hd : 2 ^ 63 ≤ (word t.mem B (em + 8 * (w - 1))).toNat)
    (hv : (word t.mem B ev).toNat = (2 ^ 128 - 1) / (word t.mem B (em + 8 * (w - 1))).toNat - 2 ^ 64) :
    WP isa (.block quot) t fun t' =>
      t'.gpr .rcx = BitVec.ofNat 64 (min (((word t.mem B (ex + 8 * (w - 1))).toNat * 2 ^ 64 +
        (word t.mem B (ex + 8 * (w - 2))).toNat) / (word t.mem B (em + 8 * (w - 1))).toNat) (2 ^ 64 - 1)) ∧
      t'.mem = t.mem ∧ Keep [.rsi, .rdx, .rax, .r9, .r11, .r14, .r15, .rcx, .r13] t t' := by
  have ofNat_toNat : ∀ x : BitVec 64, BitVec.ofNat 64 x.toNat = x := fun x => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [show quot = [.mov .rsi (.mem (ix .r10 .r12 (-8))), .mov .rdx (.mem (ix .rbx .r12 (-8))),
      .mov .rax (.mem (ix .rbx .r12 (-16)))] ++ ([.mov .r9 (.reg .rsi), .alu .sub .r9 (.reg .rdx),
      .alu .cmp .r9 (.imm 1), .alu .sbb .r9 (.reg .r9), .mov .r11 (.reg .r9), .alu .xor .r11 (.imm (-1)),
      .alu .and .rdx (.reg .r11)] ++ (quotMG ++ ([.alu .or .rcx (.reg .r9)] : List Instr))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (divLoads_ok hs hbx h10 h12 hw hX hM) fun t₁ ⟨h1si, h1dx, h1ax, hm₁, k₁⟩ => ?_
  have h1bp : t₁.gpr .rbp = off B ev := (k₁.gpr (by decide)).trans hbp
  have hs₁ := hs.congr k₁.2.2
  have hld := hs₁.ld hE
  generalize word t.mem B (em + 8 * (w - 1)) = D at *
  generalize word t.mem B (ex + 8 * (w - 1)) = U2 at *
  generalize word t.mem B (ex + 8 * (w - 2)) = U1 at *
  rw [WP.block_append_iff]
  refine WP.mono (eqMask_ok (u := U2.toNat) (d := D.toNat) (by rw [h1dx, ofNat_toNat])
    (by rw [h1si, ofNat_toNat]) hu D.isLt) fun t₂ ⟨h29, h2dx, hm₂, k₂⟩ => ?_
  have h2ax : t₂.gpr .rax = BitVec.ofNat 64 U1.toNat := by rw [k₂.gpr (by decide), h1ax, ofNat_toNat]
  have h2si : t₂.gpr .rsi = BitVec.ofNat 64 D.toNat := by rw [k₂.gpr (by decide), h1si, ofNat_toNat]
  have h2bp : t₂.gpr .rbp = off B ev := (k₂.gpr (by decide)).trans h1bp
  have hs₂ := hs₁.congr k₂.2.2
  rw [WP.block_append_iff]
  have a1 := hs₂.ld hE
  have a2 : (t₂.mem.readW (off B ev) 64).toNat = (2 ^ 128 - 1) / D.toNat - 2 ^ 64 := by rw [hm₂, hm₁]; exact hv
  have a3 : (if U2.toNat = D.toNat then 0 else U2.toNat) < D.toNat := by split <;> omega
  refine WP.mono (quotMG_ok h2dx h2ax h2si h2bp a1 a2 hd D.isLt a3 U1.isLt) fun t₃ ⟨h3cx, hm₃, k₃⟩ => ?_
  have h39 : t₃.gpr .r9 = mask (decide (U2.toNat = D.toNat)) := by rw [k₃.gpr (by decide), h29]
  refine WP.mono (WP.keep [.rcx] (Q := fun t' => t'.gpr .rcx = t₃.gpr .rcx ||| t₃.gpr .r9 ∧ t'.mem = t₃.mem)
    (by xrun) rfl) fun t' ⟨⟨hcx', hm'⟩, k'⟩ => ⟨?_, by rw [hm', hm₃, hm₂, hm₁],
      (((k₁.trans k₂).trans k₃).trans k').mono (by decide)⟩
  rw [hcx', h3cx, h39]
  have hD := D.isLt
  have hd0 : 0 < D.toNat := by omega
  by_cases he : U2.toNat = D.toNat
  · simp only [he, ite_true, decide_true]
    rw [show mask true = BitVec.allOnes 64 from rfl, BitVec.or_allOnes,
      Nat.min_eq_right (by
        rw [Nat.le_div_iff_mul_le hd0]
        exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
          (by rw [Nat.mul_comm]; exact Nat.le_add_right _ _))]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_allOnes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
  · simp only [he, ite_false, decide_false]
    rw [show mask false = 0#64 from rfl, BitVec.or_zero]
    have hlt : (U2.toNat * 2 ^ 64 + U1.toNat) / D.toNat < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul hd0]
      have := Nat.mul_le_mul_right (2 ^ 64) (show U2.toNat + 1 ≤ D.toNat by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      have := U1.isLt
      rw [Nat.mul_comm (2 ^ 64)]; omega
    rw [Nat.min_eq_left (by omega)]

/-! ## The reciprocal -/

/-- `v = ⌊(2^128 - 1) / d⌋ - 2^64 = ⌊((2^64 - 1 - d) 2^64 + 2^64 - 1) / d⌋`. -/
theorem recip_eq {d : Nat} (hd : d < 2 ^ 64) (hd0 : 0 < d) :
    ((2 ^ 64 - 1 - d) * 2 ^ 64 + (2 ^ 64 - 1)) / d = (2 ^ 128 - 1) / d - 2 ^ 64 := by
  have e : (2 ^ 64 - 1 - d) * 2 ^ 64 + (2 ^ 64 - 1) = 2 ^ 128 - 1 - 2 ^ 64 * d := by
    rw [Nat.sub_mul, Nat.sub_mul]
    have := Nat.mul_le_mul_right (2 ^ 64) (show d ≤ 2 ^ 64 - 1 by omega)
    rw [Nat.sub_mul] at this
    rw [Nat.mul_comm d]; omega
  rw [e, Nat.mul_comm (2 ^ 64) d, Nat.sub_mul_div]

/-- `recip`: `v` for `d = m[w - 1] ≥ 2^63` into the word at `r8`, for `m` at
`r10` of `w` words. -/
theorem recip_ok {t : State} {B : Addr} {Z w em ev : Nat} (hs : Scr t B Z)
    (h10 : t.gpr .r10 = off B em) (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (h8 : t.gpr .r8 = off B ev)
    (hw : 1 ≤ w) (hM : em + 8 * w ≤ Z) (hE : ev + 8 ≤ Z)
    (hd : 2 ^ 63 ≤ (word t.mem B (em + 8 * (w - 1))).toNat) :
    WP isa recip t fun t' => t'.mem = t.mem.writeW (off B ev)
        (BitVec.ofNat 64 ((2 ^ 128 - 1) / (word t.mem B (em + 8 * (w - 1))).toNat - 2 ^ 64)) ∧
      Keep [.rsi, .rdx, .rax, .rcx, .r13, .r11, .r14, .r15] t t' := by
  have ofNat_toNat : ∀ x : BitVec 64, BitVec.ofNat 64 x.toNat = x := fun x => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  generalize hD : word t.mem B (em + 8 * (w - 1)) = D at hd
  have hD' := D.isLt
  unfold recip
  refine WP.seq (WP.mono (WP.keep [.rsi, .rdx, .rax, .rcx, .r13] (Q := fun t' =>
      t'.gpr .rsi = BitVec.ofNat 64 D.toNat ∧ t'.gpr .rdx = BitVec.ofNat 64 (2 ^ 64 - 1 - D.toNat) ∧
      t'.gpr .rax = BitVec.ofNat 64 (2 ^ 64 - 1) ∧ t'.gpr .rcx = BitVec.ofNat 64 0 ∧
      t'.gpr .r13 = BitVec.ofNat 64 64 ∧ t'.mem = t.mem) (by
    xrun [State.ea, ix, addrm8 h10 h12 hw, hs.ld (show em + 8 * (w - 1) + 8 ≤ Z by omega), sxm1]
    show word t.mem B (em + 8 * (w - 1)) = _ ∧ word t.mem B (em + 8 * (w - 1)) ^^^ _ = _
    rw [hD, ofNat_toNat, BitVec.xor_allOnes]
    refine ⟨rfl, BitVec.eq_of_toNat_eq ?_⟩
    rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) rfl) fun t₁ ⟨⟨h1si, h1dx, h1ax, h1cx, h113, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (divLoop_ok h1ax (by decide) h1dx (by omega) h1si hD' h1cx h113)
    fun t₂ ⟨h2cx, hm₂, k₂⟩ => ?_)
  have h28 : t₂.gpr .r8 = off B ev := by rw [k₂.gpr (by decide), k₁.gpr (by decide), h8]
  have hs₂ := (hs.congr k₁.2.2).congr k₂.2.2
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t₂.mem.writeW (off B ev) (t₂.gpr .rcx)) (by
    xrun [State.ea, at0, h28, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hs₂.st hE]) rfl) fun t' ⟨hm', k'⟩ => ⟨?_, ?_⟩
  · rw [hm', hm₂, hm₁, h2cx, recip_eq hD' (by omega)]
  · exact ((k₁.trans k₂).trans k').mono (by decide)

end VG.Proof.Bignum.X86_64.R2w
