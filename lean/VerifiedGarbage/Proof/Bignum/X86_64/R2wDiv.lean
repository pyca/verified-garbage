import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Impl.Bignum.X86_64.R2Words

/-!
# `R² mod m` by word steps on x86-64: the estimate of the quotient

`quot`'s loop is restoring division, a bit at a time, of
`N = u₂ 2^64 + u₁` by `d ≥ 2^63` for `u₂ < d` (`divBit_ok`, `divLoop_ok`);
with `u₂ = d` its result is all ones, `2^64 - 1` (`quot_ok`): `q̂`.
-/

namespace VG.Proof.Bignum.X86_64.R2w

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Words
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.WordStep

theorem sxm1 : BitVec.signExtend 64 (-1 : BitVec 32) = BitVec.allOnes 64 := by decide

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
and rdx, r11; mov ecx, 0; mov r13d, 64`: `r9` the mask of `u₂ = d`, and then
`rdx` zero, for `u₂ ≤ d`. -/
theorem eqMask_ok {t : State} {u d : Nat} (hdx : t.gpr .rdx = BitVec.ofNat 64 u)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 d) (hu : u ≤ d) (hd : d < 2 ^ 64) :
    WP isa (.block [.mov .r9 (.reg .rsi), .alu .sub .r9 (.reg .rdx), .alu .cmp .r9 (.imm 1),
        .alu .sbb .r9 (.reg .r9), .mov .r11 (.reg .r9), .alu .xor .r11 (.imm (-1)), .alu .and .rdx (.reg .r11),
        .mov32 .rcx (.imm 0), .mov32 .r13 (.imm 64)]) t fun t' =>
      t'.gpr .r9 = mask (decide (u = d)) ∧ t'.gpr .rdx = BitVec.ofNat 64 (if u = d then 0 else u) ∧
      t'.gpr .rcx = BitVec.ofNat 64 0 ∧ t'.gpr .r13 = BitVec.ofNat 64 64 ∧ t'.mem = t.mem ∧
      Keep [.r9, .r11, .rdx, .rcx, .r13] t t' := by
  refine WP.mono (WP.keep [.r9, .r11, .rdx, .rcx, .r13] (Q := fun t' =>
      t'.gpr .r9 = mask (decide (u = d)) ∧ t'.gpr .rdx = BitVec.ofNat 64 (if u = d then 0 else u) ∧
      t'.gpr .rcx = BitVec.ofNat 64 0 ∧ t'.gpr .r13 = BitVec.ofNat 64 64 ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
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

/-- The estimate of the quotient of `x 2^64` by `m`:
`q̂ = min(⌊(u₂ 2^64 + u₁) / d⌋, 2^64 - 1)` into `rcx`, for `x` at `rbx` and `m`
at `r10` of `w` words, `u₂ ≤ d` and `d > 0`. -/
theorem quot_ok {t : State} {B : Addr} {Z w ex em : Nat} (hs : Scr t B Z)
    (hbx : t.gpr .rbx = off B ex) (h10 : t.gpr .r10 = off B em) (h12 : t.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 2 ≤ w) (hX : ex + 8 * w ≤ Z) (hM : em + 8 * w ≤ Z)
    (hu : (word t.mem B (ex + 8 * (w - 1))).toNat ≤ (word t.mem B (em + 8 * (w - 1))).toNat)
    (hd : 0 < (word t.mem B (em + 8 * (w - 1))).toNat) :
    WP isa quot t fun t' =>
      t'.gpr .rcx = BitVec.ofNat 64 (min (((word t.mem B (ex + 8 * (w - 1))).toNat * 2 ^ 64 +
        (word t.mem B (ex + 8 * (w - 2))).toNat) / (word t.mem B (em + 8 * (w - 1))).toNat) (2 ^ 64 - 1)) ∧
      t'.mem = t.mem ∧ Keep [.rsi, .rdx, .rax, .r9, .r11, .r14, .r15, .rcx, .r13] t t' := by
  have ofNat_toNat : ∀ x : BitVec 64, BitVec.ofNat 64 x.toNat = x := fun x => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold quot
  rw [show divHead = [.mov .rsi (.mem (ix .r10 .r12 (-8))), .mov .rdx (.mem (ix .rbx .r12 (-8))),
      .mov .rax (.mem (ix .rbx .r12 (-16)))] ++ [.mov .r9 (.reg .rsi), .alu .sub .r9 (.reg .rdx),
      .alu .cmp .r9 (.imm 1), .alu .sbb .r9 (.reg .r9), .mov .r11 (.reg .r9), .alu .xor .r11 (.imm (-1)),
      .alu .and .rdx (.reg .r11), .mov32 .rcx (.imm 0), .mov32 .r13 (.imm 64)] from rfl]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (divLoads_ok hs hbx h10 h12 hw hX hM) fun t₁ ⟨h1si, h1dx, h1ax, hm₁, k₁⟩ => ?_
  generalize word t.mem B (em + 8 * (w - 1)) = D at *
  generalize word t.mem B (ex + 8 * (w - 1)) = U2 at *
  generalize word t.mem B (ex + 8 * (w - 2)) = U1 at *
  refine WP.mono (eqMask_ok (u := U2.toNat) (d := D.toNat) (by rw [h1dx, ofNat_toNat])
    (by rw [h1si, ofNat_toNat]) hu D.isLt) fun t₂ ⟨h29, h2dx, h2cx, h213, hm₂, k₂⟩ => ?_
  have h2ax : t₂.gpr .rax = BitVec.ofNat 64 U1.toNat := by rw [k₂.gpr (by decide), h1ax, ofNat_toNat]
  have h2si : t₂.gpr .rsi = BitVec.ofNat 64 D.toNat := by rw [k₂.gpr (by decide), h1si, ofNat_toNat]
  refine WP.seq (WP.mono (divLoop_ok h2ax U1.isLt h2dx (by split <;> omega) h2si D.isLt h2cx h213)
    fun t₃ ⟨h3cx, hm₃, k₃⟩ => ?_)
  have h39 : t₃.gpr .r9 = mask (decide (U2.toNat = D.toNat)) := by rw [k₃.gpr (by decide), h29]
  refine WP.mono (WP.keep [.rcx] (Q := fun t' => t'.gpr .rcx = t₃.gpr .rcx ||| t₃.gpr .r9 ∧ t'.mem = t₃.mem)
    (by xrun) rfl) fun t' ⟨⟨hcx', hm'⟩, k'⟩ => ⟨?_, by rw [hm', hm₃, hm₂, hm₁],
      (((k₁.trans k₂).trans k₃).trans k').mono (by decide)⟩
  rw [hcx', h3cx, h39]
  have hD := D.isLt
  by_cases he : U2.toNat = D.toNat
  · simp only [he, ite_true, decide_true]
    rw [show mask true = BitVec.allOnes 64 from rfl, BitVec.or_allOnes,
      Nat.min_eq_right (by
        rw [Nat.le_div_iff_mul_le hd]
        exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
          (by rw [Nat.mul_comm]; exact Nat.le_add_right _ _))]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_allOnes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
  · simp only [he, ite_false, decide_false]
    rw [show mask false = 0#64 from rfl, BitVec.or_zero]
    have hlt : (U2.toNat * 2 ^ 64 + U1.toNat) / D.toNat < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul hd]
      have := Nat.mul_le_mul_right (2 ^ 64) (show U2.toNat + 1 ≤ D.toNat by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      have := U1.isLt
      rw [Nat.mul_comm (2 ^ 64)]; omega
    rw [Nat.min_eq_left (by omega)]

end VG.Proof.Bignum.X86_64.R2w
