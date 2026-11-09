module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PubMont
public import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontRounds
import VerifiedGarbage.Proof.Bignum.RISCV64.PubSan
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.PackedRead
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA public-key operation on RISC-V: the power

`power_ok`: `x^(E mod 2^33) mod n` into array 4, by `one`, `x R mod n`
(`montOp 6 4 1`), the leading zeros of `e` skipped (`skip`), `a := x R mod
n` (`initA`) and a square per later bit and a multiplication by `x R mod n`
per later set bit but the last (`bits`), as on PPC64LE.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pub

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.PublicChecked
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot slot_sep slot_le Arrays)

/-- Array `j`'s number. -/
abbrev V (m : Mem) (B : Addr) (w j : Nat) : Nat := wordsVal m B (slot w j) w

/-- The arrays the power changes: all but array 0. -/
def powJs : List Nat := [1, 2, 3, 4, 5, 6, 7]

/-- An array apart from those changed keeps its number. -/
theorem arrays_V {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m') {j : Nat}
    (hjs : ∀ k ∈ js, k ≠ j) (hfit : slot w j + 8 * w ≤ 2 ^ 64) : V m' B w j = V m B w j := by
  simp only [V]
  rw [VG.Proof.Bignum.wordsVal_read, VG.Proof.Bignum.read_eq_wv, VG.Proof.Bignum.wordsVal_read,
    VG.Proof.Bignum.read_eq_wv]
  exact h.wv_eq (fun k hk => by have := slot_sep (w := w) (Ne.symm (hjs k hk)); omega_arith) hfit

/-- What the Montgomery multiplications need, with `N` the modulus in
array 0. -/
structure Ctx (s : State) (B : Addr) (Z w N : Nat) : Prop where
  scr : Scr s B Z
  w2 : 2 ≤ w
  w31 : w < 2 ^ 31
  hZ : slot w 8 ≤ Z
  a7 : s.gpr .a7 = off B (slot w 0)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))
  t0 : s.gpr .t0 = BitVec.ofNat 64 w
  inv : ((word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  n : V s.mem B w 0 = N

theorem Ctx.sl {s : State} {B : Addr} {Z w N : Nat} (h : Ctx s B Z w N) {j : Nat} (hj : j < 8) :
    slot w j + 8 * (w + 2) ≤ Z :=
  Nat.le_trans (slot_le hj) h.hZ

theorem Ctx.vj {s : State} {B : Addr} {Z w N : Nat} (h : Ctx s B Z w N) {m m' : Mem} {js : List Nat}
    {j : Nat} (hj : j < 8) (hjs : ∀ k ∈ js, k ≠ j) (o : Arrays B w js m m') :
    V m' B w j = V m B w j := by
  have hnw := h.scr.nowrap
  have := h.sl hj
  exact arrays_V o hjs (by omega_arith)

/-- The context after code that writes only arrays 1–7 and none of `a7`,
`s5`, `t0`, `t1`. -/
theorem Ctx.of {s t : State} {B : Addr} {Z w N : Nat} (h : Ctx s B Z w N) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ [Reg.a7, .s5, .t0, .t1], r ∉ rs) (o : Arrays B w powJs s.mem t.mem) : Ctx t B Z w N := by
  have hnw := h.scr.nowrap
  have hrs' : ∀ r ∈ [Reg.a7, .s5, .t0, .t1], t.gpr r = s.gpr r := fun r hr => k.gpr (hrs r hr)
  have s0 := h.sl (j := 0) (by decide)
  refine ⟨h.scr.congr k.2.2, h.w2, h.w31, h.hZ, (hrs' .a7 (by decide)).trans h.a7,
    (hrs' .s5 (by decide)).trans h.s5, (hrs' .t0 (by decide)).trans h.t0, ?_, ?_⟩
  · rw [hrs' .t1 (by decide), o.word_eq (fun j hj => by
      have : j ≠ 0 := by revert j; decide
      have := slot_sep (w := w) (Ne.symm this); omega_arith) (by omega_arith)]
    exact h.inv
  · rw [← h.n]
    exact h.vj (by decide) (by decide) o

theorem arrays_pow {w : Nat} {m m' : Mem} {B : Addr} {js : List Nat} (h : Arrays B w js m m')
    (hjs : ∀ j ∈ js, j ∈ powJs) : Arrays B w powJs m m' :=
  h.mono hjs

/-- A Montgomery multiplication in the context. -/
theorem Ctx.mont {s : State} {B : Addr} {Z w N : Nat} (h : Ctx s B Z w N) {o a b : Nat} (ho : o < 8) (ha : a < 8)
    (hb : b < 8) (ho1 : o ≠ 0) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2) (hb2 : b ≠ 2) (hB : V s.mem B w b < N) :
    WP isa (montOp o a b) s fun t =>
      (Ctx t B Z w N ∧ V t.mem B w o < N ∧
        V t.mem B w o * 2 ^ (64 * w) % N = V s.mem B w a * V s.mem B w b % N ∧
        (∀ j < 8, j ≠ 2 → j ≠ 3 → j ≠ o → V t.mem B w j = V s.mem B w j) ∧
        Arrays B w powJs s.mem t.mem) ∧ Keep montRegs s t := by
  refine WP.mono (montOp_ok h.scr ho ha hb ho2 ho3 ha2 hb2 h.w2 h.w31 h.hZ h.a7 h.s5 h.t0 h.inv
    (by rw [show wordsVal s.mem B (slot w 0) w = N from h.n]; exact hB)) fun t ⟨⟨hlt, he, out⟩, k⟩ => ?_
  have op : Arrays B w powJs s.mem t.mem := arrays_pow out (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    simp only [powJs, List.mem_cons, List.not_mem_nil, or_false]; omega_arith)
  rw [show wordsVal s.mem B (slot w 0) w = N from h.n] at hlt he
  exact ⟨⟨h.of k (by decide) op, hlt, he,
    fun j hj h2 h3 hjo => h.vj hj (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega_arith) out, op⟩, k⟩

/-- A dedicated square of the running power in the public-operation context. -/
theorem Ctx.square {s : State} {B : Addr} {Z w N : Nat} (h : Ctx s B Z w N)
    (hA : V s.mem B w 5 < N) :
    WP isa square s fun t =>
      (Ctx t B Z w N ∧ V t.mem B w 5 < N ∧
        V t.mem B w 5 * 2 ^ (64 * w) % N = V s.mem B w 5 * V s.mem B w 5 % N ∧
        (∀ j < 8, j ≠ 1 → j ≠ 2 → j ≠ 3 → j ≠ 5 → V t.mem B w j = V s.mem B w j) ∧
        Arrays B w powJs s.mem t.mem) ∧ Keep montRegs s t := by
  refine WP.mono (square_ok h.scr h.w2 h.w31 h.hZ h.a7 h.s5 h.t0 h.inv
    (by rw [show wordsVal s.mem B (slot w 0) w = N from h.n]; exact hA))
    fun t ⟨⟨hlt, he, out⟩, k⟩ => ?_
  have op : Arrays B w powJs s.mem t.mem := arrays_pow out (by decide)
  rw [show wordsVal s.mem B (slot w 0) w = N from h.n] at hlt he
  exact ⟨⟨h.of k (by decide) op, hlt, he,
    fun j hj h1 h2 h3 h5 => h.vj hj (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega_arith) out, op⟩, k⟩

/-! ## The arithmetic of the scan -/

theorem sq_step {A S X c R N : Nat} (hR : Nat.Coprime R N) (hA : A % N = X ^ c * R % N)
    (hS : S * R % N = A * A % N) : S % N = X ^ (2 * c) * R % N := by
  refine VG.Proof.Bignum.mont_cancel hR ?_
  rw [hS, Nat.mul_mod, hA, ← Nat.mul_mod, Nat.two_mul, Nat.pow_add]
  congr 1
  grind

theorem mul_step {S P X c R N XM : Nat} (hR : Nat.Coprime R N) (hS : S % N = X ^ (2 * c) * R % N)
    (hX : XM % N = X * R % N) (hP : P * R % N = S * XM % N) : P % N = X ^ (2 * c + 1) * R % N := by
  refine VG.Proof.Bignum.mont_cancel hR ?_
  rw [hP, Nat.mul_mod, hS, hX, ← Nat.mul_mod, Nat.pow_succ]
  congr 1
  grind

theorem top_bit (x : BitVec 64) :
    x >>> 63 = BitVec.ofNat 64 (if 2 ^ 63 ≤ x.toNat then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have := x.isLt
  split <;> omega_arith

theorem pow_step (a i : Nat) : a * 2 ^ (i + 1) = 2 * (a * 2 ^ i) := by
  rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 2]

theorem r24_shift (x : BitVec 64) :
    (x <<< 1).toNat + (if 2 ^ 63 ≤ x.toNat then 1 else 0) * 2 ^ 64 = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have := x.isLt
  split <;> omega_arith

/-- The last bit: `y R ≡ x^b S` with `S R ≡ a²` and `a ≡ x^c R`. -/
theorem last_step {A S Y X c R N : Nat} (hR : Nat.Coprime R N) (hA : A % N = X ^ c * R % N)
    (hS : S * R % N = A * A % N) (b : Bool) (hY : Y * R % N = (if b then X else 1) * S % N) :
    Y % N = X ^ (2 * c + if b then 1 else 0) % N := by
  have hS' := sq_step hR hA hS
  refine VG.Proof.Bignum.mont_cancel hR ?_
  rw [hY, Nat.mul_mod, hS', ← Nat.mul_mod]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_mul, Nat.add_zero]
  · simp only [↓reduceIte]
    congr 1
    rw [Nat.pow_succ]
    grind

theorem shift_arith {c t r r' : Nat} (hr : r' + t * 2 ^ 64 = 2 * r) :
    (2 * c + t) * 2 ^ 64 + r' = 2 * (c * 2 ^ 64 + r) := by
  omega_arith

/-- A bit of the scan: `c` and `a ≡ x^c R` for the bits after `q` shifts. -/
theorem bit_step {A S A' X XM c R N r r' v q : Nat} (hR : Nat.Coprime R N) (hA : A % N = X ^ c * R % N)
    (hXM : XM % N = X * R % N) (hS : S * R % N = A * A % N) (b : Bool)
    (hA' : if b then A' * R % N = S * XM % N else A' = S) (hc : c * 2 ^ 64 + r = v * 2 ^ 31 * 2 ^ q)
    (hr : r' + (if b then 1 else 0) * 2 ^ 64 = 2 * r) :
    (2 * c + if b then 1 else 0) * 2 ^ 64 + r' = v * 2 ^ 31 * 2 ^ (q + 1) ∧
      A' % N = X ^ (2 * c + if b then 1 else 0) * R % N := by
  have hS' := sq_step hR hA hS
  refine ⟨by rw [pow_step (v * 2 ^ 31) q, ← hc]; exact shift_arith hr, ?_⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at hA' ⊢
    rw [hA', Nat.add_zero]; exact hS'
  · simp only [↓reduceIte] at hA' ⊢
    exact mul_step hR hS' hXM hA'

/-! ## `one` -/

theorem one_word (m : Mem) (B : Addr) (d : Nat) {w : Nat} (hw : 1 ≤ w) (hfit : d + 8 * w ≤ 2 ^ 64)
    (hz : ∀ i < w, Mont.word m B (d + 8 * i) = 0) :
    wordsVal (m.writeW (off B d) (BitVec.ofNat 64 1)) B d w = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega_arith⟩
  have ho := writeW_outside m B (d := d) (BitVec.ofNat 64 1) (by omega_arith)
  simp only [wordsVal]
  rw [VG.Proof.Mont.word_writeW_self, Outside.wordsVal ho (by omega_arith) (by omega_arith),
    wsv_zero (fun i hi => by rw [show d + 8 + 8 * i = d + 8 * (i + 1) by omega_arith]; exact hz _ (by omega_arith))]
  rfl

/-- `one`: 1 in array 7. -/
theorem oneP_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hw1 : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) :
    WP isa PublicChecked.one s fun t =>
      (V t.mem B w 7 = 1 ∧ Outside B (slot w 7) (8 * w) s.mem t.mem) ∧ Keep [.s0, .t3, .t5] s t := by
  have hnw := hs.nowrap
  have s7 := slot_le (w := w) (j := 7) (by decide)
  have al := slot_al w
  unfold PublicChecked.one
  refine WP.seq (WP.mono (base_ok (rd := .t3) (by decide) h7 h5 7) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr k1.2.2) a3 ((k1.gpr (by decide)).trans ht0) hw1 hw' (al 7)
    (by omega_arith)) fun s₂ ⟨⟨_, hz, out₂⟩, k₂⟩ => ?_)
  have k12 := k1.trans k₂
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .t3) (by decide) ((k12.gpr (by decide)).trans h7)
    ((k12.gpr (by decide)).trans h5) 7) fun s₃ ⟨⟨b3, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (WP.keep [.s0] (Q := fun t =>
    t.mem = s₃.mem.writeW (off B (slot w 7)) (BitVec.ofNat 64 1)) ?_ (by rfl) (by rfl))
    fun t ⟨tm, k4⟩ => ⟨⟨?_, ?_⟩, ((k13.trans k4).mono (by decide))⟩
  · brun [pub_li1, b3, BitVec.add_zero, (hs.congr k13.2.2).st (d := slot w 7) (n := 8) (by omega_arith),
      (hs.congr k13.2.2).al8 (d := slot w 7) (by omega_arith) (al 7)]
  · rw [tm, m3]
    exact one_word _ _ _ hw1 (by omega_arith) hz
  · rw [tm, m3]
    rw [m1] at out₂
    exact out₂.trans ((writeW_outside s₂.mem B (d := slot w 7) _ (by omega_arith)).mono (by omega_arith)
      (by omega_arith))

/-! ## The leading zeros -/

/-- A step of `skip`: the top bit of `s7` shifted out, `s8` counted down,
and `t3` 0 if the bit was set, else `s8`. -/
theorem skipBody_ok {t : State} {n : Nat} (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (h8 : t.gpr .s8 = BitVec.ofNat 64 n) :
    WP isa (.block [.shift .srl .d .t3 .s7 63, .shift .sll .d .s7 .s7 1, .addi .s8 .s8 (-1),
        .addi .t3 .t3 (-1), .logic .and .t3 .t3 .s8]) t fun t' =>
      (t'.gpr .s7 = t.gpr .s7 <<< 1 ∧ t'.gpr .s8 = BitVec.ofNat 64 (n - 1) ∧
        t'.gpr .t3 = (if 2 ^ 63 ≤ (t.gpr .s7).toNat then 0 else BitVec.ofNat 64 (n - 1)) ∧ t'.mem = t.mem) ∧
      Keep [.t3, .s7, .s8] t t' := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [top_bit, h8]
  have e : BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  rw [e]
  refine ⟨rfl, ?_⟩
  split
  · simp
  · rw [show BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 by decide, BitVec.allOnes_and]

/-- `skip`: from `s7 = v 2³¹`, `s8 = 32 - i` after `i + 1` shifts, the last of
them out of `e`'s first set bit if `v` is not 0. -/
theorem skip_ok {s : State} {v : Nat} (h7 : (s.gpr .s7).toNat = v * 2 ^ 31) :
    WP isa skip s fun t =>
      (∃ i ≤ 32, t.gpr .s8 = BitVec.ofNat 64 (32 - i) ∧
        (0 < v → 2 ^ 64 + (t.gpr .s7).toNat = v * 2 ^ 31 * 2 ^ (i + 1)) ∧ t.mem = s.mem) ∧
      Keep [.t3, .s7, .s8] s t := by
  unfold skip
  refine WP.seq (WP.mono (WP.keep [.s8] (Q := fun t => t.gpr .s8 = BitVec.ofNat 64 33 ∧ t.mem = s.mem)
    (by brun [exec_li]) (by rfl) (by rfl)) fun s₁ ⟨⟨h8, m1⟩, k1⟩ => ?_)
  let Inv : Nat → State → Prop := fun n t => ∃ i, n = 33 - i ∧ i ≤ 32 ∧ t.gpr .s8 = BitVec.ofNat 64 (33 - i) ∧
    (t.gpr .s7).toNat = v * 2 ^ 31 * 2 ^ i ∧ t.mem = s.mem ∧ Keep [.t3, .s7, .s8] s t
  refine WP.loop Inv (fun n t ⟨i, hn, hi, t8, t7, tm, kt⟩ => ?_) 33 s₁
    ⟨0, rfl, by omega_arith, h8, by rw [k1.gpr (by decide), h7]; simp, m1, k1.mono (by decide)⟩
  refine WP.mono (skipBody_ok (n := 33 - i) (by omega_arith) (by omega_arith) t8) fun t' ⟨⟨a7, a8, a3, am⟩, k'⟩ => ?_
  have hsh := r24_shift (t.gpr .s7)
  rw [← a7] at hsh
  have hlt := (t'.gpr .s7).isLt
  have hlt' := (t.gpr .s7).isLt
  have kt' : Keep [.t3, .s7, .s8] s t' := (kt.trans k').mono (by decide)
  by_cases hb : 2 ^ 63 ≤ (t.gpr .s7).toNat
  · simp only [hb, ↓reduceIte] at a3 hsh
    refine .inl ⟨by rw [Steps.eval_nonzero, a3]; rfl, ⟨i, hi, by rw [a8]; congr 1; omega_arith, fun _ => ?_,
      am.trans tm⟩, kt'⟩
    rw [pow_step, ← t7]
    omega_arith
  · simp only [hb, ↓reduceIte, Nat.zero_mul, Nat.add_zero] at a3 hsh
    by_cases hz : i = 32
    · subst hz
      refine .inl ⟨by rw [Steps.eval_nonzero, a3]; rfl, ⟨32, by omega_arith, by rw [a8], fun hv0 => ?_,
        am.trans tm⟩, kt'⟩
      exfalso
      have : v * 2 ^ 31 * 2 ^ 32 < 2 ^ 63 := by rw [← t7]; omega_arith
      have : 2 ^ 63 ≤ v * 2 ^ 31 * 2 ^ 32 := by
        rw [show (2 : Nat) ^ 63 = 1 * 2 ^ 31 * 2 ^ 32 from rfl]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hv0)
      omega_arith
    · refine .inr ⟨?_, 33 - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, by rw [a8]; congr 1, ?_,
        am.trans tm, kt'⟩
      · rw [Steps.eval_nonzero, a3, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
        congr 1
        simp only [ne_eq, decide_eq_true_eq]
        omega_arith
      · rw [pow_step, ← t7]
        omega_arith

/-! ## The scan -/

/-- The mask of all ones and the bases of arrays 6, 6 and 5, for `initA`. -/
theorem initBlock_ok {t : State} {B : Addr} {w : Nat} (h7 : t.gpr .a7 = off B (slot w 0))
    (h5 : t.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block (([.li .s4 (-1)] : List Instr) ++ base .a5 6 ++ base .a6 6 ++ base .a2 5)) t fun t' =>
      (t'.gpr .s4 = BitVec.allOnes 64 ∧
        t'.gpr .a5 = off B (slot w 6) ∧ t'.gpr .a6 = off B (slot w 6) ∧ t'.gpr .a2 = off B (slot w 5) ∧
        t'.mem = t.mem) ∧
      Keep [.s4, .a5, .a6, .a2] t t' := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.s4] (Q := fun t₁ => t₁.gpr .s4 = BitVec.allOnes 64 ∧ t₁.mem = t.mem)
    (by brun [exec_li]; decide) (by rfl) (by rfl)) fun t₁ ⟨⟨a4, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .a5) (by decide) ((k1.gpr (by decide)).trans h7)
    ((k1.gpr (by decide)).trans h5) 6) fun t₂ ⟨⟨a5, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .a6) (by decide) ((k12.gpr (by decide)).trans h7)
    ((k12.gpr (by decide)).trans h5) 6) fun t₃ ⟨⟨a6, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (base_ok (rd := .a2) (by decide) ((k13.gpr (by decide)).trans h7)
    ((k13.gpr (by decide)).trans h5) 5) fun t₄ ⟨⟨a2, m4⟩, k4⟩ =>
      ⟨⟨?_, ?_, ?_, a2, ?_⟩, (k13.trans k4).mono (by decide)⟩
  · rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), a4]
  · rw [k4.gpr (by decide), k3.gpr (by decide), a5]
  · rw [k4.gpr (by decide), a6]
  · rw [m4, m3, m2, m1]

/-- The registers `initA` writes. -/
def initRegs : List Reg := [.s4, .a5, .a6, .a2, .a0, .t3, .t4, .t5, .s2, .s3]

/-- `initA`: array 6 into array 5. -/
theorem initA_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ctx s B Z w N) :
    WP isa initA s fun t =>
      (Ctx t B Z w N ∧ V t.mem B w 5 = V s.mem B w 6 ∧
        (∀ j < 8, j ≠ 5 → V t.mem B w j = V s.mem B w j) ∧ Arrays B w powJs s.mem t.mem) ∧
      Keep initRegs s t := by
  have hnw := h.scr.nowrap
  have al := slot_al w
  unfold initA
  refine WP.seq (WP.mono (initBlock_ok h.a7 h.s5) fun s₁ ⟨⟨a4, a5, a6, a2, m1⟩, k1⟩ => ?_)
  have s5 := h.sl (j := 5) (by decide)
  have s6 := h.sl (j := 6) (by decide)
  have d56 := slot_sep (w := w) (show (5 : Nat) ≠ 6 by decide)
  refine WP.mono (selectAcc64_ok (b := true) (w := w) (dA := slot w 6) (dT := slot w 6) (dO := slot w 5)
    (h.scr.congr k1.2.2) a5 a6 a2 ((k1.gpr (by decide)).trans h.t0) (by rw [a4]; rfl)
    (by have := h.w2; omega_arith) h.w31 (al 6) (al 6) (al 5) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith))
    fun t ⟨hv, out, k2⟩ => ?_
  rw [m1] at hv out
  have o : Arrays B w [5] s.mem t.mem :=
    Arrays.of_outside (j := 5) (by simp) out (Nat.le_refl _) (by omega_arith)
  have op : Arrays B w powJs s.mem t.mem := arrays_pow o (by decide)
  have k12 : Keep initRegs s t := (k1.trans k2).mono (by decide)
  simp only [ite_true] at hv
  exact ⟨⟨h.of k12 (by decide) op, hv,
    fun j hj hj5 => h.vj hj (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega_arith) o, op⟩, k12⟩

/-- The registers `bitStep` writes. -/
def bitRegs : List Reg := montRegs ++ [.t3, .s7]

/-- `bitStep`: `S R ≡ a² (mod n)`, `P R ≡ S (x R) (mod n)` and `a := P` if the
top bit of `s7` is set, else `S`. -/
theorem bitStep_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ctx s B Z w N) (hA : V s.mem B w 5 < N)
    (hX : V s.mem B w 6 < N) :
    WP isa bitStep s fun t =>
      (Ctx t B Z w N ∧ V t.mem B w 5 < N ∧
        (∃ S, S * 2 ^ (64 * w) % N = V s.mem B w 5 * V s.mem B w 5 % N ∧
          if 2 ^ 63 ≤ (s.gpr .s7).toNat then V t.mem B w 5 * 2 ^ (64 * w) % N = S * V s.mem B w 6 % N
          else V t.mem B w 5 = S) ∧
        (∀ j < 8, j ≠ 1 → j ≠ 2 → j ≠ 3 → j ≠ 5 → V t.mem B w j = V s.mem B w j) ∧
        Arrays B w powJs s.mem t.mem ∧ t.gpr .s7 = s.gpr .s7 <<< 1) ∧ Keep bitRegs s t := by
  unfold bitStep
  refine WP.seq (WP.mono (h.square hA) fun s₁ ⟨⟨c1, lt1, e1, v1, o1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.t3, .s7] (Q := fun t => t.gpr .t3 = s₁.gpr .s7 >>> 63 ∧
      t.gpr .s7 = s₁.gpr .s7 <<< 1 ∧ t.mem = s₁.mem) (by brun) (by rfl) (by rfl))
    fun s₂ ⟨⟨a3, a7, m2⟩, k2⟩ => ?_)
  have e7 : s₁.gpr .s7 = s.gpr .s7 := k1.gpr (by decide)
  rw [e7, top_bit] at a3
  rw [e7] at a7
  have k12 := k1.trans k2
  have c2 : Ctx s₂ B Z w N := c1.of k2 (by decide) (by rw [m2]; exact fun _ _ => rfl)
  have X1 : V s₁.mem B w 6 = V s.mem B w 6 := v1 6 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.ite (decide (2 ^ 63 ≤ (s.gpr .s7).toNat)) (by
    rw [Steps.eval_nonzero, a3, ne_zero_iff]; split <;> rename_i hb <;> simp [hb]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.mono (c2.mont (o := 5) (a := 5) (b := 6) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by rw [m2, X1]; exact hX))
      fun t ⟨⟨c3, lt3, e3, v3, o3⟩, k3⟩ => ⟨⟨c3, lt3, ⟨_, e1, by simp only [hb, ↓reduceIte]; rw [e3, m2, X1]⟩,
        fun j hj h1 h2 h3 h5 => by rw [v3 j hj h2 h3 h5, m2, v1 j hj h1 h2 h3 h5], ?_, ?_⟩,
        (k12.trans k3).mono (by decide)⟩
    · rw [m2] at o3; exact o1.trans o3
    · rw [k3.gpr (by decide), a7]
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil ⟨⟨c2, by rw [m2]; exact lt1, ⟨_, e1, by simp only [hb, ↓reduceIte]; rw [m2]⟩,
      fun j hj h1 h2 h3 h5 => by rw [m2, v1 j hj h1 h2 h3 h5], by rw [m2]; exact o1, a7⟩, k12.mono (by decide)⟩

/-- The registers the power writes. -/
def powRegs : List Reg := montRegs ++ [.t3, .s7, .s8, .s0, .t5]

/-- `lastBit`: `S R ≡ a² (mod n)`, then the result `y` in array 4 with
`y R ≡ x S (mod n)` if the top bit of `s7` is set, else `y R ≡ S`. -/
theorem lastBit_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ctx s B Z w N) (hA : V s.mem B w 5 < N)
    (h7 : V s.mem B w 7 = 1) :
    WP isa lastBit s fun t =>
      (∃ S, S * 2 ^ (64 * w) % N = V s.mem B w 5 * V s.mem B w 5 % N ∧
        V t.mem B w 4 * 2 ^ (64 * w) % N =
          (if 2 ^ 63 ≤ (s.gpr .s7).toNat then V s.mem B w 4 else 1) * S % N) ∧
        V t.mem B w 4 < N ∧ Arrays B w powJs s.mem t.mem ∧ Keep powRegs s t := by
  unfold lastBit
  refine WP.seq (WP.mono (h.square hA) fun s₁ ⟨⟨c1, lt1, e1, v1, o1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = s₁.gpr .s7 >>> 63 ∧ t.mem = s₁.mem)
    (by brun) (by rfl) (by rfl)) fun s₂ ⟨⟨a3, m2⟩, k2⟩ => ?_)
  have e7 : s₁.gpr .s7 = s.gpr .s7 := k1.gpr (by decide)
  rw [e7, top_bit] at a3
  have k12 := k1.trans k2
  have c2 : Ctx s₂ B Z w N := c1.of k2 (by decide) (by rw [m2]; exact fun _ _ => rfl)
  have X1 : V s₁.mem B w 4 = V s.mem B w 4 := v1 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have S1 : V s₁.mem B w 7 = 1 := by rw [v1 7 (by decide) (by decide) (by decide) (by decide) (by decide), h7]
  refine WP.ite (decide (2 ^ 63 ≤ (s.gpr .s7).toNat)) (by
    rw [Steps.eval_nonzero, a3, ne_zero_iff]; split <;> rename_i hb <;> simp [hb]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.mono (c2.mont (o := 4) (a := 4) (b := 5) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by rw [m2]; exact lt1))
      fun t ⟨⟨_, lt3, e3, _, o3⟩, k3⟩ => ⟨⟨_, e1, by rw [e3, m2, X1]; simp only [hb, ↓reduceIte]⟩, lt3,
        by rw [m2] at o3; exact o1.trans o3, (k12.trans k3).mono (by decide)⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (c2.mont (o := 4) (a := 7) (b := 5) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by rw [m2]; exact lt1))
      fun t ⟨⟨_, lt3, e3, _, o3⟩, k3⟩ => ⟨⟨_, e1, by rw [e3, m2, S1]; simp only [hb, ↓reduceIte]⟩, lt3,
        by rw [m2] at o3; exact o1.trans o3, (k12.trans k3).mono (by decide)⟩

/-! ## The power -/

theorem shl31_toNat (E : Nat) : (BitVec.ofNat 64 E <<< 31).toNat = E % 2 ^ 33 * 2 ^ 31 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega_arith

/-- `power`: `x^(E mod 2^33) mod n` into array 4, for the input `x` in array 4,
`E 2^31` in `s7` and something below `n` in array 1: if it is `R² mod n`
and `E mod 2^33` is not 0. -/
theorem power_ok {s : State} {B : Addr} {Z w E : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hN : 2 ≤ wordsVal s.mem B (slot w 0) w) (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1)
    (hRRlt : wordsVal s.mem B (slot w 1) w < wordsVal s.mem B (slot w 0) w)
    (hs7 : s.gpr .s7 = BitVec.ofNat 64 E <<< 31) :
    WP isa power s fun t =>
      ((0 < E % 2 ^ 33 →
          wordsVal s.mem B (slot w 1) w = 2 ^ (64 * w) * 2 ^ (64 * w) % wordsVal s.mem B (slot w 0) w →
          wordsVal t.mem B (slot w 4) w =
            wordsVal s.mem B (slot w 4) w ^ (E % 2 ^ 33) % wordsVal s.mem B (slot w 0) w) ∧
        Arrays B w powJs s.mem t.mem) ∧ Keep powRegs s t := by
  have hnw := hs.nowrap
  have h0 : Ctx s B Z w (wordsVal s.mem B (slot w 0) w) := ⟨hs, hw2, hw', hZ, h7, h5, ht0, hinv, rfl⟩
  generalize hNd : wordsVal s.mem B (slot w 0) w = N at hN hodd hRRlt h0 ⊢
  generalize hR : 2 ^ (64 * w) = R
  have hcop : Nat.Coprime R N := by rw [← hR]; exact VG.Proof.Bignum.coprime_pow2 hodd _
  have hN0 : 0 < N := by omega_arith
  generalize hXd : wordsVal s.mem B (slot w 4) w = X
  generalize hRRd : wordsVal s.mem B (slot w 1) w = RRv at hRRlt ⊢
  generalize hv : E % 2 ^ 33 = v
  have h7' : (s.gpr .s7).toNat = v * 2 ^ 31 := by rw [hs7, shl31_toNat, hv]
  unfold power
  -- 1 in array 7.
  refine WP.seq (WP.mono (oneP_ok hs (by omega_arith) hw' hZ h7 h5 ht0) fun s₁ ⟨⟨h17, out1⟩, k1⟩ => ?_)
  have o1 : Arrays B w [7] s.mem s₁.mem :=
    Arrays.of_outside (j := 7) (by simp) out1 (Nat.le_refl _) (by omega_arith)
  have c1 := h0.of k1 (by decide) (arrays_pow o1 (by decide))
  have R1 : V s₁.mem B w 1 = RRv := (h0.vj (by decide) (by decide) o1).trans hRRd
  have X1 : V s₁.mem B w 4 = X := (h0.vj (by decide) (by decide) o1).trans hXd
  -- `x R mod n` into array 6.
  refine WP.seq (WP.mono (c1.mont (o := 6) (a := 4) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [R1]; exact hRRlt))
    fun s₂ ⟨⟨c2, lt2, e2, v2, o2⟩, k2⟩ => ?_)
  rw [X1, R1, hR] at e2
  have XM : RRv = R * R % N → V s₂.mem B w 6 % N = X * R % N := fun hE => by
    refine VG.Proof.Bignum.mont_cancel hcop ?_
    rw [e2, hE, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have X2 : V s₂.mem B w 4 = X := (v2 4 (by decide) (by decide) (by decide) (by decide)).trans X1
  have S2 : V s₂.mem B w 7 = 1 := (v2 7 (by decide) (by decide) (by decide) (by decide)).trans h17
  have O2 : Arrays B w powJs s.mem s₂.mem := (arrays_pow o1 (by decide)).trans o2
  have k12 := k1.trans k2
  generalize hXMd : V s₂.mem B w 6 = XMv at lt2 XM
  -- The leading zeros.
  refine WP.seq (WP.mono (skip_ok (s := s₂) (v := v)
    (by rw [k2.gpr (by decide), k1.gpr (by decide)]; exact h7'))
    fun s₃ ⟨⟨i, hi, h8, hfound, m3⟩, k3⟩ => ?_)
  have c3 := c2.of k3 (by decide) (by rw [m3]; exact fun _ _ => rfl)
  -- `a := x R mod n`.
  refine WP.seq (WP.mono (initA_ok c3) fun s₄ ⟨⟨c4, a4, v4, o4⟩, k4⟩ => ?_)
  rw [m3] at a4 v4 o4
  have k14 := (k12.trans k3).trans k4
  -- What holds after `q` shifts of `s7`.
  let Inv : Nat → State → Prop := fun q t =>
    Ctx t B Z w N ∧ Arrays B w powJs s.mem t.mem ∧ V t.mem B w 6 = XMv ∧ V t.mem B w 7 = 1 ∧
      V t.mem B w 4 = X ∧ V t.mem B w 5 < N ∧ Keep powRegs s t ∧
      (0 < v → RRv = R * R % N →
        ∃ c, c * 2 ^ 64 + (t.gpr .s7).toNat = v * 2 ^ 31 * 2 ^ q ∧ V t.mem B w 5 % N = X ^ c * R % N)
  have I4 : Inv (i + 1) s₄ := ⟨c4, O2.trans o4, by rw [v4 6 (by decide) (by decide)]; exact hXMd,
    by rw [v4 7 (by decide) (by decide), S2], by rw [v4 4 (by decide) (by decide), X2],
    by rw [a4, hXMd]; exact lt2, k14.mono (by decide), fun hv0 hE => ⟨1, by
      rw [k4.gpr (by decide), Nat.one_mul]; exact hfound hv0, by rw [a4, hXMd, Nat.pow_one]; exact XM hE⟩⟩
  have h8' : s₄.gpr .s8 = BitVec.ofNat 64 (32 - i) := (k4.gpr (by decide)).trans h8
  -- The rest of the bits.
  have last : ∀ t, Inv 32 t → WP isa lastBit t fun u =>
      ((0 < v → RRv = R * R % N → V u.mem B w 4 = X ^ v % N) ∧ Arrays B w powJs s.mem u.mem) ∧
        Keep powRegs s u := by
    intro t ⟨ct, ot, _, t7, t4, tA, kt, hc⟩
    refine WP.mono (lastBit_ok ct tA t7) fun u ⟨⟨S, eS, eY⟩, uY, ou, ku⟩ =>
      ⟨⟨fun hv0 hE => ?_, ot.trans ou⟩, (kt.trans ku).mono (by decide)⟩
    obtain ⟨c, hc, hcA⟩ := hc hv0 hE
    rw [t4, hR] at eY
    rw [hR] at eS
    have hY := last_step hcop hcA eS (decide (2 ^ 63 ≤ (t.gpr .s7).toNat)) (by
      rw [eY]; simp only [decide_eq_true_eq])
    have hlt := (t.gpr .s7).isLt
    have hb : 2 * c + (if decide (2 ^ 63 ≤ (t.gpr .s7).toNat) then 1 else 0) = v := by
      simp only [decide_eq_true_eq]
      rw [show v * 2 ^ 31 * 2 ^ 32 = v * 2 ^ 63 by rw [Nat.mul_assoc]] at hc
      split <;> omega_arith
    rw [hb] at hY
    rw [← hY, Nat.mod_eq_of_lt uY]
  unfold bits
  refine WP.ite (decide (32 - i ≠ 0)) (by rw [Steps.eval_nonzero, h8', ne_zero_iff, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_arith)]) (fun hp => ?_) (fun hp => ?_)
  · simp only [ne_eq, decide_eq_true_eq] at hp
    refine WP.seq (WP.mono (dec_ok s₄ .s8) fun s₅ e5 => ?_)
    subst e5
    have h8'' : (s₄.write .s8 (s₄.gpr .s8 - BitVec.ofNat 64 1)).gpr .s8 = BitVec.ofNat 64 (31 - i) := by
      gsimp
      rw [h8']
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith
    have I5 : Inv (i + 1) (s₄.write .s8 (s₄.gpr .s8 - BitVec.ofNat 64 1)) := by
      obtain ⟨ct, ot, t6, t7, t4, tA, kt, hc⟩ := I4
      exact ⟨ct.of (Keep.write _ _ _) (by decide) (by rw [mem_write]; exact fun _ _ => rfl),
        by rw [mem_write]; exact ot,
        by rw [mem_write]; exact t6, by rw [mem_write]; exact t7, by rw [mem_write]; exact t4,
        by rw [mem_write]; exact tA, (kt.trans (Keep.write _ _ _)).mono (by decide),
        by gsimp; exact hc⟩
    refine WP.seq (WP.mono (?_ : WP isa _ _ (Inv 32)) fun t ht => last t ht)
    refine WP.ite (decide (31 - i ≠ 0)) (by rw [Steps.eval_nonzero, h8'', ne_zero_iff, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_arith)]) (fun hq => ?_) (fun hq => ?_)
    · simp only [ne_eq, decide_eq_true_eq] at hq
      refine WP.mono (wp_countdown (cnt := .s8) (N := 31 - i) (by omega_arith) (by omega_arith)
        (fun j t => Inv (i + 1 + j) t)
        (fun j _ t ⟨ct, ot, t6, t7, t4, tA, kt, hc⟩ _ => ?_) I5 h8'') fun t ht => by
          rwa [show i + 1 + (31 - i) = 32 by omega_arith] at ht
      refine WP.seq (WP.mono (bitStep_ok ct tA (by rw [t6]; exact lt2))
        fun t₁ ⟨⟨c1', lt1', ⟨S, eS, eA⟩, v1', o1', a7⟩, k1'⟩ => ?_)
      refine WP.mono (dec_ok t₁ .s8) fun t₂ e => ?_
      subst e
      refine ⟨⟨c1'.of (Keep.write _ _ _) (by decide) (by rw [mem_write]; exact fun _ _ => rfl),
        by rw [mem_write]; exact ot.trans o1',
        by rw [mem_write, v1' 6 (by decide) (by decide) (by decide) (by decide) (by decide), t6],
        by rw [mem_write, v1' 7 (by decide) (by decide) (by decide) (by decide) (by decide), t7],
        by rw [mem_write, v1' 4 (by decide) (by decide) (by decide) (by decide) (by decide), t4],
        by rw [mem_write]; exact lt1', ((kt.trans k1').trans (Keep.write _ _ _)).mono (by decide),
        fun hv0 hE => ?_⟩,
        by gsimp; rw [k1'.gpr (by decide)]⟩
      obtain ⟨c, hc, hcA⟩ := hc hv0 hE
      rw [hR] at eS eA
      rw [t6] at eA
      have hsh := r24_shift (t.gpr .s7)
      rw [← a7] at hsh
      obtain ⟨hc', hA'⟩ := bit_step (b := decide (2 ^ 63 ≤ (t.gpr .s7).toNat)) hcop hcA (XM hE)
        eS (by simp only [decide_eq_true_eq]; exact eA) hc (by simp only [decide_eq_true_eq]; exact hsh)
      refine ⟨_, ?_, by rw [mem_write]; exact hA'⟩
      gsimp
      rw [show i + 1 + (j + 1) = i + 1 + j + 1 by omega_arith]
      exact hc'
    · simp only [ne_eq, decide_eq_false_iff_not, Decidable.not_not] at hq
      refine WP.block_nil ?_
      rw [show (32 : Nat) = i + 1 by omega_arith]
      exact I5
  · simp only [ne_eq, decide_eq_false_iff_not, Decidable.not_not] at hp
    -- `e = 1`: out of Montgomery form.
    obtain ⟨ct, ot, _, t7, _, tA, kt, _⟩ := I4
    refine WP.mono (ct.mont (o := 4) (a := 7) (b := 5) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) tA) fun u ⟨⟨_, uY, eY, _, ou⟩, ku⟩ =>
      ⟨⟨fun hv0 hE => ?_, ot.trans ou⟩, (kt.trans ku).mono (by decide)⟩
    have hf := hfound hv0
    have hlt := (s₃.gpr .s7).isLt
    have hv1 : v = 1 := by
      rw [show i = 32 by omega_arith, show v * 2 ^ 31 * 2 ^ (32 + 1) = v * 2 ^ 64 by rw [Nat.mul_assoc]] at hf
      omega_arith
    subst hv1
    rw [t7, Nat.one_mul, hR, a4, hXMd] at eY
    refine (Nat.mod_eq_of_lt uY).symm.trans ?_
    exact VG.Proof.Bignum.mont_cancel hcop (by rw [eY, XM hE, Nat.pow_one])

end VG.Proof.Bignum.RISCV64.Pub
