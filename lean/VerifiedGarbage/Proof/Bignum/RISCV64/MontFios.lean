module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Montgomery multiplication on RISC-V: the steps of a round

`fiosStep_ok`: a word of a round, `tⱼ + aᵢ bⱼ + u mⱼ` plus the two carries,
its low word stored and the carries replaced. A carry out of an addition is
`sltu` of the sum and an operand (`carry_toNat`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum.RISCV64

/-- The carry out of `x + y`, as `sltu` of the sum and `y` computes it. -/
theorem carry_toNat (x y : BitVec 64) :
    (if x + y < y then (1 : BitVec 64) else 0).toNat = (decide (2 ^ 64 ≤ x.toNat + y.toNat)).toNat := by
  have hx := x.isLt
  have hy := y.isLt
  by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat
  · have : x + y < y := by
      rw [BitVec.lt_def, BitVec.toNat_add]; omega
    simp [this, h]
  · have : ¬ x + y < y := by
      rw [BitVec.lt_def, BitVec.toNat_add]; omega
    simp only [this, h, ite_false, decide_false, Bool.toNat_false]; rfl

/-- The carry out of `y + x`, as `sltu` of the sum and `y` computes it. -/
theorem carry_toNat' (x y : BitVec 64) :
    (if y + x < y then (1 : BitVec 64) else 0).toNat = (decide (2 ^ 64 ≤ x.toNat + y.toNat)).toNat := by
  rw [BitVec.add_comm, carry_toNat]

/-- The arithmetic of one of a step's two sums: with `c₁ = c + x` and its
carry `k₁`, and `l = p q + c₁` and its carry `k₂`, the low word `l` and
`2⁶⁴` times the high word of `p q` plus both carries make `x + p q + c`,
below `2¹²⁸`. -/
theorem fios_chain (x p q c : BitVec 64) :
    (p * q + (c + x)).toNat +
      2 ^ 64 * (BitVec.ofNat 64 (p.toNat * q.toNat / 2 ^ 64) + (if c + x < x then 1 else 0) +
        (if p * q + (c + x) < c + x then 1 else 0)).toNat =
      x.toNat + p.toNat * q.toNat + c.toNat := by
  have hx := x.isLt
  have hp := p.isLt
  have hq := q.isLt
  have hc := c.isLt
  have hP : p.toNat * q.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  simp only [BitVec.toNat_add (_ + _), BitVec.toNat_add (BitVec.ofNat 64 _), carry_toNat]
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  by_cases h1 : 2 ^ 64 ≤ c.toNat + x.toNat <;>
    by_cases h2 : 2 ^ 64 ≤ p.toNat * q.toNat % 2 ^ 64 + (c.toNat + x.toNat) % 2 ^ 64 <;>
    simp only [h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

theorem fiosStep_writes (k : Nat) : writesOnly [.s0, .s1, .s2, .s3, .s4] (.block (fiosStep k)) = true := by
  rfl

theorem fiosStep_ok {s : State} {B : Addr} {Z dT dB dM k : Nat} (hs : Scr s B Z)
    (h3 : s.gpr .t3 = off B dT) (h4 : s.gpr .t4 = off B dB) (h0 : s.gpr .a0 = off B dM)
    (hk : k + 8 < 2048) (hk8 : k % 8 = 0) (hT8 : dT % 8 = 0) (hB8 : dB % 8 = 0) (hM8 : dM % 8 = 0)
    (hT : dT + k + 16 ≤ Z) (hB : dB + k + 16 ≤ Z) (hM : dM + k + 16 ≤ Z) :
    WP isa (.block (fiosStep k)) s fun s' =>
      (∃ v : BitVec 64, s'.mem = s.mem.writeW (off B (dT + k)) v ∧
        v.toNat + 2 ^ 64 * ((s'.gpr .s0).toNat + (s'.gpr .s1).toNat) =
          (word s.mem B (dT + (k + 8))).toNat + (s.gpr .t6).toNat * (word s.mem B (dB + (k + 8))).toNat +
            (s.gpr .t2).toNat * (word s.mem B (dM + (k + 8))).toNat +
            ((s.gpr .s0).toNat + (s.gpr .s1).toNat)) ∧ Keep [.s0, .s1, .s2, .s3, .s4] s s' := by
  have hk1 : k < 2048 := by omega_arith
  refine WP.keep _ ?_ (fiosStep_writes k) (by rfl)
  unfold fiosStep
  brun [h3, h4, h0, hk, hk1, hs.ld (show dT + (k + 8) + 8 ≤ Z by omega_arith),
    hs.ld (show dB + (k + 8) + 8 ≤ Z by omega_arith), hs.ld (show dM + (k + 8) + 8 ≤ Z by omega_arith),
    hs.st (show dT + k + 8 ≤ Z by omega_arith),
    hs.al8 (show dT + (k + 8) + 8 ≤ Z by omega_arith) (by omega_arith),
    hs.al8 (show dB + (k + 8) + 8 ≤ Z by omega_arith) (by omega_arith),
    hs.al8 (show dM + (k + 8) + 8 ≤ Z by omega_arith) (by omega_arith),
    hs.al8 (show dT + k + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine ⟨_, rfl, ?_⟩
  have h1 := fios_chain (word s.mem B (dT + (k + 8))) (s.gpr .t6) (word s.mem B (dB + (k + 8))) (s.gpr .s0)
  have h2 := fios_chain (s.gpr .t6 * word s.mem B (dB + (k + 8)) + (s.gpr .s0 + word s.mem B (dT + (k + 8))))
    (s.gpr .t2) (word s.mem B (dM + (k + 8))) (s.gpr .s1)
  simp only [Nat.reducePow, word] at h1 h2 ⊢
  omega_arith


/-! ## The words of a round -/

/-- A store of word `j` of a number of `j + 1` words. -/
theorem fios_wordsVal_write_top (m : Mem) (B : Addr) (d j : Nat) (v : BitVec 64) (h : d + 8 * j + 8 ≤ 2 ^ 64) :
    wordsVal (m.writeW (off B (d + 8 * j)) v) B d (j + 1) = wordsVal m B d j + 2 ^ (64 * j) * v.toNat := by
  rw [wordsVal_succ_top, (writeW_outside m B v h).wordsVal (by omega_arith) (by omega_arith), word_writeW_self]

theorem fios_wordsVal_append (m : Mem) (B : Addr) (d j k : Nat) :
    wordsVal m B d (j + k) = wordsVal m B d j + 2 ^ (64 * j) * wordsVal m B (d + 8 * j) k := by
  induction j generalizing d with
  | zero => simp only [wordsVal, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero]
  | succ j ih =>
    rw [Nat.add_right_comm, wordsVal, ih, wordsVal, pow64_succ, show d + 8 + 8 * j = d + 8 * (j + 1) by omega_arith,
      Nat.mul_add, Nat.mul_assoc]
    omega_arith

theorem fiosSteps_succ (K : Nat) :
    (List.range (K + 1)).flatMap (fun k => fiosStep (8 * k)) =
      (List.range K).flatMap (fun k => fiosStep (8 * k)) ++ fiosStep (8 * K) := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The registers the steps write. -/
def fiosRegs : List Reg := [.s0, .s1, .s2, .s3, .s4]

/-- The sum of `K` steps from `T`, `S`, `M` and the carries `c + d`, as the
sum of the first `K` steps and the last. -/
theorem fios_sum_succ {W T S M W' C₀ C₁ C₂ a u v t b m P : Nat}
    (e₁ : W + P * C₁ = T + a * S + u * M + C₀) (e₂ : v + 2 ^ 64 * C₂ = t + a * b + u * m + C₁)
    (hW : W' = W + P * v) :
    W' + P * 2 ^ 64 * C₂ = T + P * t + a * (S + P * b) + u * (M + P * m) + C₀ := by
  subst hW
  have e : P * v + P * 2 ^ 64 * C₂ = P * (t + a * b + u * m + C₁) := by
    rw [← e₂, Nat.mul_add, Nat.mul_assoc]
  grind

/-- `K` steps (`8 K + 8` bytes into the arrays at most `2¹¹`), the pointers
`t3`, `t4`, `a0` at offsets `dT`, `dB`, `dM`: the `K` words stored from `dT`
on and the carries `s0 + s1` make up `T + aᵢ S + u M` plus the carries on
entry, for the `K` words `T`, `S`, `M` from `dT + 8`, `dB + 8`, `dM + 8` on,
`aᵢ` in `t6` and `u` in `t2`. -/
theorem fiosSteps_ok {B : Addr} {Z dT dB dM : Nat} (hT8 : dT % 8 = 0) (hB8 : dB % 8 = 0) (hM8 : dM % 8 = 0) :
    ∀ (K : Nat) {s : State}, Scr s B Z →
    s.gpr .t3 = off B dT → s.gpr .t4 = off B dB → s.gpr .a0 = off B dM → 8 * K < 2048 →
    dT + 8 * K + 8 ≤ Z → dB + 8 * K + 8 ≤ Z → dM + 8 * K + 8 ≤ Z →
    (dB + 8 * K + 8 ≤ dT ∨ dT + 8 * K ≤ dB + 8) → (dM + 8 * K + 8 ≤ dT ∨ dT + 8 * K ≤ dM + 8) →
    WP isa (.block ((List.range K).flatMap fun k => fiosStep (8 * k))) s fun s' =>
      (Outside B dT (8 * K) s.mem s'.mem ∧
        wordsVal s'.mem B dT K + 2 ^ (64 * K) * ((s'.gpr .s0).toNat + (s'.gpr .s1).toNat) =
          wordsVal s.mem B (dT + 8) K + (s.gpr .t6).toNat * wordsVal s.mem B (dB + 8) K +
            (s.gpr .t2).toNat * wordsVal s.mem B (dM + 8) K + ((s.gpr .s0).toNat + (s.gpr .s1).toNat)) ∧
      Keep fiosRegs s s'
  | 0, s, _, _, _, _, _, _, _, _, _, _ => by
    simp only [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨⟨Outside.refl _ _ _ _, by simp [wordsVal]⟩, Keep.refl _ _⟩
  | K + 1, s, hs, h3, h4, h0, hK, hT, hB, hM, sB, sM => by
    have hnw := hs.nowrap
    rw [fiosSteps_succ, WP.block_append_iff]
    refine WP.mono (fiosSteps_ok hT8 hB8 hM8 K hs h3 h4 h0 (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith)) fun s₁ ⟨⟨o₁, e₁⟩, k₁⟩ => ?_
    have g : ∀ r ∈ [Reg.t2, .a0, .t3, .t4, .t6], s₁.gpr r = s.gpr r := fun r hr =>
      k₁.gpr (by revert r hr; decide)
    refine WP.mono (fiosStep_ok (dT := dT) (dB := dB) (dM := dM) (k := 8 * K) (hs.congr k₁.2.2)
      (by rw [g .t3 (by decide), h3]) (by rw [g .t4 (by decide), h4]) (by rw [g .a0 (by decide), h0])
      (by omega_arith) (by omega_arith) hT8 hB8 hM8 (by omega_arith) (by omega_arith) (by omega_arith))
      fun s₂ ⟨⟨v, m₂, e₂⟩, k₂⟩ => ⟨⟨?_, ?_⟩, (k₁.trans k₂).mono (by decide)⟩
    · rw [m₂]
      exact (o₁.mono (Nat.le_refl _) (by omega_arith)).trans
        ((writeW_outside _ B v (by omega_arith)).mono (by omega_arith) (by omega_arith))
    · -- The words read are those on entry.
      rw [show dT + (8 * K + 8) = dT + 8 + 8 * K by omega_arith, show dB + (8 * K + 8) = dB + 8 + 8 * K by omega_arith,
        show dM + (8 * K + 8) = dM + 8 + 8 * K by omega_arith, o₁.word (by omega_arith) (by omega_arith),
        o₁.word (by omega_arith) (by omega_arith), o₁.word (by omega_arith) (by omega_arith), g .t2 (by decide),
        g .t6 (by decide)] at e₂
      rw [m₂, fios_wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B (dT + 8) K,
        wordsVal_succ_top s.mem B (dB + 8) K, wordsVal_succ_top s.mem B (dM + 8) K, Nat.mul_succ, Nat.pow_add]
      exact fios_sum_succ e₁ e₂ rfl

/-- The sum of a loop's iterations, as the sum of the first ones and the last. -/
theorem fios_sum_group {W T S M W' C₀ C₁ C₂ a u G T' S' M' P Q : Nat}
    (e₁ : W + P * C₁ = T + a * S + u * M + C₀) (e₂ : G + Q * C₂ = T' + a * S' + u * M' + C₁)
    (hW : W' = W + P * G) :
    W' + P * Q * C₂ = T + P * T' + a * (S + P * S') + u * (M + P * M') + C₀ := by
  subst hW
  have e : P * G + P * Q * C₂ = P * (T' + a * S' + u * M' + C₁) := by
    rw [← e₂, Nat.mul_add, Nat.mul_assoc]
  grind

/-- The registers a loop of steps writes. -/
def fiosLoopRegs : List Reg := [.a0, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4]

/-- What `N` iterations of `U` steps leave, the pointers at offsets `dT`,
`dB`, `dM` on entry: `fiosSteps_ok` for `U N` words, the pointers advanced
past them. -/
def FiosPost (B : Addr) (dT dB dM K : Nat) (s₀ s : State) : Prop :=
  s.gpr .t3 = off B (dT + 8 * K) ∧ s.gpr .t4 = off B (dB + 8 * K) ∧ s.gpr .a0 = off B (dM + 8 * K) ∧
    Outside B dT (8 * K) s₀.mem s.mem ∧
    wordsVal s.mem B dT K + 2 ^ (64 * K) * ((s.gpr .s0).toNat + (s.gpr .s1).toNat) =
      wordsVal s₀.mem B (dT + 8) K + (s₀.gpr .t6).toNat * wordsVal s₀.mem B (dB + 8) K +
        (s₀.gpr .t2).toNat * wordsVal s₀.mem B (dM + 8) K + ((s₀.gpr .s0).toNat + (s₀.gpr .s1).toNat) ∧
    Keep fiosLoopRegs s₀ s

/-- `N > 0` iterations of `U` steps (`countLoop .t5 (fiosGroup U)`). -/
theorem fiosLoop_ok {B : Addr} {Z dT dB dM U N : Nat} (hU : 8 * U < 2048) {s₀ : State} (hs : Scr s₀ B Z)
    (hT8 : dT % 8 = 0) (hB8 : dB % 8 = 0) (hM8 : dM % 8 = 0)
    (h3 : s₀.gpr .t3 = off B dT) (h4 : s₀.gpr .t4 = off B dB) (h0 : s₀.gpr .a0 = off B dM)
    (h5 : s₀.gpr .t5 = BitVec.ofNat 64 N) (hN : 1 ≤ N) (hN' : N < 2 ^ 32)
    (hT : dT + 8 * (U * N) + 8 ≤ Z) (hB : dB + 8 * (U * N) + 8 ≤ Z) (hM : dM + 8 * (U * N) + 8 ≤ Z)
    (sB : dB + 8 * (U * N) + 8 ≤ dT ∨ dT + 8 * (U * N) ≤ dB + 8)
    (sM : dM + 8 * (U * N) + 8 ≤ dT ∨ dT + 8 * (U * N) ≤ dM + 8) :
    WP isa (countLoop .t5 (fiosGroup U)) s₀ (FiosPost B dT dB dM (U * N) s₀) := by
  have hnw := hs.nowrap
  refine wp_countdown (body := .block (fiosGroup U ++ ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5)
    (N := N) (by omega_arith) (by omega_arith) (fun i s => FiosPost B dT dB dM (U * i) s₀ s) (fun i hi s hI hc => ?_)
    ⟨by rw [h3]; rfl, by rw [h4]; rfl, by rw [h0]; rfl, Outside.refl _ _ _ _, by simp [wordsVal],
      Keep.refl _ _⟩ h5
  obtain ⟨i3, i4, i0, iout, ieq, ik⟩ := hI
  have hUi : U * i + U ≤ U * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have g : ∀ r ∈ [Reg.t2, .t6], s.gpr r = s₀.gpr r := fun r hr => ik.gpr (by revert r hr; decide)
  rw [fiosGroup, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fiosSteps_ok (show (dT + 8 * (U * i)) % 8 = 0 by omega_arith)
    (show (dB + 8 * (U * i)) % 8 = 0 by omega_arith) (show (dM + 8 * (U * i)) % 8 = 0 by omega_arith)
    U (hs.congr ik.2.2) i3 i4 i0 hU (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₁ ⟨⟨o₁, e₁⟩, k₁⟩ => ?_
  have g₁ : ∀ r ∈ [Reg.a0, .t3, .t4, .t5], s₁.gpr r = s.gpr r := fun r hr =>
    k₁.gpr (by revert r hr; decide)
  have hst : WP isa (.block [.addi .t3 .t3 ((8 * U : Nat) : Int), .addi .t4 .t4 ((8 * U : Nat) : Int),
      .addi .a0 .a0 ((8 * U : Nat) : Int), .addi .t5 .t5 (-1)]) s₁ fun s₂ =>
      s₂ = (((s₁.write .t3 (off B (dT + 8 * (U * i) + 8 * U))).write .t4 (off B (dB + 8 * (U * i) + 8 * U))).write
        .a0 (off B (dM + 8 * (U * i) + 8 * U))).write .t5 (s₁.gpr .t5 - BitVec.ofNat 64 1) := by
    brun [g₁ .t3 (by decide), g₁ .t4 (by decide), g₁ .a0 (by decide), i3, i4, i0, hU]
  refine WP.mono hst fun s₂ e => ?_
  subst e
  have pU : U * (i + 1) = U * i + U := Nat.mul_succ _ _
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by gsimp; rw [g₁ .t5 (by decide)]⟩
  · gsimp; rw [pU, Nat.mul_add, Nat.add_assoc]
  · gsimp; rw [pU, Nat.mul_add, Nat.add_assoc]
  · gsimp; rw [pU, Nat.mul_add, Nat.add_assoc]
  · gsimp
    exact (iout.mono (Nat.le_refl _) (by omega_arith)).trans (o₁.mono (by omega_arith) (by omega_arith))
  · gsimp
    -- The words read are those on entry.
    have rd : ∀ d, (d + 8 * (U * N) + 8 ≤ dT ∨ dT + 8 * (U * N) ≤ d + 8) → d + 8 * (U * N) + 8 ≤ Z →
        wordsVal s.mem B (d + 8 * (U * i) + 8) U = wordsVal s₀.mem B (d + 8 + 8 * (U * i)) U := by
      intro d hd hdZ
      rw [show d + 8 * (U * i) + 8 = d + 8 + 8 * (U * i) by omega_arith]
      exact iout.wordsVal (by omega_arith) (by omega_arith)
    rw [rd dB sB hB, rd dM sM hM, g .t2 (by decide), g .t6 (by decide)] at e₁
    rw [show dT + 8 * (U * i) + 8 = dT + 8 + 8 * (U * i) by omega_arith,
      iout.wordsVal (o := dT) (n := 8 * (U * i)) (by omega_arith) (by omega_arith)] at e₁
    rw [pU, fios_wordsVal_append s₁.mem B dT (U * i) U, fios_wordsVal_append s₀.mem B (dT + 8) (U * i) U,
      fios_wordsVal_append s₀.mem B (dB + 8) (U * i) U, fios_wordsVal_append s₀.mem B (dM + 8) (U * i) U,
      show 64 * (U * i + U) = 64 * (U * i) + 64 * U by omega_arith, Nat.pow_add,
      (o₁.wordsVal (o := dT + 8 * (U * i)) (n := 8 * U) (d := dT) (k := U * i) (by omega_arith) (by omega_arith))]
    exact fios_sum_group ieq e₁ rfl
  · exact Keep.trans' ik (Keep.trans' (k₁.mono (by decide)) (Keep.mono (by
      exact (((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _))
      (by decide)))

/-- `N` iterations of `U` steps if `N ≠ 0` (`countLoop? (fiosGroup U)`). -/
theorem fiosLoop?_ok {B : Addr} {Z dT dB dM U N : Nat} (hU : 8 * U < 2048) {s₀ : State} (hs : Scr s₀ B Z)
    (hT8 : dT % 8 = 0) (hB8 : dB % 8 = 0) (hM8 : dM % 8 = 0)
    (h3 : s₀.gpr .t3 = off B dT) (h4 : s₀.gpr .t4 = off B dB) (h0 : s₀.gpr .a0 = off B dM)
    (h5 : s₀.gpr .t5 = BitVec.ofNat 64 N) (hN' : N < 2 ^ 32)
    (hT : dT + 8 * (U * N) + 8 ≤ Z) (hB : dB + 8 * (U * N) + 8 ≤ Z) (hM : dM + 8 * (U * N) + 8 ≤ Z)
    (sB : dB + 8 * (U * N) + 8 ≤ dT ∨ dT + 8 * (U * N) ≤ dB + 8)
    (sM : dM + 8 * (U * N) + 8 ≤ dT ∨ dT + 8 * (U * N) ≤ dM + 8) :
    WP isa (countLoop? (fiosGroup U)) s₀ (FiosPost B dT dB dM (U * N) s₀) := by
  refine WP.ite _ (Steps.eval_zero_ofNat _ _ (by omega_arith) h5) (fun hz => ?_) (fun hz => ?_)
  · have hN : N = 0 := of_decide_eq_true hz
    subst hN
    exact WP.block_nil ⟨by rw [h3]; rfl, by rw [h4]; rfl, by rw [h0]; rfl, Outside.refl _ _ _ _,
      by simp [wordsVal], Keep.refl _ _⟩
  · exact fiosLoop_ok hU hs hT8 hB8 hM8 h3 h4 h0 h5 (Nat.pos_of_ne_zero (of_decide_eq_false hz)) hN' hT hB hM sB sM

/-! ## The start and the end of a round -/

theorem ofNat_sub_one {n : Nat} (hn : 1 ≤ n) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

theorem fios_rem (n : Nat) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& BitVec.ofNat 64 3 = BitVec.ofNat 64 (n % 4) := by
  apply BitVec.eq_of_toNat_eq
  have a := Nat.and_two_pow_sub_one_eq_mod n 2
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub, Nat.reduceMod] at a ⊢
  rw [Nat.mod_eq_of_lt h, a]
  omega_arith

theorem fios_quot (n : Nat) (h : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 2 = BitVec.ofNat 64 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

/-- The arithmetic of word 0's product: `t + a b` is the low word of `t +
(a b mod 2⁶⁴)` and `2⁶⁴` times the high word of `a b` plus the carry. -/
theorem fios_head_arith (t a b : BitVec 64) :
    (t + a * b).toNat +
      2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64) + (if t + a * b < a * b then 1 else 0)).toNat =
      t.toNat + a.toNat * b.toNat := by
  have ht := t.isLt
  have ha := a.isLt
  have hb := b.isLt
  have hP : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  simp only [BitVec.toNat_add (BitVec.ofNat 64 _), carry_toNat]
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  by_cases h1 : 2 ^ 64 ≤ t.toNat + a.toNat * b.toNat % 2 ^ 64 <;>
    simp only [h1, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- The arithmetic of word 0's reduction: `u m₀ + s₀`, a multiple of `2⁶⁴`, is
`2⁶⁴` times the high word of `u m₀` plus the carry of its low word plus `s₀`. -/
theorem fios_red_arith (t u m : BitVec 64) (h : ((u * m).toNat + t.toNat) % 2 ^ 64 = 0) :
    2 ^ 64 * (BitVec.ofNat 64 (u.toNat * m.toNat / 2 ^ 64) + (if u * m + t < t then 1 else 0)).toNat =
      u.toNat * m.toNat + t.toNat := by
  have hu := u.isLt
  have hm := m.isLt
  have ht := t.isLt
  have hP : u.toNat * m.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  simp only [BitVec.toNat_add (BitVec.ofNat 64 _), carry_toNat]
  simp only [BitVec.toNat_mul] at h
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  by_cases h1 : 2 ^ 64 ≤ u.toNat * m.toNat % 2 ^ 64 + t.toNat <;>
    simp only [h1, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- The registers the start of a round writes. -/
def fiosHeadRegs : List Reg := [.a0, .a3, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- The start of a round (`fiosHead ++ fiosRem`), for `aᵢ` at `da` (`a3`),
`T` at `dA`, `b` at `dB`, `m` at `dM`, `w` in `t0` and `-m⁻¹ mod 2⁶⁴` in
`t1`: `aᵢ` in `t6`, `t2` a `u < 2⁶⁴` such that `2⁶⁴ (c + d) = t₀ + aᵢ b₀ + u
m₀` for the carries `c` in `s0` and `d` in `s1`, the pointers at word 0 and
`(w - 1) mod 4` in `t5`. -/
theorem fiosHead_ok {s : State} {B : Addr} {Z da dA dB dM w : Nat} (hs : Scr s B Z)
    (ha8 : da % 8 = 0) (hA8 : dA % 8 = 0) (hB8 : dB % 8 = 0) (hM8 : dM % 8 = 0)
    (h3 : s.gpr .a3 = off B da) (h4 : s.gpr .a4 = off B dB) (h5 : s.gpr .a5 = off B dA)
    (h7 : s.gpr .a7 = off B dM) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((word s.mem B dM).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (ha : da + 8 ≤ Z) (hA : dA + 8 ≤ Z) (hB : dB + 8 ≤ Z) (hM : dM + 8 ≤ Z) :
    WP isa (.block (fiosHead ++ fiosRem)) s fun s' =>
      (s'.gpr .t6 = word s.mem B da ∧ s'.gpr .a3 = off B (da + 8) ∧ s'.gpr .t3 = off B dA ∧
        s'.gpr .t4 = off B dB ∧ s'.gpr .a0 = off B dM ∧ s'.gpr .t5 = BitVec.ofNat 64 ((w - 1) % 4) ∧
        s'.mem = s.mem ∧
        2 ^ 64 * ((s'.gpr .s0).toNat + (s'.gpr .s1).toNat) = (word s.mem B dA).toNat +
          (word s.mem B da).toNat * (word s.mem B dB).toNat + (s'.gpr .t2).toNat * (word s.mem B dM).toNat) ∧
      Keep fiosHeadRegs s s' := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold fiosHead fiosRem
  brun [h3, h4, h5, h7, ht0, hs.ld ha, hs.ld hA, hs.ld hB, hs.ld hM, BitVec.add_zero,
    hs.al8 ha ha8, hs.al8 hA hA8, hs.al8 hB hB8, hs.al8 hM hM8,
    ofNat_sub_one hw (by omega_arith), fios_rem (w - 1) (by omega_arith)]
  have h1 := fios_head_arith (word s.mem B dA) (word s.mem B da) (word s.mem B dB)
  have h2 := fios_red_arith (word s.mem B dA + word s.mem B da * word s.mem B dB)
    ((word s.mem B dA + word s.mem B da * word s.mem B dB) * s.gpr .t1) (word s.mem B dM) (by
    rw [BitVec.toNat_mul, BitVec.toNat_mul, Nat.mod_add_mod, Nat.add_comm]; exact mont_low _ _ _ hinv)
  simp only [Nat.reducePow, word] at h1 h2 ⊢
  omega_arith

/-- The arithmetic of the end of a round: `c + t + d` as two words, the high
word the sum of the two carries. -/
theorem fios_top_arith (c t d : BitVec 64) :
    (c + t + d).toNat +
      2 ^ 64 * ((if c + t < t then (1 : BitVec 64) else 0) + (if c + t + d < d then 1 else 0)).toNat =
      c.toNat + t.toNat + d.toNat := by
  have hc := c.isLt
  have ht := t.isLt
  have hd := d.isLt
  simp only [BitVec.toNat_add (if _ then _ else _), carry_toNat]
  simp only [BitVec.toNat_add]
  by_cases h1 : 2 ^ 64 ≤ c.toNat + t.toNat <;>
    by_cases h2 : 2 ^ 64 ≤ (c.toNat + t.toNat) % 2 ^ 64 + d.toNat <;>
    simp only [h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- The end of a round (`fiosTop`), `t3` at `dT`: the carries `c` (`s0`) and
`d` (`s1`) plus the word at `dT + 8`, stored as two words at `dT`. -/
theorem fiosTop_ok {s : State} {B : Addr} {Z dT : Nat} (hs : Scr s B Z) (h3 : s.gpr .t3 = off B dT)
    (hT8 : dT % 8 = 0) (hT : dT + 16 ≤ Z) :
    WP isa (.block fiosTop) s fun s' =>
      (∃ x y : BitVec 64, s'.mem = (s.mem.writeW (off B dT) x).writeW (off B (dT + 8)) y ∧
        x.toNat + 2 ^ 64 * y.toNat = (s.gpr .s0).toNat + (word s.mem B (dT + 8)).toNat + (s.gpr .s1).toNat) ∧
      Keep fiosRegs s s' := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold fiosTop
  brun [h3, hs.ld (show dT + 8 + 8 ≤ Z by omega_arith), hs.st (show dT + 8 ≤ Z by omega_arith),
    hs.st (show dT + 8 + 8 ≤ Z by omega_arith), hs.al8 (show dT + 8 + 8 ≤ Z by omega_arith) (by omega_arith),
    hs.al8 (show dT + 8 ≤ Z by omega_arith) hT8, BitVec.add_zero]
  have h := fios_top_arith (s.gpr .s0) (word s.mem B (dT + 8)) (s.gpr .s1)
  simp only [Nat.reducePow, word] at h ⊢
  exact ⟨_, _, rfl, h⟩

/-- `(w - 1) / 4` into `t5`. -/
theorem fiosQuot_ok {s : State} {w : Nat} (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) :
    WP isa (.block fiosQuot) s fun s' =>
      (s'.gpr .t5 = BitVec.ofNat 64 ((w - 1) / 4) ∧ s'.mem = s.mem) ∧ Keep [.t5] s s' := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold fiosQuot
  brun [ht0, ofNat_sub_one hw (by omega_arith), fios_quot (w - 1) (by omega_arith)]

/-- Two words stored at `d + 8 j`, `d + 8 j + 8`, above `j` words at `d`. -/
theorem fios_wordsVal_write2 (m : Mem) (B : Addr) (d j : Nat) (v v' : BitVec 64) (h : d + 8 * j + 16 ≤ 2 ^ 64) :
    wordsVal ((m.writeW (off B (d + 8 * j)) v).writeW (off B (d + 8 * j + 8)) v') B d (j + 2) =
      wordsVal m B d j + 2 ^ (64 * j) * (v.toNat + 2 ^ 64 * v'.toNat) := by
  rw [show d + 8 * j + 8 = d + 8 * (j + 1) by omega_arith, fios_wordsVal_write_top _ _ _ _ _ (by omega_arith),
    fios_wordsVal_write_top _ _ _ _ _ (by omega_arith), Nat.mul_succ, Nat.pow_add]
  grind

/-- The sum of a round: `2⁶⁴ (W + P (c + t_w + d)) = T + aᵢ b + u m`, from that of
words `1` to `w - 1`, `W + P (c + d) = T' + aᵢ b' + u m' + C₀`, and of word 0,
`2⁶⁴ C₀ = t₀ + aᵢ b₀ + u m₀`. -/
theorem fios_round_sum {W T S M C₀ c d a u t0 b0 m0 tw x P : Nat}
    (e : W + P * (c + d) = T + a * S + u * M + C₀) (h0 : 2 ^ 64 * C₀ = t0 + a * b0 + u * m0)
    (hx : x = c + tw + d) :
    2 ^ 64 * (W + P * x) = t0 + 2 ^ 64 * (T + P * tw) + a * (b0 + 2 ^ 64 * S) + u * (m0 + 2 ^ 64 * M) := by
  subst hx
  grind

theorem fios_wordsVal_pred (m : Mem) (B : Addr) (d : Nat) {w : Nat} (hw : 1 ≤ w) :
    wordsVal m B d w = (word m B d).toNat + 2 ^ 64 * wordsVal m B (d + 8) (w - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega_arith⟩
  rfl

/-- The registers a round writes. -/
def roundRegs : List Reg := [.a0, .a3, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- A round (`round`), for `aᵢ` at `da` (`a3`, advanced), `T` (`w + 1` words)
at `dA`, `b` and `m` (`w` words) at `dB` and `dM`, `w` in `t0` and `-m⁻¹ mod
2⁶⁴` in `t1`: `2⁶⁴ T' = T + aᵢ b + u m` for some `u < 2⁶⁴`. -/
theorem round_ok {s : State} {B : Addr} {Z da dA dB dM w : Nat} (hs : Scr s B Z)
    (ha8 : da % 8 = 0) (hA8 : dA % 8 = 0) (hB8 : dB % 8 = 0) (hM8 : dM % 8 = 0)
    (h3 : s.gpr .a3 = off B da) (h4 : s.gpr .a4 = off B dB) (h5 : s.gpr .a5 = off B dA)
    (h7 : s.gpr .a7 = off B dM) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((word s.mem B dM).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (ha : da + 8 ≤ Z) (hA : dA + 8 * (w + 1) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dB) (dMA : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dM) :
    WP isa round s fun s' =>
      (s'.gpr .a3 = off B (da + 8) ∧ Outside B dA (8 * (w + 1)) s.mem s'.mem ∧
        ∃ u < 2 ^ 64, 2 ^ 64 * wordsVal s'.mem B dA (w + 1) =
          wordsVal s.mem B dA (w + 1) + (word s.mem B da).toNat * wordsVal s.mem B dB w +
            u * wordsVal s.mem B dM w) ∧
      Keep roundRegs s s' := by
  have hnw := hs.nowrap
  have hK := Nat.mod_add_div (w - 1) 4
  generalize hN₁ : (w - 1) % 4 = N₁ at hK
  generalize hN₂ : (w - 1) / 4 = N₂ at hK
  have hN₁4 : N₁ < 4 := hN₁ ▸ Nat.mod_lt _ (by decide)
  unfold round
  -- Word 0.
  refine WP.seq (WP.mono (fiosHead_ok hs ha8 hA8 hB8 hM8 h3 h4 h5 h7 ht0 hinv hw hw' ha (by omega_arith)
    (by omega_arith) (by omega_arith))
    fun s₁ ⟨⟨i6, i3, i3', i4, i0, i5, im, i0'⟩, k₁⟩ => ?_)
  rw [hN₁] at i5
  -- Words `1` to `N₁`, one at a time.
  refine WP.seq (WP.mono (fiosLoop?_ok (U := 1) (N := N₁) (by decide) (hs.congr k₁.2.2) hA8 hB8 hM8 i3' i4 i0 i5
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₂ ⟨j3, j4, j0, jout, jeq, k₂⟩ => ?_)
  rw [Nat.one_mul] at j3 j4 j0 jout jeq
  have g₂ : ∀ r ∈ [Reg.a3, .t0, .t6, .t2], s₂.gpr r = s₁.gpr r := fun r hr => k₂.gpr (by revert r hr; decide)
  have g₁ : s₁.gpr .t0 = s.gpr .t0 := k₁.gpr (by decide)
  -- The count of groups of four.
  refine WP.seq (WP.mono (fiosQuot_ok (s := s₂) (w := w) (by rw [g₂ .t0 (by decide), g₁, ht0]) hw hw')
    fun s₃ ⟨⟨l5, lm⟩, k₃⟩ => ?_)
  rw [hN₂] at l5
  have g₃ : ∀ r ∈ [Reg.t2, .a0, .a3, .t3, .t4, .t6, .s0, .s1], s₃.gpr r = s₂.gpr r := fun r hr =>
    k₃.gpr (by revert r hr; decide)
  -- Words `N₁ + 1` to `w - 1`, four at a time.
  refine WP.seq (WP.mono (fiosLoop?_ok (U := 4) (N := N₂) (dT := dA + 8 * N₁) (dB := dB + 8 * N₁)
    (dM := dM + 8 * N₁) (by decide) (hs.congr (k₁.trans (k₂.trans k₃)).2.2) (by omega_arith) (by omega_arith)
    (by omega_arith) (by rw [g₃ .t3 (by decide), j3])
    (by rw [g₃ .t4 (by decide), j4]) (by rw [g₃ .a0 (by decide), j0]) l5 (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun s₄ ⟨n3, _, _, nout, neq, k₄⟩ => ?_)
  -- Word `w` and the carries.
  refine WP.mono (fiosTop_ok (dT := dA + 8 * (w - 1)) (hs.congr (k₁.trans (k₂.trans (k₃.trans k₄))).2.2)
    (by rw [n3, Nat.add_assoc, ← Nat.mul_add, show N₁ + 4 * N₂ = w - 1 by omega_arith]) (by omega_arith)
    (by omega_arith))
    fun s₅ ⟨⟨x, y, tm, txy⟩, k₅⟩ => ?_
  have k25 := k₂.trans (k₃.trans (k₄.trans k₅))
  have pK : 2 ^ (64 * N₁) * 2 ^ (64 * (4 * N₂)) = 2 ^ (64 * (w - 1)) := by
    rw [← Nat.pow_add, ← Nat.mul_add, hK]
  -- The memory outside `T` is that on entry.
  have o₄ : Outside B dA (8 * (w - 1)) s.mem s₄.mem := by
    rw [← im]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (by rw [← lm]; exact nout.mono (by omega_arith) (by omega_arith))
  refine ⟨⟨by rw [k25.gpr (by decide), i3], ?_, (s₁.gpr .t2).toNat, (s₁.gpr .t2).isLt, ?_⟩,
    (k₁.trans k25).mono (by decide)⟩
  · rw [tm]
    exact (o₄.mono (Nat.le_refl _) (by omega_arith)).trans
      (((writeW_outside _ B _ (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
        ((writeW_outside _ B _ (by omega_arith)).mono (by omega_arith) (by omega_arith)))
  -- The words read by the second loop and the end are those on entry.
  have rd : ∀ d, (d + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ d ∨ d = dA) → d + 8 * w ≤ Z →
      wordsVal s₃.mem B (d + 8 * N₁ + 8) (4 * N₂) = wordsVal s.mem B (d + 8 + 8 * N₁) (4 * N₂) := by
    intro d hd hdZ
    rw [lm, show d + 8 * N₁ + 8 = d + 8 + 8 * N₁ by omega_arith, jout.wordsVal (by omega_arith) (by omega_arith), im]
  have tw : word s₄.mem B (dA + 8 * (w - 1) + 8) = word s.mem B (dA + 8 + 8 * (w - 1)) := by
    rw [o₄.word (by omega_arith) (by omega_arith), show dA + 8 * (w - 1) + 8 = dA + 8 + 8 * (w - 1) by omega_arith]
  rw [rd dA (.inr (.inr rfl)) (by omega_arith), rd dB (by omega_arith) hB, rd dM (by omega_arith) hM, g₃ .t2 (by decide),
    g₃ .t6 (by decide), g₃ .s0 (by decide), g₃ .s1 (by decide), g₂ .t2 (by decide), g₂ .t6 (by decide)] at neq
  rw [im] at jeq
  rw [tw] at txy
  have e := fios_sum_group jeq neq rfl
  rw [← fios_wordsVal_append, ← fios_wordsVal_append, ← fios_wordsVal_append, hK, pK] at e
  rw [show wordsVal s₂.mem B dA N₁ = wordsVal s₄.mem B dA N₁ by
      rw [← lm]; exact (nout.wordsVal (by omega_arith) (by omega_arith)).symm,
    ← fios_wordsVal_append, hK] at e
  rw [tm, show w + 1 = w - 1 + 2 by omega_arith, fios_wordsVal_write2 _ _ _ _ _ _ (by omega_arith),
    fios_wordsVal_pred s.mem B dA (show 1 ≤ w - 1 + 2 by omega_arith), show w - 1 + 2 - 1 = w - 1 + 1 by omega_arith,
    wordsVal_succ_top s.mem B (dA + 8) (w - 1), fios_wordsVal_pred s.mem B dB hw,
    fios_wordsVal_pred s.mem B dM hw]
  rw [i6] at e
  exact fios_round_sum e i0' txy

end VG.Proof.Bignum.RISCV64
