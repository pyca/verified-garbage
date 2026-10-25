module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontSqr
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Montgomery squaring on PPC64LE: the words without a product

`rstep_ok`: a word `j < i` of round `i` of `MontSqr.sqrTail`, `tⱼ + u mⱼ`
plus the carry `d`, its low word stored and `d` replaced; `rLoop?_ok`: a
loop of them (`countLoop? (rgroup U)`), as `fiosLoop?_ok` for `fiosStep`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Sqr

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.MontSqr
open VG.Proof.Bignum.PPC64LE

/-- The arithmetic of a word: `u m + t + d`, below `2¹²⁸`, is the low word of
`u m + t + d` and `2⁶⁴` times the high word of `u m` plus both carries. -/
theorem rstep_arith (t u m d : BitVec 64) :
    (BitVec.ofNat 64 ((BitVec.ofNat 64 ((u * m).toNat + t.toNat)).toNat + d.toNat)).toNat +
      2 ^ 64 * (BitVec.ofNat 64 ((BitVec.ofNat 64 ((BitVec.ofNat 64 (u.toNat * m.toNat / 2 ^ 64)).toNat +
        (decide (2 ^ 64 ≤ (u * m).toNat + t.toNat)).toNat)).toNat +
          (decide (2 ^ 64 ≤ (BitVec.ofNat 64 ((u * m).toNat + t.toNat)).toNat + d.toNat)).toNat)).toNat =
      t.toNat + u.toNat * m.toNat + d.toNat := by
  have ht := t.isLt
  have hu := u.isLt
  have hm := m.isLt
  have hd := d.isLt
  have hP : u.toNat * m.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  simp only [BitVec.toNat_ofNat, BitVec.toNat_mul]
  by_cases h1 : 2 ^ 64 ≤ u.toNat * m.toNat % 2 ^ 64 + t.toNat <;>
    by_cases h2 : 2 ^ 64 ≤ (u.toNat * m.toNat % 2 ^ 64 + t.toNat) % 2 ^ 64 + d.toNat <;>
    simp only [h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem rstep_writes (k : Nat) : writesOnly fiosRegs (.block (rstep k)) = true := rfl

theorem rstep_ok {s : State} {B : Addr} {Z dT dM k : Nat} (hs : Scr s B Z)
    (h14 : s.gpr .r14 = off B dT) (h3 : s.gpr .r3 = off B dM)
    (hk : k + 8 < 32768) (hk4 : k % 4 = 0) (hT : dT + k + 16 ≤ Z) (hM : dM + k + 16 ≤ Z) :
    WP isa (.block (rstep k)) s fun s' =>
      (∃ v : BitVec 64, s'.mem = s.mem.writeW (off B (dT + k)) v ∧
        v.toNat + 2 ^ 64 * (s'.gpr .r22).toNat =
          (word s.mem B (dT + (k + 8))).toNat + (s.gpr .r0).toNat * (word s.mem B (dM + (k + 8))).toNat +
            (s.gpr .r22).toNat) ∧ Keep fiosRegs s s' := by
  have hk1 : k < 32768 := by omega
  have hk2 : (k + 8) % 4 = 0 := by omega
  refine WP.keep _ ?_ (rstep_writes k)
  unfold rstep
  mcrun [h14, h3, hk, hk1, hk2, hk4, hs.ld (show dT + (k + 8) + 8 ≤ Z by omega),
    hs.ld (show dM + (k + 8) + 8 ≤ Z by omega), hs.st (show dT + k + 8 ≤ Z by omega)]
  refine ⟨_, rfl, ?_⟩
  have h := rstep_arith (word s.mem B (dT + (k + 8))) (s.gpr .r0) (word s.mem B (dM + (k + 8))) (s.gpr .r22)
  simp only [Nat.reducePow, word] at h ⊢
  omega

theorem rsteps_succ (K : Nat) :
    (List.range (K + 1)).flatMap (fun k => rstep (8 * k)) =
      (List.range K).flatMap (fun k => rstep (8 * k)) ++ rstep (8 * K) := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The sum of `K + 1` words, as the sum of the first `K` and the last. -/
theorem r_sum_succ {W T M W' C₀ C₁ C₂ u v t m P : Nat}
    (e₁ : W + P * C₁ = T + u * M + C₀) (e₂ : v + 2 ^ 64 * C₂ = t + u * m + C₁) (hW : W' = W + P * v) :
    W' + P * 2 ^ 64 * C₂ = T + P * t + u * (M + P * m) + C₀ := by
  subst hW
  have e : P * v + P * 2 ^ 64 * C₂ = P * (t + u * m + C₁) := by
    rw [← e₂, Nat.mul_add, Nat.mul_assoc]
  grind

/-- `K` words (`8 K + 8` bytes into the arrays at most `2¹⁵`), the pointers
`r14`, `r3` at offsets `dT`, `dM`: the `K` words stored from `dT` on and the
carry `r22` make up `T + u M` plus the carry on entry, for the `K` words
`T`, `M` from `dT + 8`, `dM + 8` on and `u` in `r0`. -/
theorem rsteps_ok {B : Addr} {Z dT dM : Nat} : ∀ (K : Nat) {s : State}, Scr s B Z →
    s.gpr .r14 = off B dT → s.gpr .r3 = off B dM → 8 * K < 32768 →
    dT + 8 * K + 8 ≤ Z → dM + 8 * K + 8 ≤ Z → (dM + 8 * K + 8 ≤ dT ∨ dT + 8 * K ≤ dM + 8) →
    WP isa (.block ((List.range K).flatMap fun k => rstep (8 * k))) s fun s' =>
      (Outside B dT (8 * K) s.mem s'.mem ∧
        wordsVal s'.mem B dT K + 2 ^ (64 * K) * (s'.gpr .r22).toNat =
          wordsVal s.mem B (dT + 8) K + (s.gpr .r0).toNat * wordsVal s.mem B (dM + 8) K + (s.gpr .r22).toNat) ∧
      Keep fiosRegs s s'
  | 0, s, _, _, _, _, _, _, _ => by
    simp only [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨⟨Outside.refl _ _ _ _, by simp [wordsVal]⟩, Keep.refl _ _⟩
  | K + 1, s, hs, h14, h3, hK, hT, hM, sM => by
    have hnw := hs.nowrap
    rw [rsteps_succ, WP.block_append_iff]
    refine WP.mono (rsteps_ok K hs h14 h3 (by omega) (by omega) (by omega) (by omega))
      fun s₁ ⟨⟨o₁, e₁⟩, k₁⟩ => ?_
    have g : ∀ r ∈ [Reg.r0, .r3, .r14], s₁.gpr r = s.gpr r := fun r hr =>
      k₁.gpr r (by revert r hr; decide)
    refine WP.mono (rstep_ok (dT := dT) (dM := dM) (k := 8 * K) (hs.congr k₁.wr) (by rw [g .r14 (by decide), h14])
      (by rw [g .r3 (by decide), h3]) (by omega) (by omega) (by omega) (by omega))
      fun s₂ ⟨⟨v, m₂, e₂⟩, k₂⟩ => ⟨⟨?_, ?_⟩, (k₁.trans k₂).mono (by decide)⟩
    · rw [m₂]
      exact (o₁.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside _ B v (by omega)).mono (by omega) (by omega))
    · rw [show dT + (8 * K + 8) = dT + 8 + 8 * K by omega, show dM + (8 * K + 8) = dM + 8 + 8 * K by omega,
        o₁.word (by omega) (by omega), o₁.word (by omega) (by omega), g .r0 (by decide)] at e₂
      rw [m₂, fios_wordsVal_write_top _ _ _ _ _ (by omega), wordsVal_succ_top s.mem B (dT + 8) K,
        wordsVal_succ_top s.mem B (dM + 8) K, Nat.mul_succ, Nat.pow_add]
      exact r_sum_succ e₁ e₂ rfl

/-- The sum of a loop's iterations, as the sum of the first ones and the last. -/
theorem r_sum_group {W T M W' C₀ C₁ C₂ u G T' M' P Q : Nat}
    (e₁ : W + P * C₁ = T + u * M + C₀) (e₂ : G + Q * C₂ = T' + u * M' + C₁) (hW : W' = W + P * G) :
    W' + P * Q * C₂ = T + P * T' + u * (M + P * M') + C₀ := by
  subst hW
  have e : P * G + P * Q * C₂ = P * (T' + u * M' + C₁) := by
    rw [← e₂, Nat.mul_add, Nat.mul_assoc]
  grind

/-- What `N` iterations of `U` words leave, the pointers at offsets `dT`,
`dB`, `dM` on entry: `rsteps_ok` for `U N` words, the pointers advanced past
them. -/
def RPost (B : Addr) (dT dB dM K : Nat) (s₀ s : State) : Prop :=
  s.gpr .r14 = off B (dT + 8 * K) ∧ s.gpr .r15 = off B (dB + 8 * K) ∧ s.gpr .r3 = off B (dM + 8 * K) ∧
    Outside B dT (8 * K) s₀.mem s.mem ∧
    wordsVal s.mem B dT K + 2 ^ (64 * K) * (s.gpr .r22).toNat =
      wordsVal s₀.mem B (dT + 8) K + (s₀.gpr .r0).toNat * wordsVal s₀.mem B (dM + 8) K + (s₀.gpr .r22).toNat ∧
    Keep fiosLoopRegs s₀ s

/-- `N > 0` iterations of `U` words (`countLoop .r16 (rgroup U)`). -/
theorem rLoop_ok {B : Addr} {Z dT dB dM U N : Nat} (hU : 8 * U < 32768) {s₀ : State} (hs : Scr s₀ B Z)
    (h14 : s₀.gpr .r14 = off B dT) (h15 : s₀.gpr .r15 = off B dB) (h3 : s₀.gpr .r3 = off B dM)
    (h16 : s₀.gpr .r16 = BitVec.ofNat 64 N) (hN : 1 ≤ N) (hN' : N < 2 ^ 32)
    (hT : dT + 8 * (U * N) + 8 ≤ Z) (hM : dM + 8 * (U * N) + 8 ≤ Z)
    (sM : dM + 8 * (U * N) + 8 ≤ dT ∨ dT + 8 * (U * N) ≤ dM + 8) :
    WP isa (countLoop .r16 (rgroup U)) s₀ (RPost B dT dB dM (U * N) s₀) := by
  have hnw := hs.nowrap
  refine wp_countdown (body := .block (rgroup U ++ ([.subi .r16 .r16 1] : List Instr))) (cnt := .r16)
    (N := N) (by omega) (by omega) (fun i s => RPost B dT dB dM (U * i) s₀ s) (fun i hi s hI hc => ?_)
    ⟨by rw [h14]; rfl, by rw [h15]; rfl, by rw [h3]; rfl, Outside.refl _ _ _ _, by simp [wordsVal],
      Keep.refl _ _⟩ h16
  obtain ⟨i14, i15, i3, iout, ieq, ik⟩ := hI
  have hUi : U * i + U ≤ U * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have g : s.gpr .r0 = s₀.gpr .r0 := ik.gpr _ (by decide)
  rw [rgroup, List.append_assoc, WP.block_append_iff]
  refine WP.mono (rsteps_ok U (hs.congr ik.wr) i14 i3 hU (by omega) (by omega) (by omega))
    fun s₁ ⟨⟨o₁, e₁⟩, k₁⟩ => ?_
  have g₁ : ∀ r ∈ [Reg.r3, .r14, .r15, .r16], s₁.gpr r = s.gpr r := fun r hr =>
    k₁.gpr r (by revert r hr; decide)
  have hst : WP isa (.block [.addi .r14 .r14 (8 * U), .addi .r15 .r15 (8 * U), .addi .r3 .r3 (8 * U),
      .subi .r16 .r16 1]) s₁ fun s₂ =>
      s₂ = (((s₁.write .r14 (off B (dT + 8 * (U * i) + 8 * U))).write .r15 (off B (dB + 8 * (U * i) + 8 * U))).write
        .r3 (off B (dM + 8 * (U * i) + 8 * U))).write .r16 (s₁.gpr .r16 - BitVec.ofNat 64 1) := by
    prun [g₁ .r14 (by decide), g₁ .r15 (by decide), g₁ .r3 (by decide), i14, i15, i3, hU]
  refine WP.mono hst fun s₂ e => ?_
  subst e
  have pU : U * (i + 1) = U * i + U := Nat.mul_succ _ _
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by gsimp; rw [g₁ .r16 (by decide)]⟩
  · gsimp; rw [pU, Nat.mul_add, Nat.add_assoc]
  · gsimp; rw [pU, Nat.mul_add, Nat.add_assoc]
  · gsimp; rw [pU, Nat.mul_add, Nat.add_assoc]
  · gsimp
    exact (iout.mono (Nat.le_refl _) (by omega)).trans (o₁.mono (by omega) (by omega))
  · gsimp
    rw [show dM + 8 * (U * i) + 8 = dM + 8 + 8 * (U * i) by omega,
      iout.wordsVal (o := dT) (n := 8 * (U * i)) (by omega) (by omega), g] at e₁
    rw [show dT + 8 * (U * i) + 8 = dT + 8 + 8 * (U * i) by omega,
      iout.wordsVal (o := dT) (n := 8 * (U * i)) (by omega) (by omega)] at e₁
    rw [pU, fios_wordsVal_append s₁.mem B dT (U * i) U, fios_wordsVal_append s₀.mem B (dT + 8) (U * i) U,
      fios_wordsVal_append s₀.mem B (dM + 8) (U * i) U,
      show 64 * (U * i + U) = 64 * (U * i) + 64 * U by omega, Nat.pow_add,
      (o₁.wordsVal (o := dT + 8 * (U * i)) (n := 8 * U) (d := dT) (k := U * i) (by omega) (by omega))]
    exact r_sum_group ieq e₁ rfl
  · exact ik.trans' ((k₁.mono (by decide)).trans' (Keep.mono (by
      exact (((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _))
      (by decide)))

/-- `N` iterations of `U` words if `N ≠ 0` (`countLoop? (rgroup U)`). -/
theorem rLoop?_ok {B : Addr} {Z dT dB dM U N : Nat} (hU : 8 * U < 32768) {s₀ : State} (hs : Scr s₀ B Z)
    (h14 : s₀.gpr .r14 = off B dT) (h15 : s₀.gpr .r15 = off B dB) (h3 : s₀.gpr .r3 = off B dM)
    (h16 : s₀.gpr .r16 = BitVec.ofNat 64 N) (hN' : N < 2 ^ 32)
    (hT : dT + 8 * (U * N) + 8 ≤ Z) (hM : dM + 8 * (U * N) + 8 ≤ Z)
    (sM : dM + 8 * (U * N) + 8 ≤ dT ∨ dT + 8 * (U * N) ≤ dM + 8) :
    WP isa (countLoop? (rgroup U)) s₀ (RPost B dT dB dM (U * N) s₀) := by
  refine WP.ite _ (eval_zero_ofNat _ _ (by omega) h16) (fun hz => ?_) (fun hz => ?_)
  · have hN : N = 0 := of_decide_eq_true hz
    subst hN
    exact WP.block_nil ⟨by rw [h14]; rfl, by rw [h15]; rfl, by rw [h3]; rfl, Outside.refl _ _ _ _,
      by simp [wordsVal], Keep.refl _ _⟩
  · exact rLoop_ok hU hs h14 h15 h3 h16 (Nat.pos_of_ne_zero (of_decide_eq_false hz)) hN' hT hM sM

end VG.Proof.Bignum.PPC64LE.Sqr
