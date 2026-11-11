module

public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Run
public import VerifiedGarbage.Impl.Bignum.X86.R2Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power

/-!
# `R2Words` on x86: `p = 2^z` and `d`

`normBit` doubles `eax` and `esi` where the top bit of `eax` is clear
(`normBit_ok`); 31 of them take the top word `T ≠ 0` of `M` to `T 2^z` and
`1` to `2^z`, for the leading zeros `z` of `T` (`normLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.R2Words

open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.R2Words

/-- The mask of a clear top bit. -/
def clearMask (a : BitVec 32) : BitVec 32 := (a >>> 31) - 1

theorem normBit_ok {s : State} :
    WP isa (.block normBit) s fun t =>
      t.gpr .eax = s.gpr .eax + (s.gpr .eax &&& clearMask (s.gpr .eax)) ∧
      t.gpr .esi = s.gpr .esi + (s.gpr .esi &&& clearMask (s.gpr .eax)) ∧
      t.gpr .edx = s.gpr .edx - 1 ∧ t.zf = some (s.gpr .edx - 1 == 0) ∧ t.mem = s.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.mono (WP.keeps [.eax, .ecx, .edx, .ebp, .esi] (Q := fun t =>
      t.gpr .eax = s.gpr .eax + (s.gpr .eax &&& clearMask (s.gpr .eax)) ∧
      t.gpr .esi = s.gpr .esi + (s.gpr .esi &&& clearMask (s.gpr .eax)) ∧
      t.gpr .edx = s.gpr .edx - 1 ∧ t.zf = some (s.gpr .edx - 1 == 0) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  xrun [normBit, clearMask]

/-- The leading zeros of a nonzero word. -/
def lz (T : Nat) : Nat := 31 - T.log2

/-- `T 2^i` for `i ≤ lz T` fits a word, with its top bit set exactly when `i = lz T`. -/
theorem shifted_bounds {T i : Nat} (hT : 0 < T) (hT' : T < 2 ^ 32) (hi : i ≤ lz T) :
    T * 2 ^ i < 2 ^ 32 ∧ (T * 2 ^ i / 2 ^ 31 = if i = lz T then 1 else 0) := by
  have hL : T.log2 < 32 := (Nat.log2_lt (by omega)).mpr hT'
  have h1 := Nat.log2_self_le (n := T) (by omega)
  have h2 := Nat.lt_log2_self (n := T)
  unfold lz at hi ⊢
  have u : T * 2 ^ i < 2 ^ (T.log2 + 1 + i) := by rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)
  have l : 2 ^ (T.log2 + i) ≤ T * 2 ^ i := by rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ h1
  have p1 : 2 ^ (T.log2 + 1 + i) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨Nat.lt_of_lt_of_le u p1, ?_⟩
  by_cases e : i = 31 - T.log2
  · simp only [e, ite_true]
    have a : 2 ^ (T.log2 + (31 - T.log2)) = 2 ^ 31 := congrArg _ (by omega)
    have b : 2 ^ (T.log2 + 1 + (31 - T.log2)) = 2 * 2 ^ 31 := by
      rw [show T.log2 + 1 + (31 - T.log2) = 31 + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    rw [e] at u l
    rw [Nat.div_eq_iff (by decide)]; omega
  · simp only [e, ite_false]
    have : 2 ^ (T.log2 + 1 + i) ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) (by omega)
    exact Nat.div_eq_of_lt (by omega)

/-- A step of the doublings: `T 2^i` and `2^i` to `T 2^min(i + 1, z)` and `2^min(i + 1, z)`. -/
theorem normStep_val {T i : Nat} (hT : 0 < T) (hT' : T < 2 ^ 32) (hi : i ≤ lz T) :
    BitVec.ofNat 32 (T * 2 ^ i) + (BitVec.ofNat 32 (T * 2 ^ i) &&& clearMask (BitVec.ofNat 32 (T * 2 ^ i))) =
      BitVec.ofNat 32 (T * 2 ^ min (i + 1) (lz T)) ∧
    BitVec.ofNat 32 (2 ^ i) + (BitVec.ofNat 32 (2 ^ i) &&& clearMask (BitVec.ofNat 32 (T * 2 ^ i))) =
      BitVec.ofNat 32 (2 ^ min (i + 1) (lz T)) := by
  obtain ⟨b1, b2⟩ := shifted_bounds hT hT' hi
  have hm : clearMask (BitVec.ofNat 32 (T * 2 ^ i)) = if i = lz T then 0 else BitVec.allOnes 32 := by
    unfold clearMask
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt b1,
      Nat.shiftRight_eq_div_pow, b2]
    by_cases e : i = lz T <;> simp [e]
  rw [hm]
  by_cases e : i = lz T
  · simp only [e, ite_true, Nat.min_eq_right (Nat.le_succ _)]
    exact ⟨by simp, by simp⟩
  · simp only [e, ite_false, BitVec.and_allOnes, ← BitVec.ofNat_add]
    rw [Nat.min_eq_left (by omega), Nat.pow_succ]
    exact ⟨congrArg _ (by rw [← Nat.mul_assoc]; omega), congrArg _ (by omega)⟩

/-- The 31 doublings: from `eax = T ≠ 0`, `esi = 1` and `edx = 31`, `eax = T 2^z`
and `esi = 2^z` for `z = lz T`. -/
theorem normLoop_ok {s : State} {T : Nat} (hT : 0 < T) (hT' : T < 2 ^ 32) (hax : s.gpr .eax = BitVec.ofNat 32 T)
    (hsi : s.gpr .esi = 1) (hdx : s.gpr .edx = 31) :
    WP isa (.loop (.block normBit) .ne) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (T * 2 ^ lz T) ∧ t.gpr .esi = BitVec.ofNat 32 (2 ^ lz T) ∧ t.mem = s.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s t := by
  have hz : lz T ≤ 31 := by unfold lz; omega
  refine WP.loop (M := isa) (fun n t => ∃ j, n = 31 - j ∧ j < 31 ∧
      t.gpr .eax = BitVec.ofNat 32 (T * 2 ^ min j (lz T)) ∧ t.gpr .esi = BitVec.ofNat 32 (2 ^ min j (lz T)) ∧
      t.gpr .edx = BitVec.ofNat 32 (31 - j) ∧ t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .esi] s t) ?_ _ s
    ⟨0, rfl, by decide, by rw [hax]; simp, by rw [hsi]; simp, by rw [hdx]; rfl, rfl, Keeps.refl _ _⟩
  rintro n t ⟨j, rfl, hj, hax', hsi', hdx', hm, k⟩
  refine WP.mono normBit_ok fun t' ⟨h1, h2, h3, h4, hm', k'⟩ => ?_
  obtain ⟨e1, e2⟩ := normStep_val hT hT' (i := min j (lz T)) (Nat.min_le_right _ _)
  have hmin : min (min j (lz T) + 1) (lz T) = min (j + 1) (lz T) := by omega
  rw [hmin] at e1 e2
  obtain ⟨c1, c2⟩ := VG.Proof.Bignum.X86.PublicRt.count1_zf (N := 31) (x := t.gpr .edx)
    (by rw [hdx', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) hj
  have hd : t'.gpr .edx = BitVec.ofNat 32 (31 - (j + 1)) := by
    rw [h3]; apply BitVec.eq_of_toNat_eq; rw [c1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have K := k.trans k'
  by_cases e : j + 1 = 31
  · refine .inl ⟨by simp only [eval, h4, c2, e, decide_true, Option.map_some, Bool.not_true], ?_, ?_, hm'.trans hm, K⟩
    · rw [h1, hax', e1, Nat.min_eq_right (by omega)]
    · rw [h2, hsi', hax', e2, Nat.min_eq_right (by omega)]
  · refine .inr ⟨by simp only [eval, h4, c2, e, decide_false, Option.map_some, Bool.not_false], 31 - (j + 1), by omega, j + 1, rfl, by omega, ?_, ?_, hd,
      hm'.trans hm, K⟩
    · rw [h1, hax', e1]
    · rw [h2, hsi', hax', e2]

end VG.Proof.Bignum.X86.R2Words
