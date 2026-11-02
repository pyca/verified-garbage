module

public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Candidate
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.RsaKeyGen.Gcd
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on RISC-V: the steps on words

`modBit_ok`: one bit of `(c − 1) mod e`, `a1 := (2 a1 + x₆₃) mod e` for
`a1 < e` (in `s10`), `a2 := 2 x`; `gcdStep_ok`: one step of the binary gcd
on `u = a1` and the odd `v = s10`, as `Proof.RsaKeyGen.gcdStep`. A flag
`f ∈ {0, 1}` from `sltu` or a low bit becomes the mask `0 − f`, which selects
between two words by `y ^ ((x ^ y) & mask)` (`sel_mask`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64

theorem sltu_val (a b : BitVec 64) :
    (if a < b then (1 : BitVec 64) else 0) = BitVec.ofNat 64 (if a.toNat < b.toNat then 1 else 0) := by
  by_cases h : a.toNat < b.toNat
  · rw [ite_eq_left (BitVec.lt_def.mpr h), ite_eq_left h]; rfl
  · rw [ite_eq_right (fun e => h (BitVec.lt_def.mp e)), ite_eq_right h]; rfl

theorem shr63_val (a : BitVec 64) : a >>> 63 = BitVec.ofNat 64 (a.toNat / 2 ^ 63) := by
  have := a.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_arith)]

/-- A selection under the mask of a flag. -/
theorem sel_mask (c : Prop) [Decidable c] (x y : BitVec 64) :
    y ^^^ ((x ^^^ y) &&& (0 - BitVec.ofNat 64 (if c then 1 else 0))) = if c then x else y := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h, show (0 : BitVec 64) - BitVec.ofNat 64 1 = BitVec.allOnes 64 by decide,
      BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_comm y x, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero]
  · rw [ite_eq_right h, ite_eq_right h, show (0 : BitVec 64) - BitVec.ofNat 64 0 = 0#64 by decide, BitVec.and_zero,
      BitVec.xor_zero]

/-- The low bit of a word as a flag. -/
theorem and1_val (a : BitVec 64) : a &&& 1#64 = BitVec.ofNat 64 (if a.toNat % 2 = 1 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_comm, Nat.one_and_eq_mod_two]
  split <;> simp_all

/-- The same, the other way round. -/
theorem sel_mask' (c : Prop) [Decidable c] (x y : BitVec 64) :
    (x ^^^ y) &&& (0 - BitVec.ofNat 64 (if c then 1 else 0)) ^^^ y = if c then x else y := by
  rw [BitVec.xor_comm, sel_mask]

/-- One step of the binary gcd on `u = a1` and the odd `v = s10`. -/
theorem gcdStep_ok {s : State} {u v : Nat} (h1 : s.gpr .a1 = BitVec.ofNat 64 u)
    (h10 : s.gpr .s10 = BitVec.ofNat 64 v) (hu : u < 2 ^ 64) (hv : v < 2 ^ 64) :
    WP isa (.block VG.Impl.RsaKeyGen.RISCV64.Candidate.gcdStep) s fun t =>
      (t.gpr .a1 = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.gcdStep u v).1 ∧
        t.gpr .s10 = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.gcdStep u v).2 ∧ t.mem = s.mem) ∧
        Keep [.t2, .a1, .a2, .a3, .a4, .a5, .s10] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [VG.Impl.RsaKeyGen.RISCV64.Candidate.gcdStep, h1, h10, fin64_exec_li_zero, sltu_val, and1_val, sel_mask,
    sel_mask']
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv]
  unfold VG.Proof.RsaKeyGen.gcdStep
  by_cases ho : u % 2 = 1
  · rw [ite_eq_left ho, ite_eq_left ho, ite_eq_left ho]
    by_cases hl : u < v
    · rw [ite_eq_left hl, ite_eq_left hl, ite_eq_left hl]
      refine ⟨BitVec.eq_of_toNat_eq ?_, rfl⟩
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      omega_arith
    · rw [ite_eq_right hl, ite_eq_right hl, ite_eq_right hl]
      refine ⟨BitVec.eq_of_toNat_eq ?_, rfl⟩
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      omega_arith
  · rw [ite_eq_right ho, ite_eq_right ho, ite_eq_right ho]
    refine ⟨BitVec.eq_of_toNat_eq ?_, rfl⟩
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_arith

/-- The condition of `modBit`'s subtraction. -/
theorem flag_val (p : Prop) [Decidable p] (a : BitVec 64) :
    BitVec.ofNat 64 (if p then 1 else 0) ^^^ 1#64 ||| a >>> 63 =
      BitVec.ofNat 64 (if ¬p ∨ 2 ^ 63 ≤ a.toNat then 1 else 0) := by
  rw [shr63_val]
  have := a.isLt
  by_cases hp : p
  · by_cases ha : 2 ^ 63 ≤ a.toNat
    · rw [ite_eq_left hp, ite_eq_left (Or.inr ha), show a.toNat / 2 ^ 63 = 1 by omega_arith]; decide
    · rw [ite_eq_left hp, ite_eq_right (fun h => h.elim (· hp) ha), show a.toNat / 2 ^ 63 = 0 by omega_arith]; decide
  · rw [ite_eq_right hp, ite_eq_left (Or.inl hp)]
    have : a.toNat / 2 ^ 63 = 0 ∨ a.toNat / 2 ^ 63 = 1 := by omega_arith
    rcases this with h | h <;> rw [h] <;> decide

/-- `modBit`: `a1 := (2 a1 + x₆₃) mod e` for `a1 < e`, and `a2 := 2 x`. -/
theorem modBit_ok {s : State} {acc x e : Nat} (h1 : s.gpr .a1 = BitVec.ofNat 64 acc)
    (h2 : s.gpr .a2 = BitVec.ofNat 64 x) (h10 : s.gpr .s10 = BitVec.ofNat 64 e) (hacc : acc < e)
    (he : e < 2 ^ 64) (hx : x < 2 ^ 64) :
    WP isa (.block VG.Impl.RsaKeyGen.RISCV64.Candidate.modBit) s fun t =>
      (t.gpr .a1 = BitVec.ofNat 64 ((2 * acc + x / 2 ^ 63) % e) ∧ t.gpr .a2 = BitVec.ofNat 64 (2 * x % 2 ^ 64) ∧
        t.mem = s.mem) ∧
        Keep [.a1, .a2, .a3, .a4, .a5] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have hy : BitVec.ofNat 64 acc <<< 1 + BitVec.ofNat 64 x >>> 63 =
      BitVec.ofNat 64 (2 * acc % 2 ^ 64 + x / 2 ^ 63) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show acc < 2 ^ 64 by omega_arith),
      Nat.mod_eq_of_lt hx]
    omega_arith
  brun [VG.Impl.RsaKeyGen.RISCV64.Candidate.modBit, h1, h2, h10, hy, fin64_exec_li_zero, sltu_val, flag_val,
    sel_mask]
  simp only [show (9223372036854775808 : Nat) = 2 ^ 63 by decide,
    show (18446744073709551616 : Nat) = 2 ^ 64 by decide]
  have hb : x / 2 ^ 63 ≤ 1 := by omega_arith
  refine ⟨?_, ?_⟩
  · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he,
      Nat.mod_eq_of_lt (show acc < 2 ^ 64 by omega_arith)]
    by_cases hA : 2 ^ 63 ≤ acc
    · rw [ite_eq_left (Or.inr hA)]
      have hm : (2 * acc + x / 2 ^ 63) % e = 2 * acc + x / 2 ^ 63 - e := by
        rw [Nat.mod_eq_sub_mod (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
      rw [hm]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith
    · have hyl : (2 * acc % 2 ^ 64 + x / 2 ^ 63) % 2 ^ 64 = 2 * acc + x / 2 ^ 63 := by omega_arith
      rw [hyl]
      by_cases hl : 2 * acc + x / 2 ^ 63 < e
      · rw [ite_eq_right (by omega_arith), Nat.mod_eq_of_lt hl]
        exact congrArg _ (by omega_arith)
      · rw [ite_eq_left (Or.inl hl)]
        have hm : (2 * acc + x / 2 ^ 63) % e = 2 * acc + x / 2 ^ 63 - e := by
          rw [Nat.mod_eq_sub_mod (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
        rw [hm]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega_arith
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hx]
    omega_arith

end VG.Proof.RsaKeyGen.RISCV64.Cand
