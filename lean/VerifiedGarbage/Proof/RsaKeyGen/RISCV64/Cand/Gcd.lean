module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Fin
public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Candidate
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.RsaKeyGen.Gcd
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on RISC-V: `gcd(c − 1, e)`'s steps

`modBit_ok`: one bit of `(c − 1) mod e`, `a1 := (2 a1 + x₆₃) mod e` for
`a1 < e` (in `s10`), `a2 := 2 x`, and `modBits_ok` the 64 bits of a word;
`gcdStep_ok`: one step of the binary gcd on `u = a1` and the odd `v = s10`,
as `Proof.RsaKeyGen.gcdStep`, and `gcdLoop_ok` its 128 steps. A flag
`f ∈ {0, 1}` from `sltu` or a low bit becomes the mask `0 − f`, which selects
between two words by `y ^ ((x ^ y) & mask)` (`sel_mask`). `loadE_ok`: `e`'s
`e_len` octets, most significant first, from the frame's `oE` and `oELen`
into `s10`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64

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

/-! ## The loops -/

theorem gcdStep_lt {u v : Nat} (hu : u < 2 ^ 64) (hv : v < 2 ^ 64) :
    (VG.Proof.RsaKeyGen.gcdStep u v).1 < 2 ^ 64 ∧ (VG.Proof.RsaKeyGen.gcdStep u v).2 < 2 ^ 64 := by
  unfold VG.Proof.RsaKeyGen.gcdStep
  split
  · split <;> exact ⟨by omega_arith, by omega_arith⟩
  · exact ⟨by omega_arith, hv⟩

theorem gcdIter_lt : ∀ n {u v : Nat}, u < 2 ^ 64 → v < 2 ^ 64 → v % 2 = 1 →
    (VG.Proof.RsaKeyGen.gcdIter n u v).1 < 2 ^ 64 ∧ (VG.Proof.RsaKeyGen.gcdIter n u v).2 < 2 ^ 64 ∧
      (VG.Proof.RsaKeyGen.gcdIter n u v).2 % 2 = 1
  | 0, _, _, hu, hv, ho => ⟨hu, hv, ho⟩
  | n + 1, u, v, hu, hv, ho => by
    rw [VG.Proof.RsaKeyGen.gcdIter]
    exact gcdIter_lt n (gcdStep_lt hu hv).1 (gcdStep_lt hu hv).2 (VG.Proof.RsaKeyGen.gcdStep_odd ho)

/-- The registers the gcd's steps write. -/
def gsRegs : List Reg := [.t2, .t5, .a1, .a2, .a3, .a4, .a5, .s10]

/-- The counter's decrement. -/
theorem dec_ok (s : State) :
    WP isa (.block [.addi .t5 .t5 (-1)]) s fun t =>
      (t.gpr .t5 = s.gpr .t5 - BitVec.ofNat 64 1 ∧ t.mem = s.mem) ∧ Keep [.t5] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [gpr_write_self]

/-- 128 steps of the binary gcd from `u = a1` and the odd `v = s10`, counted
in `t5`. -/
theorem gcdLoop_ok {s : State} {u v : Nat} (h1 : s.gpr .a1 = BitVec.ofNat 64 u)
    (h10 : s.gpr .s10 = BitVec.ofNat 64 v) (h5 : s.gpr .t5 = BitVec.ofNat 64 128) (hu : u < 2 ^ 64)
    (hv : v < 2 ^ 64) (ho : v % 2 = 1) :
    WP isa (VG.Impl.Bignum.RISCV64.countLoop .t5 VG.Impl.RsaKeyGen.RISCV64.Candidate.gcdStep) s fun t =>
      t.gpr .s10 = BitVec.ofNat 64 (Nat.gcd u v) ∧ t.mem = s.mem ∧ Keep gsRegs s t := by
  refine WP.mono (wp_countdown (cnt := .t5) (N := 128) (by decide) (by decide)
    (fun i t => t.gpr .a1 = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.gcdIter i u v).1 ∧
      t.gpr .s10 = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.gcdIter i u v).2 ∧ t.mem = s.mem ∧ Keep gsRegs s t)
    ?_ ⟨h1, h10, rfl, Keep.refl _ _⟩ h5) fun t ⟨_, t10, tm, tk⟩ => ⟨?_, tm, tk⟩
  · intro i _ t ⟨t1, t10, tm, tk⟩ _
    obtain ⟨b1, b2, -⟩ := gcdIter_lt i hu hv ho
    refine WP.block_append_iff.mpr (WP.mono (gcdStep_ok t1 t10 b1 b2) fun t₁ ⟨⟨a1, a10, m₁⟩, k₁⟩ => ?_)
    refine WP.mono (dec_ok t₁) fun t' ⟨⟨h5', m'⟩, k'⟩ => ⟨⟨?_, ?_, by rw [m', m₁, tm], ?_⟩, ?_⟩
    · rw [k'.gpr (by decide), a1, VG.Proof.RsaKeyGen.gcdIter_succ']
    · rw [k'.gpr (by decide), a10, VG.Proof.RsaKeyGen.gcdIter_succ']
    · exact Keep.trans' (Keep.trans' tk (k₁.mono (by decide))) (k'.mono (by decide))
    · rw [h5', k₁.gpr (by decide)]
  · rw [t10, VG.Proof.RsaKeyGen.gcdIter_eq 128 u v ho (by
      have : u * v < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul_of_lt_of_lt hu hv
      rw [← Nat.pow_add] at this; exact this)]

theorem self_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

/-- A word shifted left `i` bits, `y = (x mod 2^(k + 1)) 2^i` for `k + i = 63`:
its top bit, and itself doubled modulo `2^64`. -/
theorem shift1 (x k i : Nat) (hki : k + i = 63) :
    (x % 2 ^ (k + 1)) * 2 ^ i / 2 ^ 63 = x / 2 ^ k % 2 ∧
    2 * ((x % 2 ^ (k + 1)) * 2 ^ i) % 2 ^ 64 = (x % 2 ^ k) * 2 ^ (i + 1) := by
  obtain ⟨hy, hb, hsh, -⟩ := VG.Proof.RsaKeyGen.shift_step x k i hki
  generalize (x % 2 ^ (k + 1)) * 2 ^ i = y at hy hb hsh ⊢
  refine ⟨?_, by rw [← hsh]; congr 1; omega_arith⟩
  rw [← hb]
  by_cases h : 2 ^ 64 ≤ y + y
  · rw [decide_eq_true h]; simp only [Bool.toNat_true]; omega_arith
  · rw [decide_eq_false h]; simp only [Bool.toNat_false]; omega_arith

/-- The registers the bits' loop writes. -/
def mbRegs : List Reg := [.t5, .a1, .a2, .a3, .a4, .a5]

/-- The 64 bits of the word `x` in `a2` into `r = a1 < e` (`s10`), counted in
`t5`: `(r 2^64 + x) mod e`. -/
theorem modBits_ok {s : State} (h5 : s.gpr .t5 = BitVec.ofNat 64 64)
    (hre : (s.gpr .a1).toNat < (s.gpr .s10).toNat) :
    WP isa (VG.Impl.Bignum.RISCV64.countLoop .t5 VG.Impl.RsaKeyGen.RISCV64.Candidate.modBit) s fun t =>
      (t.gpr .a1).toNat = ((s.gpr .a1).toNat * 2 ^ 64 + (s.gpr .a2).toNat) % (s.gpr .s10).toNat ∧
      t.mem = s.mem ∧ Keep mbRegs s t := by
  have he0 : 0 < (s.gpr .s10).toNat := by omega_arith
  have hX := (s.gpr .a2).isLt
  have hE := (s.gpr .s10).isLt
  refine WP.mono (wp_countdown (cnt := .t5) (N := 64) (by decide) (by decide)
    (fun i t => (t.gpr .a1).toNat = ((s.gpr .a1).toNat * 2 ^ i + (s.gpr .a2).toNat / 2 ^ (64 - i)) %
        (s.gpr .s10).toNat ∧
      (t.gpr .a2).toNat = ((s.gpr .a2).toNat % 2 ^ (64 - i)) * 2 ^ i ∧ t.mem = s.mem ∧
      Keep mbRegs s t) ?_ ⟨?_, ?_, rfl, Keep.refl _ _⟩ h5) fun t ⟨hr, _, hm, k⟩ => ?_
  · intro i hi t ⟨hr, hd, hm, k⟩ _
    have h10 : t.gpr .s10 = s.gpr .s10 := k.gpr (by decide)
    have hacc : (t.gpr .a1).toNat < (t.gpr .s10).toNat := by rw [h10, hr]; exact Nat.mod_lt _ he0
    refine WP.block_append_iff.mpr (WP.mono (modBit_ok (acc := (t.gpr .a1).toNat) (x := (t.gpr .a2).toNat)
      (e := (t.gpr .s10).toNat) (self_ofNat _) (self_ofNat _) (self_ofNat _) hacc (t.gpr .s10).isLt
      (t.gpr .a2).isLt) fun t₁ ⟨⟨h1, h2, m₁⟩, k₁⟩ => ?_)
    refine WP.mono (dec_ok t₁) fun t' ⟨⟨h5', m'⟩, k'⟩ => ⟨⟨?_, ?_, by rw [m', m₁, hm], ?_⟩, ?_⟩
    · obtain ⟨_, _, _, hdiv⟩ := VG.Proof.RsaKeyGen.shift_step (s.gpr .a2).toNat (63 - i) i (by omega_arith)
      obtain ⟨hbit, _⟩ := shift1 (s.gpr .a2).toNat (63 - i) i (by omega_arith)
      rw [show 63 - i + 1 = 64 - i by omega_arith] at hbit hdiv
      rw [k'.gpr (by decide), h1, h10, BitVec.toNat_ofNat, hd, hbit, hr,
        show 64 - (i + 1) = 63 - i by omega_arith, Nat.pow_succ,
        Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ he0) hE)]
      conv => rhs; rw [← hdiv]
      have hm2 : ∀ V b E : Nat, (2 * (V % E) + b) % E = (2 * V + b) % E := fun V b E => by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
      rw [hm2]
      congr 1
      have hb2 : (s.gpr .a2).toNat / 2 ^ (63 - i) % 2 < 2 := Nat.mod_lt _ (by decide)
      generalize (s.gpr .a1).toNat = R
      generalize (s.gpr .a2).toNat / 2 ^ (64 - i) = Q
      generalize (s.gpr .a2).toNat / 2 ^ (63 - i) % 2 = b at hb2 ⊢
      rw [Nat.pow_succ, Nat.mul_add, Nat.mul_comm 2 (R * 2 ^ i), Nat.mul_assoc, Nat.mul_comm 2 Q]
      omega_arith
    · obtain ⟨_, hsh⟩ := shift1 (s.gpr .a2).toNat (63 - i) i (by omega_arith)
      rw [show 63 - i + 1 = 64 - i by omega_arith] at hsh
      rw [k'.gpr (by decide), h2, BitVec.toNat_ofNat, hd, show 64 - (i + 1) = 63 - i by omega_arith, hsh]
      exact Nat.mod_eq_of_lt (by rw [← hsh]; exact Nat.mod_lt _ (by decide))
    · exact Keep.trans' (Keep.trans' k (k₁.mono (by decide))) (k'.mono (by decide))
    · rw [h5', k₁.gpr (by decide)]
  · rw [Nat.pow_zero, Nat.mul_one, Nat.div_eq_of_lt hX, Nat.add_zero, Nat.mod_eq_of_lt hre]
  · rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hX]
  · refine ⟨?_, hm, k⟩
    rw [hr, Nat.sub_self, Nat.pow_zero, Nat.div_one]

open VG.Proof.Mont (off)
open VG.Impl.RsaKeyGen.RISCV64.Candidate (loadE ldf oE oELen)

/-- `e`'s value. -/
abbrev eV (s0 : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a3) (s0.gpr .a4).toNat)

theorem os2ip_bytes_lt (m : Mem) (E : Addr) : ∀ i, Spec.Rsa.os2ip (Spec.Rsa.bytesAt m E i) < 256 ^ i
  | 0 => by simp [Spec.Rsa.bytesAt, Spec.Rsa.os2ip]
  | i + 1 => by
    rw [Pub.bytesAt_succ, VG.Proof.Rsa.os2ip_snoc, Nat.pow_succ]
    have := os2ip_bytes_lt m E i
    have := (m (off E i)).isLt
    omega_arith

theorem eV_lt {s0 : State} (hp : CIn s0) : eV s0 < 2 ^ 64 := by
  have h1 := os2ip_bytes_lt s0.mem (s0.gpr .a3) (s0.gpr .a4).toNat
  have h8 : (256 : Nat) ^ (s0.gpr .a4).toNat ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) hp.el2
  have h9 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  simp only [eV]
  omega_arith

theorem read_byte (m : Mem) (a : Addr) : (m.read a 1).setWidth 64 = BitVec.ofNat 64 (m a).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, VG.Proof.Mont.read_toNat_succ]
  simp [Mem.read]

/-- `loadE`: `e` into `s10`. -/
theorem loadE_ok {s0 s : State} (h : Fr s0 s) :
    WP isa loadE s fun t =>
      (t.gpr .s10 = BitVec.ofNat 64 (eV s0) ∧ t.mem = s.mem) ∧ Keep [.t2, .t3, .t4, .t5, .s10] s t := by
  have hp := h.pre
  generalize hE : s0.gpr .a3 = E
  generalize hL : (s0.gpr .a4).toNat = L
  have hL1 : 1 ≤ L := hL ▸ hp.el1
  have hL8 : L ≤ 8 := hL ▸ hp.el2
  have eL : s0.gpr .a4 = BitVec.ofNat 64 L := by rw [← hL, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hfe : E.toNat + L ≤ 2 ^ 64 := by rw [← hE, ← hL]; exact hp.fe
  have hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off E i) 1 := fun i hi =>
    ⟨cE s0, List.mem_append_left _ (by rw [h.rd]; exact hp.rE), by
      show (⟨s0.gpr .a3, (s0.gpr .a4).toNat⟩ : Region).Contains _ _
      rw [hE, hL]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hbytes : Spec.Rsa.bytesAt s.mem E L = Spec.Rsa.bytesAt s0.mem E L := by
    refine bytes_keep h.out (by omega_arith) fun ρ hρ => ?_
    have e : (⟨E, L⟩ : Region) = cE s0 := by rw [← hE, ← hL]
    rw [e]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl
    · exact hp.oE.symm
    · exact hp.uE.symm
    · exact hp.eS
    · exact hp.Fe.symm
  have al : ∀ o, o % 8 = 0 → (fb s0 + BitVec.ofNat 64 o).toNat % 8 = 0 := fun o h8 => fw_al hp h8
  have inr : ∀ o, o + 8 ≤ 192 → InRegions (s.rd ++ s.wr) (fb s0 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨kF s0, List.mem_append_right _ (by rw [h.wr]; exact List.mem_cons_self), kF_contains ho⟩
  have r128 : s.mem.readW (fb s0 + BitVec.ofNat 64 128) 64 = E := hE ▸ h.wE
  have r136 : s.mem.readW (fb s0 + BitVec.ofNat 64 136) 64 = BitVec.ofNat 64 L := eL ▸ h.wELen
  unfold loadE
  refine WP.seq ?_
  have hpre : WP isa (.block [.li .t2 0, ldf .t3 oE, ldf .t5 oELen]) s fun s₁ =>
      (s₁.gpr .t2 = 0 ∧ s₁.gpr .t3 = off E 0 ∧ s₁.gpr .t5 = BitVec.ofNat 64 L ∧ s₁.mem = s.mem) ∧
        Keep [.t2, .t3, .t5] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [ldf, oE, oELen, h.s11, al 128 (by decide), al 136 (by decide), inr 128 (by decide),
      inr 136 (by decide), r128, r136, fin64_exec_li_zero]
    exact (BitVec.add_zero _).symm
  refine WP.mono hpre fun s₁ ⟨⟨i2, i3, i5, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t2 = BitVec.ofNat 64 (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E i)) ∧
      t.gpr .t3 = off E i ∧ t.mem = s.mem ∧ Keep [.t2, .t3, .t4, .t5] s t
  refine WP.seq (WP.mono (wp_countdown (cnt := .t5) (N := L) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨t2, t3, tm, tk⟩ _ => ?_)
    ⟨by rw [i2]; rfl, i3, im, k₁.mono (by decide)⟩ i5) fun t ⟨t2, _, tm, tk⟩ => ?_)
  · have hb : InRegions (t.rd ++ t.wr) (off E i) 1 := by rw [tk.2.1, tk.2.2]; exact hrd i hi
    refine WP.mono (WP.keep [.t2, .t3, .t4, .t5] (Q := fun t' =>
      t'.gpr .t2 = BitVec.ofNat 64 (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E (i + 1))) ∧
        t'.gpr .t3 = off E (i + 1) ∧ t'.mem = t.mem ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ?_ (by rfl)
        (by rfl))
      fun t' ⟨⟨a, b, c, d⟩, k⟩ => ⟨⟨a, b, c.trans tm, Keep.trans' tk k⟩, d⟩
    brun [t3, t2, hb, read_byte]
    apply BitVec.eq_of_toNat_eq
    rw [Pub.bytesAt_succ, VG.Proof.Rsa.os2ip_snoc, tm, BitVec.toNat_add,
      BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have hbt := (s.mem (off E i)).isLt
    have hlt := os2ip_bytes_lt s.mem E i
    have h256 : 256 ^ i ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega_arith)
    have : (256 : Nat) ^ 7 = 2 ^ 56 := by decide
    rw [Nat.mod_eq_of_lt (show Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E i) < 2 ^ 64 by omega_arith)]
    omega_arith
  · have hfin : WP isa (.block [.addi .s10 .t2 0]) t fun t' =>
        (t'.gpr .s10 = t.gpr .t2 ∧ t'.mem = t.mem) ∧ Keep [.s10] t t' := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun
      exact BitVec.add_zero _
    refine WP.mono hfin fun t' ⟨⟨a, b⟩, k⟩ => ⟨⟨?_, b.trans tm⟩, Keep.trans' (tk.mono (by decide)) (k.mono (by decide))⟩
    rw [a, t2, hbytes, ← hE, ← hL]

end VG.Proof.RsaKeyGen.RISCV64.Cand
