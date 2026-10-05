import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Proof.RsaKeyGen.Gcd
import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

theorem xor_cancel_l (a b : BitVec 64) : a ^^^ (b ^^^ a) = b := by
  rw [BitVec.xor_comm b a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem not_sub_allOnes (d : BitVec 64) : (d ^^^ BitVec.allOnes 64) - BitVec.allOnes 64 = -d := by
  rw [BitVec.xor_allOnes, BitVec.neg_eq_not_add, BitVec.sub_eq_add_neg]
  congr 1

theorem xor_z (x : BitVec 64) : x ^^^ 0 = x := by simp
theorem z_xor (x : BitVec 64) : 0 ^^^ x = x := by simp
theorem and_z (x : BitVec 64) : x &&& 0 = 0 := by simp
theorem sub_z (x : BitVec 64) : x - 0 = x := by simp

theorem z_or (x : BitVec 64) : 0 ||| x = x := by simp

theorem shr1_toNat (x : BitVec 64) : (x >>> 1).toNat = x.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem gstep_bv (u v : BitVec 64) :
    let lt := 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (u.toNat < v.toNat)))
    let od := mask (decide (u.toNat % 2 = 1))
    (((u ^^^ ((u - v ^^^ lt) - lt ^^^ u) &&& od) >>> 1).toNat = (gcdStep u.toNat v.toNat).1 ∧
      (v ^^^ ((u ^^^ v) &&& lt ^^^ v ^^^ v) &&& od).toNat = (gcdStep u.toNat v.toNat).2) := by
  intro lt od
  have hlt : lt = mask (decide (u.toNat < v.toNat)) := rfl
  rw [hlt]
  unfold gcdStep
  by_cases ho : u.toNat % 2 = 1 <;> by_cases hl : u.toNat < v.toNat <;>
    simp only [od, ho, hl, decide_true, decide_false, mask_true, mask_false, ↓reduceIte, BitVec.and_allOnes,
      BitVec.xor_zero, xor_cancel_l, not_sub_allOnes, shr1_toNat, xor_z, z_xor,
      and_z, sub_z, BitVec.xor_self]
  · refine ⟨?_, ?_⟩
    · rw [BitVec.neg_sub, BitVec.add_comm, ← BitVec.sub_eq_add_neg,
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
    · rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · exact ⟨by rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)], trivial⟩
  · exact ⟨trivial, trivial⟩
  · exact ⟨trivial, trivial⟩

theorem sx_m1 : BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = BitVec.allOnes 64 := by decide

theorem cf_toNat (x : Nat) : (BitVec.setWidth 64 (BitVec.ofBool (decide (2 ^ 64 ≤ x)))).toNat =
    (decide (2 ^ 64 ≤ x)).toNat := by
  cases decide (2 ^ 64 ≤ x) <;> rfl

/-- One bit of `(c − 1) mod e`: `r := (2 r + bit) mod e`, the bit the top of
`d`, for `r < e`. -/
theorem modbit_bv (r e d : BitVec 64) (hre : r.toNat < e.toNat) :
    let b := BitVec.setWidth 64 (BitVec.ofBool (decide (2 ^ 64 ≤ d.toNat + d.toNat)))
    let r' := r + r + b
    (r' ^^^ (r' - e ^^^ r') &&&
        (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (2 ^ 64 ≤ r.toNat + r.toNat +
            (decide (2 ^ 64 ≤ d.toNat + d.toNat)).toNat))) |||
          0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (r'.toNat < e.toNat))) ^^^
            BitVec.signExtend 64 (BitVec.ofInt 32 (-1)))).toNat =
      (2 * r.toNat + (decide (2 ^ 64 ≤ d.toNat + d.toNat)).toNat) % e.toNat := by
  intro b r'
  have hb : b.toNat = (decide (2 ^ 64 ≤ d.toNat + d.toNat)).toNat := cf_toNat _
  have hbl : (decide (2 ^ 64 ≤ d.toNat + d.toNat)).toNat ≤ 1 := by cases decide (2 ^ 64 ≤ d.toNat + d.toNat) <;> decide
  generalize (decide (2 ^ 64 ≤ d.toNat + d.toNat)).toNat = bit at hb hbl ⊢
  have hr' : r'.toNat = (r.toNat + r.toNat + bit) % 2 ^ 64 := by
    simp only [r', BitVec.toNat_add, hb]; omega
  have he := e.isLt
  have hrl := r.isLt
  rw [sx_m1]
  have hsub : e.toNat ≤ 2 * r.toNat + bit → (2 * r.toNat + bit) % e.toNat = 2 * r.toNat + bit - e.toNat :=
    fun h => by rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  have hlt : 2 * r.toNat + bit < e.toNat → (2 * r.toNat + bit) % e.toNat = 2 * r.toNat + bit :=
    Nat.mod_eq_of_lt
  by_cases hc : 2 ^ 64 ≤ r.toNat + r.toNat + bit
  · simp only [hc, decide_true]
    rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool true)) = BitVec.allOnes 64 from rfl, BitVec.allOnes_or,
      BitVec.and_allOnes, xor_cancel_l, BitVec.toNat_sub, hr', hsub (by omega)]
    omega
  · simp only [hc, decide_false]
    rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool false)) = 0 from rfl, z_or]
    by_cases hl : r'.toNat < e.toNat
    · simp only [hl, decide_true]
      rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool true)) = BitVec.allOnes 64 from rfl, BitVec.xor_self,
        BitVec.and_zero, BitVec.xor_zero, hr']
      rw [hr'] at hl
      rw [hlt (by omega)]
      omega
    · simp only [hl, decide_false]
      rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool false)) = 0 from rfl, z_xor, BitVec.and_allOnes,
        xor_cancel_l, BitVec.toNat_sub, hr']
      rw [hr'] at hl
      rw [hsub (by omega)]
      omega

theorem and1_toNat (u : BitVec 64) : (u &&& 1).toNat = u.toNat % 2 := by
  rw [BitVec.toNat_and]; simp [Nat.and_one_is_mod]

theorem odd_mask (u : BitVec 64) :
    BitVec.setWidth 64 (0 : BitVec 32) - (u &&& 1) = mask (decide (u.toNat % 2 = 1)) := by
  apply BitVec.eq_of_toNat_eq
  have := and1_toNat u
  by_cases h : u.toNat % 2 = 1
  · simp only [h, decide_true, mask_true]
    rw [BitVec.toNat_sub, this, h]; rfl
  · simp only [h, decide_false, mask_false]
    rw [BitVec.toNat_sub, this, show u.toNat % 2 = 0 by omega]; rfl

/-- The gcd's step and count, from `u = rsi`, `v = rbx`. -/
theorem gcdBody_ok (s : State) :
    WP isa (.block (Impl.RsaKeyGen.X86_64.Candidate.bgcdStep ++ ([.alu .sub .r13 (.imm 1)] : List Instr))) s fun t =>
      (t.gpr .rsi).toNat = (gcdStep (s.gpr .rsi).toNat (s.gpr .rbx).toNat).1 ∧
      (t.gpr .rbx).toNat = (gcdStep (s.gpr .rsi).toNat (s.gpr .rbx).toNat).2 ∧
      t.gpr .r13 = s.gpr .r13 - 1 ∧ t.zf = some (s.gpr .r13 - 1 == 0) ∧ t.mem = s.mem ∧
      Keep [.rax, .rcx, .rdx, .rbp, .rsi, .rbx, .r13] s t := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .rbp, .rsi, .rbx, .r13] (Q := fun t =>
    (t.gpr .rsi).toNat = (gcdStep (s.gpr .rsi).toNat (s.gpr .rbx).toNat).1 ∧
      (t.gpr .rbx).toNat = (gcdStep (s.gpr .rsi).toNat (s.gpr .rbx).toNat).2 ∧
      t.gpr .r13 = s.gpr .r13 - 1 ∧ t.zf = some (s.gpr .r13 - 1 == 0) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  unfold Impl.RsaKeyGen.X86_64.Candidate.bgcdStep
  xrun [sx1, odd_mask, List.cons_append, List.nil_append]
  have h := gstep_bv (s.gpr .rsi) (s.gpr .rbx)
  simp only at h
  exact ⟨h.1, h.2⟩

/-- The gcd's 128 steps, from `u = rsi` and the odd `v = rbx`: `gcd u v`
in `rbx`. -/
theorem gcdLoop_ok {s : State} (h13 : s.gpr .r13 = BitVec.ofNat 64 128) (hv : (s.gpr .rbx).toNat % 2 = 1) :
    WP isa (.loop (.block (Impl.RsaKeyGen.X86_64.Candidate.bgcdStep ++ ([.alu .sub .r13 (.imm 1)] : List Instr))) .ne) s fun t =>
      (t.gpr .rbx).toNat = Nat.gcd (s.gpr .rsi).toNat (s.gpr .rbx).toNat ∧ t.mem = s.mem ∧
      Keep [.rax, .rcx, .rdx, .rbp, .rsi, .rbx, .r13] s t := by
  refine wp_countdown (cnt := .r13) (N := 128) (by decide) (by decide)
    (fun i t => (t.gpr .rsi).toNat = (gcdIter i (s.gpr .rsi).toNat (s.gpr .rbx).toNat).1 ∧
      (t.gpr .rbx).toNat = (gcdIter i (s.gpr .rsi).toNat (s.gpr .rbx).toNat).2 ∧ t.mem = s.mem ∧
      Keep [.rax, .rcx, .rdx, .rbp, .rsi, .rbx, .r13] s t) ?_ ?_ ⟨rfl, rfl, rfl, Keep.refl _ _⟩ h13
  · intro i _ t ⟨hu, hv', hm, k⟩ _
    refine WP.mono (gcdBody_ok t) fun t' ⟨h1, h2, h3, h4, h5, k'⟩ => ⟨⟨?_, ?_, h5.trans hm, (k.trans k').mono ?_⟩,
      h3, h4⟩
    · rw [h1, hu, hv', gcdIter_succ']
    · rw [h2, hu, hv', gcdIter_succ']
    · decide
  · intro t ⟨hu, hv', hm, k⟩
    have hlt : (s.gpr .rsi).toNat * (s.gpr .rbx).toNat < 2 ^ 128 := by
      have := (s.gpr .rsi).isLt; have := (s.gpr .rbx).isLt
      calc (s.gpr .rsi).toNat * (s.gpr .rbx).toNat < 2 ^ 64 * 2 ^ 64 :=
            Nat.mul_lt_mul_of_lt_of_lt (by assumption) (by assumption)
        _ = 2 ^ 128 := by rw [← Nat.pow_add]
    rw [gcdIter_eq 128 _ _ hv hlt] at hv'
    exact ⟨hv', hm, k⟩

end VG.Proof.RsaKeyGen.X86_64
