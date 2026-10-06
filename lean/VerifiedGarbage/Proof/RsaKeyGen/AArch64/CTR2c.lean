import VerifiedGarbage.Proof.Bignum.AArch64.CTR2

/-!
# A candidate on AArch64: constant time of `R² mod c`

`r2_ct` (`Proof/Bignum/AArch64/CTR2.lean`) relates runs with the same
modulus; a candidate `c` is secret, but its top bit is set, so `topBit`
runs 63 iterations and the doublings `w + 1` whatever `c` (`r2c_ct`). The
runs agree on the working space alone (`Ws`), `-c⁻¹` and `c` differing.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)

/-- The layout of the working space `L` with `-m⁻¹ = mi`. -/
abbrev lay (L : Ws) (mi : BitVec 64) : Lay := ⟨L.B, L.Z, L.w, mi⟩

/-- `Φ` fixes the registers `rs` to values of the public data. -/
theorem pins_of {α : Type} {Φ : α → State → Prop} (rs : List Reg) (f : α → Reg → BitVec 64)
    (h : ∀ a s, Φ a s → ∀ r ∈ rs, s.gpr r = f a r) : Pins Φ rs :=
  fun a _ _ h₁ h₂ r hr => (h a _ h₁ r hr).trans (h a _ h₂ r hr).symm

theorem pins_nil' {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

/-! ## The top bit -/

theorem top_div_two {T j : Nat} (hT : 2 ^ 63 ≤ T) (hT1 : T < 2 ^ 64) (hj : j < 63) :
    T / 2 ^ (j + 1) = 1 ↔ j + 1 = 63 := by
  constructor
  · intro h
    by_contra hne
    have h2 : 2 * 2 ^ (j + 1) ≤ T := by
      have : 2 ^ (j + 2) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.pow_succ] at this; omega
    have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos (j + 1))).mpr h2
    omega
  · intro h
    rw [h]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- One halving of `topBit`'s loop, from `T / 2^j` with `2^63 ≤ T`. -/
theorem topStep_ok {s : State} {T j : Nat} (hT : 2 ^ 63 ≤ T) (hT1 : T < 2 ^ 64) (hj : j < 63)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 (T / 2 ^ j)) :
    WP isa (.block [.lsr .x .x3 .x3 1, .add .x .x9 .x9 .x9, .subImm .x .x13 .x13 1, .subImm .x .x6 .x3 1]) s
      fun t => t.gpr .x3 = BitVec.ofNat 64 (T / 2 ^ (j + 1)) ∧
        isa.eval (.nonzero .x .x6) t = some (decide (j + 1 < 63)) := by
  have hTj : T / 2 ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hT1
  have hTj1 : 0 < T / 2 ^ (j + 1) := Nat.div_pos (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hT)
    (Nat.two_pow_pos _)
  have hlt : T / 2 ^ (j + 1) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hT1
  refine WP.mono (Q := fun (t : State) => t.gpr .x3 = BitVec.ofNat 64 (T / 2 ^ (j + 1)) ∧
      t.gpr .x6 = BitVec.ofNat 64 (T / 2 ^ (j + 1)) - BitVec.ofNat 64 1) (by
    brun [h3, shr1_ofNat _ hTj, div_pow_succ]) fun t ⟨h3', h6⟩ => ⟨h3', ?_⟩
  rw [eval_nonzero, h6]
  have e := ofNat_sub1_eq_zero hlt hTj1
  refine congrArg some ?_
  rw [bne, e]
  have k := top_div_two hT hT1 hj
  by_cases h : j + 1 = 63
  · rw [decide_eq_true (k.mpr h), decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false (fun e => h (k.mp e)), decide_eq_true (by omega)]; rfl

/-- `topBit` from `x3 = T` with `2^63 ≤ T`: its loop runs 63 iterations,
whatever `T`. -/
theorem topBit_ct {α : Type} {Φ : α → State → Prop}
    (hT : ∀ a s, Φ a s → ∃ T, 2 ^ 63 ≤ T ∧ T < 2 ^ 64 ∧ s.gpr .x3 = BitVec.ofNat 64 T) :
    RelCT isa (Two Φ) topBit fun _ _ => True := by
  unfold topBit
  refine RelCT.seq (two_piece (Ψ := fun _ s => ∃ T, 2 ^ 63 ≤ T ∧ T < 2 ^ 64 ∧
      s.gpr .x3 = BitVec.ofNat 64 (T / 2 ^ 0) ∧ isa.eval (.zero .x .x6) s = some false) [] (pins_nil' _)
      (by taint_decide) fun a s h => ?_) ?_
  · obtain ⟨T, hT0, hT1, h3⟩ := hT a s h
    refine WP.mono (Q := fun (t : State) => t.gpr .x3 = BitVec.ofNat 64 T ∧
        t.gpr .x6 = BitVec.ofNat 64 T - BitVec.ofNat 64 1) (by brun [h3]) fun t ⟨h3', h6⟩ =>
      ⟨T, hT0, hT1, by rw [h3', Nat.pow_zero, Nat.div_one], ?_⟩
    rw [eval_zero, h6, ofNat_sub1_eq_zero hT1 (by omega), decide_eq_false (by omega)]
  refine two_ite (fun _ _ _ h₁ h₂ => by
      obtain ⟨_, _, _, _, e₁⟩ := h₁
      obtain ⟨_, _, _, _, e₂⟩ := h₂
      rw [e₁, e₂])
    (RelCT.of_false fun _ _ ⟨_, ⟨⟨_, _, _, _, e⟩, et⟩, _, _⟩ => by rw [e] at et; cases et) ?_
  refine (two_loop (Φ := fun _ j s => ∃ T, 2 ^ 63 ≤ T ∧ T < 2 ^ 64 ∧ s.gpr .x3 = BitVec.ofNat 64 (T / 2 ^ j))
    (Ψ := fun _ _ => True) (fun _ => 63) (two_taint [] (pins_nil' _) (by taint_decide)) ?_).mono
    (fun _ _ ⟨a, ⟨⟨T, hT0, hT1, h3, _⟩, _⟩, ⟨⟨T', hT0', hT1', h3', _⟩, _⟩, hsp⟩ =>
      ⟨a, ⟨by decide, T, hT0, hT1, h3⟩, ⟨by decide, T', hT0', hT1', h3'⟩, hsp⟩) fun _ _ _ => trivial
  rintro a j s hj ⟨T, hT0, hT1, h3⟩
  exact WP.mono (topStep_ok hT0 hT1 hj h3) fun t ⟨h3', he⟩ => ⟨he, fun _ => ⟨T, hT0, hT1, h3'⟩, fun _ => trivial⟩

end VG.Proof.RsaKeyGen.AArch64
