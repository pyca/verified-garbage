import VerifiedGarbage.Proof.X25519.X86.Arith

/-!
# Full-width squaring columns for x86 P-256 Montgomery arithmetic

Reuse the existing x86 Comba kernel, without X25519's modular folding.
The input lies above the sixteen output words in the Montgomery workspace.
-/

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.Impl.X25519.X86 VG.Proof.X25519.X86

theorem square_col_bound (s : State) (x : BitVec 32) (a k : Nat) (hk : k < 16) :
    colv s.mem x (sqrTerms a k) < 2 ^ 68 := by
  have hl : (sqrTerms a k).length ≤ 5 := by
    simp only [sqrTerms, List.length_append, List.length_map]
    have := (by decide : ∀ k < 16, ((List.range 8).filter fun i => 2 * i < k && k - i < 8).length ≤ 4) k hk
    split <;> simp only [List.length_cons, List.length_nil] <;> omega_using [this]
  have h1 := colv_le_len (m := s.mem) (x := x) (B := 2 ^ 65) (ts := sqrTerms a k) fun t ht => by
    simp only [sqrTerms, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨i, -, rfl⟩ | ht
    · have := wv_mul_le s.mem x (a + 4 * i) (a + 4 * (k - i))
      simp only [tval]; omega_using [this]
    · split at ht
      · simp only [List.mem_singleton] at ht
        subst ht
        have := wv_mul_le s.mem x (a + 4 * (k / 2)) (a + 4 * (k / 2))
        simp only [tval]; omega_using [this]
      · exact absurd ht List.not_mem_nil
  have h2 := Nat.mul_le_mul_right (2 ^ 65) hl
  omega_using [h1, h2]

theorem square_col_sum (s : State) (x : BitVec 32) (a : Nat) :
    num (fun k => colv s.mem x (sqrTerms a k)) 16 = fe s.mem x a * fe s.mem x a := by
  have hcol : ∀ k, colv s.mem x (sqrTerms a k) = ((((List.range 8).filter fun i => 2 * i < k && k - i < 8).map
      fun i => 2 * (wv s.mem x (a + 4 * i) * wv s.mem x (a + 4 * (k - i)))) ++
      if k % 2 == 0 && k < 16 then [wv s.mem x (a + 4 * (k / 2)) * wv s.mem x (a + 4 * (k / 2))]
      else []).sum := fun k => by
    unfold colv sqrTerms
    rw [List.map_append, List.map_map]
    split <;> rfl
  simp only [hcol]
  exact sqr_identity (fun i => wv s.mem x (a + 4 * i))

/-- Full 512-bit square, with no carry beyond the output. -/
theorem square_columns_ok {W : Nat} {c : Bool} {x : BitVec 32} {s : State}
    (hc : Ctx W x s c) {o a : Nat} (ha : a + 32 ≤ 4096) (hoa : o + 64 ≤ a) :
    WP isa (.block (zeroAcc ++ cols o 16 (sqrTerms a))) s fun u =>
      Keep s u ∧ Frame [sub x o 64] s.mem u.mem ∧
      num (fun k => wv u.mem x (o + 4 * k)) 16 = fe s.mem x a * fe s.mem x a ∧ acc u = 0 := by
  refine WP.block_append (WP.mono zeroAcc_ok fun t ⟨K, M, Z⟩ => ?_)
  refine WP.mono (cols_ok (K.ctx hc) (sqrTerms a) 16 (by omega) ?_
    (fun k hk => square_col_bound t x a k hk) (by rw [Z]; decide)) fun u ⟨K', F, E, _⟩ => ?_
  · intro k hk term ht d hd
    simp only [sqrTerms, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq] at ht
    rcases ht with ⟨i, ⟨hi, -, hki⟩, rfl⟩ | ht
    · simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> constructor <;> omega
    · split at ht
      · simp only [List.mem_singleton] at ht
        subst term
        simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;> constructor <;> omega
      · exact absurd ht List.not_mem_nil
  · rw [Z, Nat.zero_add, square_col_sum, M] at E
    have hA := fe_lt s.mem x a
    have hAA := Nat.mul_lt_mul_of_lt_of_lt hA hA
    have hpow : (2 ^ 32 : Nat) ^ 16 = 2 ^ 256 * 2 ^ 256 := by decide
    rw [hpow] at E
    have hz : acc u = 0 := by omega
    refine ⟨K.trans K', ?_, ?_, hz⟩
    · simpa only [M] using F
    · simpa only [hz, Nat.mul_zero, Nat.add_zero] using E

end VG.Proof.Weierstrass.X86.Mont
