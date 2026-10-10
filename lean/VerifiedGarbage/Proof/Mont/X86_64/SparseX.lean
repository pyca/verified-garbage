import VerifiedGarbage.Proof.Mont.X86_64.Sparse

/-!
# Montgomery arithmetic on x86-64: P-384's reduction with BMI2

`redSparse` with the multiplier's ports doing the work the flags' ports did:
`u = t₀ (2³² + 1) mod 2⁶⁴` is one `imul` (`uSparseX_ok`), and the two
products of `u` by `c = 2³⁸⁴ - p`'s words are by `mulx`, their halves added in
one carry chain (`prodSparseX_ok`), then subtracted (`subSparseX_ok`):
`redSX_ok` is `redS_ok` for `redSparseX`. `redShortX_ok` is the round on six
words holding `T < 2³⁸⁴`, whose result needs no seventh word.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono se0 add_carry adc_carry sub_borrow sbb_borrow
  toNat_ofBool)

/-- `imul`'s result: the low word of the product, signed or unsigned. -/
theorem imul_toNat (a b : BitVec 64) :
    (BitVec.ofInt 64 (a.toInt * b.toInt)).toNat = a.toNat * b.toNat % 2 ^ 64 := by
  have h : BitVec.ofInt 64 (a.toInt * b.toInt) = a * b := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_ofInt, BitVec.toInt_mul]
  rw [h, BitVec.toNat_mul]

/-- `rdx = t₀ (2³² + 1) mod 2⁶⁴`. -/
theorem uSparseX_ok (s : State) {t0 : Reg} (hd : t0 ≠ .rdx) :
    WP isa (.block (uSparseX t0)) s fun s' =>
      (s'.gpr .rdx).toNat = (s.gpr t0).toNat * (2 ^ 32 + 1) % 2 ^ 64 ∧ Keeps [.rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [uSparseX, runBlock_cons, runStep_some, runBlock_nil, exec, execImul, RegUpd.gpr_setReg, hd,
    ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [imul_toNat, show sparseK.toNat = 2 ^ 32 + 1 from rfl, Nat.mul_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.2, ite_false]

/-- `rax + 2⁶⁴ rcx + 2¹²⁸ rbp` is `⌊u c / 2⁶⁴⌋` for `u` in `rdx` (kept), with
`u c mod 2⁶⁴` below. -/
theorem prodSparseX_ok (s : State) {t0 : Reg} (h0 : t0 ≠ .rax ∧ t0 ≠ .rcx ∧ t0 ≠ .rdx ∧ t0 ≠ .rbp) :
    WP isa (.block (prodSparseX t0)) s fun s' =>
      2 ^ 64 * ((s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rcx).toNat + 2 ^ 128 * (s'.gpr .rbp).toNat) +
          (s.gpr .rdx).toNat * 0xffffffff00000001 % 2 ^ 64 =
        (s.gpr .rdx).toNat * 0xffffffff00000001 + 2 ^ 64 * ((s.gpr .rdx).toNat * 0xffffffff) +
          2 ^ 128 * (s.gpr .rdx).toNat ∧
      Keeps [.rax, .rcx, .rbp, t0] s s' := by
  obtain ⟨ha, hc, hd, hb⟩ := h0
  apply WP.of_runBlock
  simp only [prodSparseX, runBlock_cons, runStep_some, runBlock_nil, exec, execMulx, execAlu, readSrc,
    readSrc32, Option.bind_some, Option.map_some, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ↓reduceIte, hc,
    Ne.symm ha, Ne.symm hd, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · generalize s.gpr .rdx = u
    have hu := u.isLt
    have hc0 : sparseC0.toNat = 0xffffffff00000001 := rfl
    have hc1 : (BitVec.setWidth 64 sparseC1).toNat = 0xffffffff := rfl
    have z : ∀ c : Bool, (BitVec.setWidth 64 (0 : BitVec 32) + BitVec.setWidth 64 (0 : BitVec 32) +
        (BitVec.ofBool c).setWidth 64).toNat = c.toNat := by
      intro c; cases c <;> rfl
    rw [hc0, hc1]
    have l0 : u.toNat * 0xffffffff00000001 / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul (by omega)
    have l1 : u.toNat * 0xffffffff / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul (by omega)
    have e0 : (BitVec.ofNat 64 (u.toNat * 0xffffffff00000001 / 2 ^ 64)).toNat =
        u.toNat * 0xffffffff00000001 / 2 ^ 64 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt l0]
    have e1 : (BitVec.ofNat 64 (u.toNat * 0xffffffff / 2 ^ 64)).toNat = u.toNat * 0xffffffff / 2 ^ 64 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt l1]
    have e2 : (BitVec.ofNat 64 (u.toNat * 0xffffffff)).toNat = u.toNat * 0xffffffff % 2 ^ 64 :=
      BitVec.toNat_ofNat _ _
    have a1 := add_carry (BitVec.ofNat 64 (u.toNat * 0xffffffff00000001 / 2 ^ 64))
      (BitVec.ofNat 64 (u.toNat * 0xffffffff))
    have a2 := adc_carry (BitVec.ofNat 64 (u.toNat * 0xffffffff / 2 ^ 64)) u
      (decide (2 ^ 64 ≤ (BitVec.ofNat 64 (u.toNat * 0xffffffff00000001 / 2 ^ 64)).toNat +
        (BitVec.ofNat 64 (u.toNat * 0xffffffff)).toNat))
    generalize decide (2 ^ 64 ≤ (BitVec.ofNat 64 (u.toNat * 0xffffffff00000001 / 2 ^ 64)).toNat +
      (BitVec.ofNat 64 (u.toNat * 0xffffffff)).toNat) = c₁ at a1 a2 ⊢
    generalize decide (2 ^ 64 ≤ (BitVec.ofNat 64 (u.toNat * 0xffffffff / 2 ^ 64)).toNat + u.toNat +
      c₁.toNat) = c₂ at a2 ⊢
    rw [z]
    rw [e0, e2] at a1
    rw [e1] at a2
    have hc2 := Bool.toNat_le c₂
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- `t₁ … t₇ += 2³²⁰ u - C` for `C = rax + 2⁶⁴ rcx + 2¹²⁸ rbp` and `u` in
`rdx`, if `C` is at most `2⁶⁶ u` and the result is below `2⁴⁴⁸`
(`subSparse_ok`'s registers). -/
theorem subSparseX_ok (s : State) {t1 t2 t3 t4 t5 t6 t7 : Reg}
    (hf : Fresh [t1, t2, t3, t4, t5, t6, t7])
    (hC : (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rcx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat ≤
      2 ^ 66 * (s.gpr .rdx).toNat)
    (hlt : regsVal s [t1, t2, t3, t4, t5, t6, t7] + 2 ^ 320 * (s.gpr .rdx).toNat <
      2 ^ 448 + ((s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rcx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat)) :
    WP isa (.block (subSparseX t1 t2 t3 t4 t5 t6 t7)) s fun s' =>
      regsVal s' [t1, t2, t3, t4, t5, t6, t7] +
          ((s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rcx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat) =
        regsVal s [t1, t2, t3, t4, t5, t6, t7] + 2 ^ 320 * (s.gpr .rdx).toNat ∧
      Keeps [t1, t2, t3, t4, t5, t6, t7, .rdx] s s' := by
  obtain ⟨hnd, hr⟩ := hf
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨⟨n12, n13, n14, n15, n16, n17⟩, ⟨n23, n24, n25, n26, n27⟩,
    ⟨n34, n35, n36, n37⟩, ⟨n45, n46, n47⟩, ⟨n56, n57⟩, n67, -⟩ := hnd
  obtain ⟨⟨a1, c1, d1, b1, -⟩, ⟨a2, c2, d2, b2, -⟩, ⟨a3, c3, d3, b3, -⟩, ⟨a4, c4, d4, b4, -⟩,
    ⟨a5, c5, d5, b5, -⟩, ⟨a6, c6, d6, b6, -⟩, ⟨a7, c7, d7, b7, -⟩⟩ := hr
  have m12 := Ne.symm n12
  have m13 := Ne.symm n13
  have m14 := Ne.symm n14
  have m15 := Ne.symm n15
  have m16 := Ne.symm n16
  have m17 := Ne.symm n17
  have m23 := Ne.symm n23
  have m24 := Ne.symm n24
  have m25 := Ne.symm n25
  have m26 := Ne.symm n26
  have m27 := Ne.symm n27
  have m34 := Ne.symm n34
  have m35 := Ne.symm n35
  have m36 := Ne.symm n36
  have m37 := Ne.symm n37
  have m45 := Ne.symm n45
  have m46 := Ne.symm n46
  have m47 := Ne.symm n47
  have m56 := Ne.symm n56
  have m57 := Ne.symm n57
  have m67 := Ne.symm n67
  have a1' := Ne.symm a1
  have c1' := Ne.symm c1
  have d1' := Ne.symm d1
  have b1' := Ne.symm b1
  have a2' := Ne.symm a2
  have c2' := Ne.symm c2
  have d2' := Ne.symm d2
  have b2' := Ne.symm b2
  have a3' := Ne.symm a3
  have c3' := Ne.symm c3
  have d3' := Ne.symm d3
  have b3' := Ne.symm b3
  have a4' := Ne.symm a4
  have c4' := Ne.symm c4
  have d4' := Ne.symm d4
  have b4' := Ne.symm b4
  have a5' := Ne.symm a5
  have c5' := Ne.symm c5
  have d5' := Ne.symm d5
  have b5' := Ne.symm b5
  have a6' := Ne.symm a6
  have c6' := Ne.symm c6
  have d6' := Ne.symm d6
  have b6' := Ne.symm b6
  have a7' := Ne.symm a7
  have c7' := Ne.symm c7
  have d7' := Ne.symm d7
  have b7' := Ne.symm b7
  simp only [regsVal] at hlt ⊢
  apply WP.of_runBlock
  simp only [subSparseX, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    ↓reduceIte, se0, Option.some.injEq, exists_eq_left', *]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · generalize s.gpr t1 = x1 at *
    generalize s.gpr t2 = x2 at *
    generalize s.gpr t3 = x3 at *
    generalize s.gpr t4 = x4 at *
    generalize s.gpr t5 = x5 at *
    generalize s.gpr t6 = x6 at *
    generalize s.gpr t7 = x7 at *
    generalize s.gpr .rbp = y at *
    generalize s.gpr .rax = r at *
    generalize s.gpr .rcx = d at *
    generalize s.gpr .rdx = u at *
    have e1 := sub_borrow x1 r
    generalize decide (x1.toNat < r.toNat) = β1 at e1 ⊢
    have e2 := sbb_borrow x2 d β1
    generalize decide (x2.toNat < d.toNat + β1.toNat) = β2 at e2 ⊢
    have e3 := sbb_borrow x3 y β2
    generalize decide (x3.toNat < y.toNat + β2.toNat) = β3 at e3 ⊢
    have e4 := sbb_borrow x4 0 β3
    generalize decide (x4.toNat < (0 : BitVec 64).toNat + β3.toNat) = β4 at e4 ⊢
    have e5 := sbb_borrow x5 0 β4
    generalize decide (x5.toNat < (0 : BitVec 64).toNat + β4.toNat) = β5 at e5 ⊢
    have e6 := sbb_borrow u 0 β5
    have e7 := add_carry x6 (u - 0 - (BitVec.ofBool β5).setWidth 64)
    generalize decide (2 ^ 64 ≤ x6.toNat + (u - 0 - (BitVec.ofBool β5).setWidth 64).toNat) = γ at e7 ⊢
    have e8 := adc_carry x7 0 γ
    have z : (0 : BitVec 64).toNat = 0 := rfl
    rw [z] at e4 e5 e6 e8
    have k1 := (x1 - r).isLt
    have k2 := (x2 - d - BitVec.setWidth 64 (BitVec.ofBool β1)).isLt
    have k3 := (x3 - y - BitVec.setWidth 64 (BitVec.ofBool β2)).isLt
    have k4 := (x4 - 0 - BitVec.setWidth 64 (BitVec.ofBool β3)).isLt
    have k5 := (x5 - 0 - BitVec.setWidth 64 (BitVec.ofBool β4)).isLt
    have k6 := (x7 + 0 + BitVec.setWidth 64 (BitVec.ofBool γ)).isLt
    have k7 := (u - 0 - BitVec.setWidth 64 (BitVec.ofBool β5)).isLt
    have q1 := Bool.toNat_le β1; have q2 := Bool.toNat_le β2; have q3 := Bool.toNat_le β3
    have q4 := Bool.toNat_le β4; have q5 := Bool.toNat_le β5; have q6 := Bool.toNat_le γ
    generalize (x1 - r).toNat = R1 at *
    generalize (x2 - d - BitVec.setWidth 64 (BitVec.ofBool β1)).toNat = R2 at *
    generalize (x3 - y - BitVec.setWidth 64 (BitVec.ofBool β2)).toNat = R3 at *
    generalize (x4 - 0 - BitVec.setWidth 64 (BitVec.ofBool β3)).toNat = R4 at *
    generalize (x5 - 0 - BitVec.setWidth 64 (BitVec.ofBool β4)).toNat = R5 at *
    generalize (x6 + (u - 0 - BitVec.setWidth 64 (BitVec.ofBool β5))).toNat = R6 at *
    generalize (x7 + 0 + BitVec.setWidth 64 (BitVec.ofBool γ)).toNat = R7 at *
    generalize (u - 0 - BitVec.setWidth 64 (BitVec.ofBool β5)).toNat = U at *
    generalize (decide (u.toNat < 0 + β5.toNat)).toNat = D6 at *
    generalize (decide (2 ^ 64 ≤ x7.toNat + 0 + γ.toNat)).toNat = D8 at *
    generalize β1.toNat = B1 at *
    generalize β2.toNat = B2 at *
    generalize β3.toNat = B3 at *
    generalize β4.toNat = B4 at *
    generalize β5.toNat = B5 at *
    generalize γ.toNat = G at *
    generalize x1.toNat = X1 at *
    generalize x2.toNat = X2 at *
    generalize x3.toNat = X3 at *
    generalize x4.toNat = X4 at *
    generalize x5.toNat = X5 at *
    generalize x6.toNat = X6 at *
    generalize x7.toNat = X7 at *
    generalize r.toNat = Rb at *
    generalize d.toNat = Dd at *
    generalize y.toNat = Y at *
    generalize u.toNat = Uu at *
    -- The five words less `C`, with the borrow `B5` out.
    have h5 : R1 + 2 ^ 64 * (R2 + 2 ^ 64 * (R3 + 2 ^ 64 * (R4 + 2 ^ 64 * R5))) +
        (Rb + 2 ^ 64 * Dd + 2 ^ 128 * Y) =
        X1 + 2 ^ 64 * (X2 + 2 ^ 64 * (X3 + 2 ^ 64 * (X4 + 2 ^ 64 * X5))) + 2 ^ 320 * B5 := by
      omega_using [e1, e2, e3, e4, e5]
    have hD6 : D6 = 0 := by omega_using [h5, e6, hC, k1, k2, k3, k4, k5, k7, q5]
    have hD8 : D8 = 0 := by omega_using [h5, e6, e7, e8, hD6, hlt, k1, k2, k3, k4, k5, k6]
    subst hD6 hD8
    rw [pow128w, pow320w] at h5 ⊢
    clear hlt hC
    grind only
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]

theorem keeps_sparseX {s s₁ s₂ s₃ s₄ : State} {t0 t1 t2 t3 t4 t5 t6 t7 : Reg} (k₁ : Keeps [.rax, .rdx] s s₁)
    (k₂ : Keeps [.rax, .rcx, .rbp, t0] s₁ s₂) (k₃ : Keeps [t1, t2, t3, t4, t5, t6, t7, .rdx] s₂ s₃)
    (k₄ : Keeps [t0] s₃ s₄) :
    Keeps (.rax :: .rcx :: .rdx :: .rbp :: [t0, t1, t2, t3, t4, t5, t6, t7]) s s₄ :=
  (((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))).trans
    (k₄.mono (by sub_regs))

/-- The reduction of a round for P-384's `p` with BMI2 (`redS_ok` for
`redSparseX`): `2⁶⁴ T' = T + u p` for a word `u`, if `T < 2p + (2⁶⁴ - 1) p`. -/
theorem redSX_ok {s : State} {n i m : Nat} (hn : n = 6)
    (hm : m = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319)
    (hT : regsVal s (wins n i) < 2 * m + (2 ^ 64 - 1) * m) :
    WP isa (.block (redSparseX (wins n i))) s fun s' =>
      (∃ u, u < 2 ^ 64 ∧ 2 ^ 64 * regsVal s' (wins n (i + 1)) = regsVal s (wins n i) + u * m) ∧
      Keeps (.rax :: .rcx :: .rdx :: .rbp :: wins n i) s s' := by
  subst hn
  have hf := fresh_wins (by decide : 6 < 7) i
  rw [wins6_succ]
  rw [wins6] at hf hT ⊢
  generalize win 6 i 0 = t0 at hf hT ⊢
  generalize win 6 i 1 = t1 at hf hT ⊢
  generalize win 6 i 2 = t2 at hf hT ⊢
  generalize win 6 i 3 = t3 at hf hT ⊢
  generalize win 6 i 4 = t4 at hf hT ⊢
  generalize win 6 i 5 = t5 at hf hT ⊢
  generalize win 6 i 6 = t6 at hf hT ⊢
  generalize win 6 i 7 = t7 at hf hT ⊢
  have h0 := hf.head
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h0
  obtain ⟨⟨n01, n02, n03, n04, n05, n06, n07⟩, ha0, hc0, hd0, hb0, -⟩ := h0
  have hR : ∀ q ∈ [t1, t2, t3, t4, t5, t6, t7], q ≠ .rax ∧ q ≠ .rcx ∧ q ≠ .rdx ∧ q ≠ .rbp ∧ q ≠ t0 :=
    fun q hq => by
      have := hf.2 q (List.mem_cons_of_mem _ hq)
      refine ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, fun h => ?_⟩
      subst h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with h | h | h | h | h | h | h <;> subst h
      exacts [n01 rfl, n02 rfl, n03 rfl, n04 rfl, n05 rfl, n06 rfl, n07 rfl]
  rw [redSparseX, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (uSparseX_ok s hd0) fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (prodSparseX_ok s₁ ⟨ha0, hc0, hd0, hb0⟩) fun s₂ ⟨e₂, k₂⟩ => ?_
  have g₁ : ∀ q ∈ [t1, t2, t3, t4, t5, t6, t7], s₂.gpr q = s.gpr q := fun q hq => by
    obtain ⟨qa, qc, qd, qb, q0⟩ := hR q hq
    rw [k₂.1 q (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨qa, qc, qb, q0⟩),
      k₁.1 q (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨qa, qd⟩)]
  have hL₂ : regsVal s₂ [t1, t2, t3, t4, t5, t6, t7] = regsVal s [t1, t2, t3, t4, t5, t6, t7] :=
    regsVal_congr g₁
  have hu₂ : s₂.gpr .rdx = s₁.gpr .rdx := k₂.1 _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by decide, by decide, by decide,
      Ne.symm hd0⟩)
  -- The window's value, and the low word of `u c`, which is `t₀`.
  generalize hU : (s₁.gpr .rdx).toNat = U at e₁ e₂
  generalize hx : (s.gpr t0).toNat = x at e₁
  have hUlt : U < 2 ^ 64 := hU ▸ (s₁.gpr .rdx).isLt
  have hx64 : x < 2 ^ 64 := hx ▸ (s.gpr t0).isLt
  have hlow : U * 0xffffffff00000001 % 2 ^ 64 = x := by omega_using [e₁, hx64]
  rw [hlow] at e₂
  generalize hC : (s₂.gpr .rax).toNat + 2 ^ 64 * (s₂.gpr .rcx).toNat + 2 ^ 128 * (s₂.gpr .rbp).toNat = C at e₂
  have hTv : regsVal s [t0, t1, t2, t3, t4, t5, t6, t7] = x + 2 ^ 64 * regsVal s [t1, t2, t3, t4, t5, t6, t7] := by
    rw [regsVal, hx]
  rw [hTv] at hT
  subst hm
  have hU₂ : (s₂.gpr .rdx).toNat = U := by rw [hu₂, hU]
  refine WP.mono (subSparseX_ok s₂ hf.tail (by omega_using [e₂, hC, hU₂])
    (by omega_using [e₂, hT, hUlt, hL₂, hC, hU₂])) fun s₃ ⟨e₃, k₃⟩ => ?_
  refine WP.mono (mov32zero_ok s₃ t0) fun s₄ ⟨z₄, _, k₄⟩ => ⟨⟨U, hUlt, ?_⟩, ?_⟩
  · have hL₄ : regsVal s₄ [t1, t2, t3, t4, t5, t6, t7] = regsVal s₃ [t1, t2, t3, t4, t5, t6, t7] :=
      regsVal_congr fun q hq => k₄.1 q (by
        simp only [List.mem_singleton]; exact (hR q hq).2.2.2.2)
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    have hv : regsVal s₄ [t1, t2, t3, t4, t5, t6, t7, t0] = regsVal s₄ [t1, t2, t3, t4, t5, t6, t7] := by
      simp only [regsVal, z₄, hz]
    rw [hv, hL₄, hTv]
    omega_using [e₂, e₃, hL₂, hC, hU₂]
  · exact keeps_sparseX k₁ k₂ k₃ k₄

/-- The block ending `redShortX`: `d₁ … d₅ -= C` for `C = rax + 2⁶⁴ rcx + 2¹²⁸ rbp`,
and `d₀ = u` less the borrow, for `u` in `rdx`, if `C` is at most `2⁶⁶ u`. -/
theorem subShortX_ok (s : State) {d0 d1 d2 d3 d4 d5 : Reg} (hf : Fresh [d0, d1, d2, d3, d4, d5])
    (hC : (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rcx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat ≤
      2 ^ 66 * (s.gpr .rdx).toNat) :
    WP isa (.block [.alu .sub d1 (.reg .rax), .alu .sbb d2 (.reg .rcx), .alu .sbb d3 (.reg .rbp),
      .alu .sbb d4 (.imm 0), .alu .sbb d5 (.imm 0), .mov d0 (.reg .rdx), .alu .sbb d0 (.imm 0)]) s fun s' =>
      regsVal s' [d1, d2, d3, d4, d5, d0] +
          ((s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rcx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat) =
        regsVal s [d1, d2, d3, d4, d5] + 2 ^ 320 * (s.gpr .rdx).toNat ∧
      Keeps [d0, d1, d2, d3, d4, d5] s s' := by
  obtain ⟨hnd, hr⟩ := hf
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨⟨n01, n02, n03, n04, n05⟩, ⟨n12, n13, n14, n15⟩, ⟨n23, n24, n25⟩, ⟨n34, n35⟩, n45, -⟩ := hnd
  obtain ⟨⟨ia0, ic0, id0, ib0, -⟩, ⟨ia1, ic1, id1, ib1, -⟩, ⟨ia2, ic2, id2, ib2, -⟩, ⟨ia3, ic3, id3, ib3, -⟩,
    ⟨ia4, ic4, id4, ib4, -⟩, ⟨ia5, ic5, id5, ib5, -⟩⟩ := hr
  have m01 := Ne.symm n01
  have m02 := Ne.symm n02
  have m03 := Ne.symm n03
  have m04 := Ne.symm n04
  have m05 := Ne.symm n05
  have m12 := Ne.symm n12
  have m13 := Ne.symm n13
  have m14 := Ne.symm n14
  have m15 := Ne.symm n15
  have m23 := Ne.symm n23
  have m24 := Ne.symm n24
  have m25 := Ne.symm n25
  have m34 := Ne.symm n34
  have m35 := Ne.symm n35
  have m45 := Ne.symm n45
  have ia0' := Ne.symm ia0
  have ic0' := Ne.symm ic0
  have id0' := Ne.symm id0
  have ib0' := Ne.symm ib0
  have ia1' := Ne.symm ia1
  have ic1' := Ne.symm ic1
  have id1' := Ne.symm id1
  have ib1' := Ne.symm ib1
  have ia2' := Ne.symm ia2
  have ic2' := Ne.symm ic2
  have id2' := Ne.symm id2
  have ib2' := Ne.symm ib2
  have ia3' := Ne.symm ia3
  have ic3' := Ne.symm ic3
  have id3' := Ne.symm id3
  have ib3' := Ne.symm ib3
  have ia4' := Ne.symm ia4
  have ic4' := Ne.symm ic4
  have id4' := Ne.symm id4
  have ib4' := Ne.symm ib4
  have ia5' := Ne.symm ia5
  have ic5' := Ne.symm ic5
  have id5' := Ne.symm id5
  have ib5' := Ne.symm ib5
  simp only [regsVal]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    ↓reduceIte, se0, Option.some.injEq, exists_eq_left', *]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · generalize s.gpr d1 = x1 at *
    generalize s.gpr d2 = x2 at *
    generalize s.gpr d3 = x3 at *
    generalize s.gpr d4 = x4 at *
    generalize s.gpr d5 = x5 at *
    generalize s.gpr .rax = r at *
    generalize s.gpr .rcx = d at *
    generalize s.gpr .rbp = y at *
    generalize s.gpr .rdx = u at *
    have e1 := sub_borrow x1 r
    generalize decide (x1.toNat < r.toNat) = β1 at e1 ⊢
    have e2 := sbb_borrow x2 d β1
    generalize decide (x2.toNat < d.toNat + β1.toNat) = β2 at e2 ⊢
    have e3 := sbb_borrow x3 y β2
    generalize decide (x3.toNat < y.toNat + β2.toNat) = β3 at e3 ⊢
    have e4 := sbb_borrow x4 0 β3
    generalize decide (x4.toNat < (0 : BitVec 64).toNat + β3.toNat) = β4 at e4 ⊢
    have e5 := sbb_borrow x5 0 β4
    generalize decide (x5.toNat < (0 : BitVec 64).toNat + β4.toNat) = β5 at e5 ⊢
    have e6 := sbb_borrow u 0 β5
    have z : (0 : BitVec 64).toNat = 0 := rfl
    rw [z] at e4 e5 e6
    have k1 := (x1 - r).isLt
    have k2 := (x2 - d - BitVec.setWidth 64 (BitVec.ofBool β1)).isLt
    have k3 := (x3 - y - BitVec.setWidth 64 (BitVec.ofBool β2)).isLt
    have k4 := (x4 - 0 - BitVec.setWidth 64 (BitVec.ofBool β3)).isLt
    have k5 := (x5 - 0 - BitVec.setWidth 64 (BitVec.ofBool β4)).isLt
    have k6 := (u - 0 - BitVec.setWidth 64 (BitVec.ofBool β5)).isLt
    have q5 := Bool.toNat_le β5
    generalize (x1 - r).toNat = R1 at *
    generalize (x2 - d - BitVec.setWidth 64 (BitVec.ofBool β1)).toNat = R2 at *
    generalize (x3 - y - BitVec.setWidth 64 (BitVec.ofBool β2)).toNat = R3 at *
    generalize (x4 - 0 - BitVec.setWidth 64 (BitVec.ofBool β3)).toNat = R4 at *
    generalize (x5 - 0 - BitVec.setWidth 64 (BitVec.ofBool β4)).toNat = R5 at *
    generalize (u - 0 - BitVec.setWidth 64 (BitVec.ofBool β5)).toNat = U at *
    generalize (decide (u.toNat < 0 + β5.toNat)).toNat = D6 at *
    generalize β1.toNat = B1 at *
    generalize β2.toNat = B2 at *
    generalize β3.toNat = B3 at *
    generalize β4.toNat = B4 at *
    generalize β5.toNat = B5 at *
    generalize x1.toNat = X1 at *
    generalize x2.toNat = X2 at *
    generalize x3.toNat = X3 at *
    generalize x4.toNat = X4 at *
    generalize x5.toNat = X5 at *
    generalize r.toNat = Rb at *
    generalize d.toNat = Dd at *
    generalize y.toNat = Y at *
    generalize u.toNat = Uu at *
    have h5 : R1 + 2 ^ 64 * (R2 + 2 ^ 64 * (R3 + 2 ^ 64 * (R4 + 2 ^ 64 * R5))) +
        (Rb + 2 ^ 64 * Dd + 2 ^ 128 * Y) =
        X1 + 2 ^ 64 * (X2 + 2 ^ 64 * (X3 + 2 ^ 64 * (X4 + 2 ^ 64 * X5))) + 2 ^ 320 * B5 := by
      omega_using [e1, e2, e3, e4, e5]
    have hD6 : D6 = 0 := by omega_using [h5, e6, hC, k1, k2, k3, k4, k5, k6, q5]
    subst hD6
    rw [pow128w, pow320w] at h5 ⊢
    clear hC
    grind only
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2, ite_false]

theorem keeps_shortX {s s₁ s₂ s₃ : State} {d0 d1 d2 d3 d4 d5 : Reg} (k₁ : Keeps [.rax, .rdx] s s₁)
    (k₂ : Keeps [.rax, .rcx, .rbp, d0] s₁ s₂) (k₃ : Keeps [d0, d1, d2, d3, d4, d5] s₂ s₃) :
    Keeps [.rax, .rcx, .rdx, .rbp, d0, d1, d2, d3, d4, d5] s s₃ :=
  ((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))

/-- A round of P-384's reduction on six words: `2⁶⁴ T' = T + u p` for a word
`u`, `T'` in `d₁ … d₅, d₀`. -/
theorem redShortX_ok {s : State} {d0 d1 d2 d3 d4 d5 : Reg} (hf : Fresh [d0, d1, d2, d3, d4, d5]) {m : Nat}
    (hm : m = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319) :
    WP isa (.block (redShortX [d0, d1, d2, d3, d4, d5])) s fun s' =>
      (∃ u, u < 2 ^ 64 ∧ 2 ^ 64 * regsVal s' [d1, d2, d3, d4, d5, d0] =
        regsVal s [d0, d1, d2, d3, d4, d5] + u * m) ∧
      Keeps [.rax, .rcx, .rdx, .rbp, d0, d1, d2, d3, d4, d5] s s' := by
  have h0 := hf.head
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h0
  obtain ⟨⟨n01, n02, n03, n04, n05⟩, ha0, hc0, hd0, hb0, -⟩ := h0
  have hR : ∀ q ∈ [d1, d2, d3, d4, d5], q ≠ .rax ∧ q ≠ .rcx ∧ q ≠ .rdx ∧ q ≠ .rbp ∧ q ≠ d0 :=
    fun q hq => by
      have := hf.2 q (List.mem_cons_of_mem _ hq)
      refine ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, fun h => ?_⟩
      subst h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with h | h | h | h | h <;> subst h
      exacts [n01 rfl, n02 rfl, n03 rfl, n04 rfl, n05 rfl]
  rw [redShortX, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (uSparseX_ok s hd0) fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (prodSparseX_ok s₁ ⟨ha0, hc0, hd0, hb0⟩) fun s₂ ⟨e₂, k₂⟩ => ?_
  have g₁ : ∀ q ∈ [d1, d2, d3, d4, d5], s₂.gpr q = s.gpr q := fun q hq => by
    obtain ⟨qa, qc, qd, qb, q0⟩ := hR q hq
    rw [k₂.1 q (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨qa, qc, qb, q0⟩),
      k₁.1 q (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨qa, qd⟩)]
  have hL₂ : regsVal s₂ [d1, d2, d3, d4, d5] = regsVal s [d1, d2, d3, d4, d5] := regsVal_congr g₁
  have hu₂ : s₂.gpr .rdx = s₁.gpr .rdx := k₂.1 _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by decide, by decide, by decide,
      Ne.symm hd0⟩)
  generalize hU : (s₁.gpr .rdx).toNat = U at e₁ e₂
  generalize hx : (s.gpr d0).toNat = x at e₁
  have hUlt : U < 2 ^ 64 := hU ▸ (s₁.gpr .rdx).isLt
  have hx64 : x < 2 ^ 64 := hx ▸ (s.gpr d0).isLt
  have hlow : U * 0xffffffff00000001 % 2 ^ 64 = x := by omega_using [e₁, hx64]
  rw [hlow] at e₂
  generalize hC : (s₂.gpr .rax).toNat + 2 ^ 64 * (s₂.gpr .rcx).toNat + 2 ^ 128 * (s₂.gpr .rbp).toNat = C at e₂
  have hTv : regsVal s [d0, d1, d2, d3, d4, d5] = x + 2 ^ 64 * regsVal s [d1, d2, d3, d4, d5] := by
    rw [regsVal, hx]
  have hU₂ : (s₂.gpr .rdx).toNat = U := by rw [hu₂, hU]
  subst hm
  refine WP.mono (subShortX_ok s₂ hf (by omega_using [e₂, hC, hU₂])) fun s₃ ⟨e₃, k₃⟩ =>
    ⟨⟨U, hUlt, ?_⟩, keeps_shortX k₁ k₂ k₃⟩
  rw [hTv]
  omega_using [e₂, e₃, hL₂, hC, hU₂]

end VG.Proof.Mont.X86_64
