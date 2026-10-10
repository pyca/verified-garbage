import VerifiedGarbage.Proof.Mont.X86_64.Friendly
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Montgomery arithmetic on x86-64: the reduction for P-384's `p`

For `p = 2³⁸⁴ - c`, `c = 2¹²⁸ + 2⁹⁶ - 2³² + 1` (`Mod.sparse`), the reduction
of a round adds `u p` to the window `T` for `u = t₀ (2³² + 1) mod 2⁶⁴`, which
is `t₀ m' mod 2⁶⁴` (`uSparse_ok`): `T + u p = T - u c + 2³⁸⁴ u`. The low word
of `u c` is `t₀`, so `(T + u p) / 2⁶⁴` is the words above `t₀` less
`⌊u c / 2⁶⁴⌋` (three words, from two products, `prodSparse_ok`) plus
`2³²⁰ u` (`subSparse_ok`); `redS_ok` is the round's step,
`2⁶⁴ T' = T + u p`. `roundM_ok` is a round by `mul`, with any of the
reductions (general, friendly, or this one).
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono se0 add_carry adc_carry sub_borrow sbb_borrow
  toNat_ofBool)

/-- `rcx = t₀ (2³² + 1) mod 2⁶⁴`. -/
theorem uSparse_ok (s : State) {t0 : Reg} (h0 : t0 ≠ .rcx) :
    WP isa (.block (uSparse t0)) s fun s' =>
      (s'.gpr .rcx).toNat = (s.gpr t0).toNat * (2 ^ 32 + 1) % 2 ^ 64 ∧ Keeps [.rcx] s s' := by
  have hs : 1 ≤ 32 ∧ 32 ≤ 63 := by decide
  apply WP.of_runBlock
  simp only [uSparse, runBlock_cons, runStep_some, runBlock_nil, exec, execShift, execAlu, readSrc, hs, and_self,
    ↓reduceIte, Option.bind_some, Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    h0, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · generalize s.gpr t0 = t
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_add_mod, Nat.mul_add,
      Nat.mul_one]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `rbp + 2⁶⁴ rdx + 2¹²⁸ t₀` is `⌊u c / 2⁶⁴⌋` for `u` in `rcx` (kept), with
`u c mod 2⁶⁴` below. -/
theorem prodSparse_ok (s : State) {t0 : Reg} (h0 : t0 ≠ .rax ∧ t0 ≠ .rcx ∧ t0 ≠ .rdx ∧ t0 ≠ .rbp) :
    WP isa (.block (prodSparse t0)) s fun s' =>
      2 ^ 64 * ((s'.gpr .rbp).toNat + 2 ^ 64 * (s'.gpr .rdx).toNat + 2 ^ 128 * (s'.gpr t0).toNat) +
          (s.gpr .rcx).toNat * 0xffffffff00000001 % 2 ^ 64 =
        (s.gpr .rcx).toNat * 0xffffffff00000001 + 2 ^ 64 * ((s.gpr .rcx).toNat * 0xffffffff) +
          2 ^ 128 * (s.gpr .rcx).toNat ∧
      Keeps [.rax, .rdx, .rbp, t0] s s' := by
  obtain ⟨ha, hc, hd, hb⟩ := h0
  apply WP.of_runBlock
  simp only [prodSparse, runBlock_cons, runStep_some, runBlock_nil, exec, execMul, execAlu, readSrc,
    readSrc32, Option.bind_some, Option.map_some, State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ↓reduceIte,
    Ne.symm hd, Ne.symm hb, reduceCtorEq, Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · generalize s.gpr .rcx = u
    have hu := u.isLt
    have hc0 : sparseC0.toNat = 0xffffffff00000001 := rfl
    have hc1 : (BitVec.setWidth 64 sparseC1).toNat = 0xffffffff := rfl
    have z : ∀ c : Bool, (BitVec.setWidth 64 (0 : BitVec 32) + 0 + (BitVec.ofBool c).setWidth 64).toNat =
        c.toNat := by
      intro c; cases c <;> rfl
    rw [hc0, hc1]
    have l0 : 0xffffffff00000001 * u.toNat / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul (by omega)
    have l1 : 0xffffffff * u.toNat / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul (by omega)
    have e0 : (BitVec.ofNat 64 (0xffffffff00000001 * u.toNat / 2 ^ 64)).toNat =
        0xffffffff00000001 * u.toNat / 2 ^ 64 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt l0]
    have e1 : (BitVec.ofNat 64 (0xffffffff * u.toNat / 2 ^ 64)).toNat = 0xffffffff * u.toNat / 2 ^ 64 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt l1]
    have e2 : (BitVec.ofNat 64 (0xffffffff * u.toNat)).toNat = 0xffffffff * u.toNat % 2 ^ 64 :=
      BitVec.toNat_ofNat _ _
    have a1 := add_carry (BitVec.ofNat 64 (0xffffffff00000001 * u.toNat / 2 ^ 64))
      (BitVec.ofNat 64 (0xffffffff * u.toNat))
    have a2 := adc_carry (BitVec.ofNat 64 (0xffffffff * u.toNat / 2 ^ 64)) u
      (decide (2 ^ 64 ≤ (BitVec.ofNat 64 (0xffffffff00000001 * u.toNat / 2 ^ 64)).toNat +
        (BitVec.ofNat 64 (0xffffffff * u.toNat)).toNat))
    generalize decide (2 ^ 64 ≤ (BitVec.ofNat 64 (0xffffffff00000001 * u.toNat / 2 ^ 64)).toNat +
      (BitVec.ofNat 64 (0xffffffff * u.toNat)).toNat) = c₁ at a1 a2 ⊢
    generalize decide (2 ^ 64 ≤ (BitVec.ofNat 64 (0xffffffff * u.toNat / 2 ^ 64)).toNat + u.toNat +
      c₁.toNat) = c₂ at a2 ⊢
    rw [z]
    rw [e0, e2] at a1
    rw [e1] at a2
    have hc2 := Bool.toNat_le c₂
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2, ite_false]

/-- `t₁ … t₇ += 2³²⁰ u - C` for `C = rbp + 2⁶⁴ rdx + 2¹²⁸ t₀` and `u` in `rcx`,
if `C` is at most `2⁶⁶ u` (so `u = 0` gives `C = 0`, and the borrow out of
`t₅` can be taken from `u`) and the result is below `2⁴⁴⁸`. -/
theorem subSparse_ok (s : State) {t0 t1 t2 t3 t4 t5 t6 t7 : Reg}
    (hf : Fresh [t0, t1, t2, t3, t4, t5, t6, t7])
    (hC : (s.gpr .rbp).toNat + 2 ^ 64 * (s.gpr .rdx).toNat + 2 ^ 128 * (s.gpr t0).toNat ≤
      2 ^ 66 * (s.gpr .rcx).toNat)
    (hlt : regsVal s [t1, t2, t3, t4, t5, t6, t7] + 2 ^ 320 * (s.gpr .rcx).toNat <
      2 ^ 448 + ((s.gpr .rbp).toNat + 2 ^ 64 * (s.gpr .rdx).toNat + 2 ^ 128 * (s.gpr t0).toNat)) :
    WP isa (.block (subSparse t0 t1 t2 t3 t4 t5 t6 t7)) s fun s' =>
      regsVal s' [t1, t2, t3, t4, t5, t6, t7] +
          ((s.gpr .rbp).toNat + 2 ^ 64 * (s.gpr .rdx).toNat + 2 ^ 128 * (s.gpr t0).toNat) =
        regsVal s [t1, t2, t3, t4, t5, t6, t7] + 2 ^ 320 * (s.gpr .rcx).toNat ∧
      Keeps [t1, t2, t3, t4, t5, t6, t7, .rcx] s s' := by
  obtain ⟨hnd, hr⟩ := hf
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨⟨n01, n02, n03, n04, n05, n06, n07⟩, ⟨n12, n13, n14, n15, n16, n17⟩, ⟨n23, n24, n25, n26, n27⟩,
    ⟨n34, n35, n36, n37⟩, ⟨n45, n46, n47⟩, ⟨n56, n57⟩, n67, -⟩ := hnd
  obtain ⟨⟨-, c0, d0, b0, -⟩, ⟨-, c1, d1, b1, -⟩, ⟨-, c2, d2, b2, -⟩, ⟨-, c3, d3, b3, -⟩, ⟨-, c4, d4, b4, -⟩,
    ⟨-, c5, d5, b5, -⟩, ⟨-, c6, d6, b6, -⟩, ⟨-, c7, d7, b7, -⟩⟩ := hr
  have m01 := Ne.symm n01
  have m02 := Ne.symm n02
  have m03 := Ne.symm n03
  have m04 := Ne.symm n04
  have m05 := Ne.symm n05
  have m06 := Ne.symm n06
  have m07 := Ne.symm n07
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
  have c0' := Ne.symm c0
  have d0' := Ne.symm d0
  have b0' := Ne.symm b0
  have c1' := Ne.symm c1
  have d1' := Ne.symm d1
  have b1' := Ne.symm b1
  have c2' := Ne.symm c2
  have d2' := Ne.symm d2
  have b2' := Ne.symm b2
  have c3' := Ne.symm c3
  have d3' := Ne.symm d3
  have b3' := Ne.symm b3
  have c4' := Ne.symm c4
  have d4' := Ne.symm d4
  have b4' := Ne.symm b4
  have c5' := Ne.symm c5
  have d5' := Ne.symm d5
  have b5' := Ne.symm b5
  have c6' := Ne.symm c6
  have d6' := Ne.symm d6
  have b6' := Ne.symm b6
  have c7' := Ne.symm c7
  have d7' := Ne.symm d7
  have b7' := Ne.symm b7
  simp only [regsVal] at hlt ⊢
  apply WP.of_runBlock
  simp only [subSparse, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
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
    generalize s.gpr t0 = y at *
    generalize s.gpr .rbp = r at *
    generalize s.gpr .rdx = d at *
    generalize s.gpr .rcx = u at *
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
    subst hD6 hD8; grind only
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]

/-- The window of round `i` for six words, and the next one. -/
theorem wins6 (i : Nat) : wins 6 i = [win 6 i 0, win 6 i 1, win 6 i 2, win 6 i 3, win 6 i 4, win 6 i 5,
    win 6 i 6, win 6 i 7] := rfl

theorem wins6_succ (i : Nat) : wins 6 (i + 1) = [win 6 i 1, win 6 i 2, win 6 i 3, win 6 i 4, win 6 i 5,
    win 6 i 6, win 6 i 7, win 6 i 0] := by
  rw [wins_succ]; rfl

theorem keeps_sparse {s s₁ s₂ s₃ s₄ : State} {t0 t1 t2 t3 t4 t5 t6 t7 : Reg} (k₁ : Keeps [.rcx] s s₁)
    (k₂ : Keeps [.rax, .rdx, .rbp, t0] s₁ s₂) (k₃ : Keeps [t1, t2, t3, t4, t5, t6, t7, .rcx] s₂ s₃)
    (k₄ : Keeps [t0] s₃ s₄) :
    Keeps (.rax :: .rcx :: .rdx :: .rbp :: [t0, t1, t2, t3, t4, t5, t6, t7]) s s₄ :=
  (((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))).trans
    (k₄.mono (by sub_regs))

/-- The reduction of a round for P-384's `p`: `2⁶⁴ T' = T + u p` for a word
`u`, if `T < 2p + (2⁶⁴ - 1) p`. -/
theorem redS_ok {s : State} {n i m : Nat} (hn : n = 6)
    (hm : m = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319)
    (hT : regsVal s (wins n i) < 2 * m + (2 ^ 64 - 1) * m) :
    WP isa (.block (redSparse (wins n i))) s fun s' =>
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
  rw [redSparse, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (uSparse_ok s hc0) fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (prodSparse_ok s₁ ⟨ha0, hc0, hd0, hb0⟩) fun s₂ ⟨e₂, k₂⟩ => ?_
  have g₁ : ∀ q ∈ [t1, t2, t3, t4, t5, t6, t7], s₂.gpr q = s.gpr q := fun q hq => by
    obtain ⟨qa, qc, qd, qb, q0⟩ := hR q hq
    rw [k₂.1 q (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨qa, qd, qb, q0⟩),
      k₁.1 q (by simp only [List.mem_singleton]; exact qc)]
  have hL₂ : regsVal s₂ [t1, t2, t3, t4, t5, t6, t7] = regsVal s [t1, t2, t3, t4, t5, t6, t7] :=
    regsVal_congr g₁
  have hu₂ : s₂.gpr .rcx = s₁.gpr .rcx := k₂.1 _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by decide, by decide, by decide,
      Ne.symm hc0⟩)
  -- The window's value, and the low word of `u c`, which is `t₀`.
  generalize hU : (s₁.gpr .rcx).toNat = U at e₁ e₂
  generalize hx : (s.gpr t0).toNat = x at e₁
  have hUlt : U < 2 ^ 64 := hU ▸ (s₁.gpr .rcx).isLt
  have hx64 : x < 2 ^ 64 := hx ▸ (s.gpr t0).isLt
  have hlow : U * 0xffffffff00000001 % 2 ^ 64 = x := by omega_using [e₁, hx64]
  rw [hlow] at e₂
  generalize hC : (s₂.gpr .rbp).toNat + 2 ^ 64 * (s₂.gpr .rdx).toNat + 2 ^ 128 * (s₂.gpr t0).toNat = C at e₂
  have hTv : regsVal s [t0, t1, t2, t3, t4, t5, t6, t7] = x + 2 ^ 64 * regsVal s [t1, t2, t3, t4, t5, t6, t7] := by
    rw [regsVal, hx]
  rw [hTv] at hT
  subst hm
  have hU₂ : (s₂.gpr .rcx).toNat = U := by rw [hu₂, hU]
  refine WP.mono (subSparse_ok s₂ hf (by omega_using [e₂, hC, hU₂])
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
  · exact keeps_sparse k₁ k₂ k₃ k₄

/-! ## A round -/

/-- Round `i` of the multiplication by `mul`: `2⁶⁴ T' = T + a_i B + u m`, and
`T' < 2m` if `T < 2m`. -/
theorem roundM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hn : M.n < 7) {a b i m : Nat} (ha : a + 8 * i + 8 ≤ size) (hb : b + 8 * M.n ≤ size)
    (hmo : M.mo + 8 * M.n ≤ size) (hm : wordsVal s.mem base M.mo M.n = m)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) (hok : M.ok m = true)
    (hB : wordsVal s.mem base b M.n < m) (hT : regsVal s (wins M.n i) < 2 * m) :
    WP isa (.block (roundM M a b i)) s fun s' =>
      (∃ u, 2 ^ 64 * regsVal s' (wins M.n (i + 1)) = regsVal s (wins M.n i) +
        (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n + u * m) ∧
      regsVal s' (wins M.n (i + 1)) < 2 * m ∧
      Keeps (.rax :: .rcx :: .rdx :: .rbp :: wins M.n i) s s' := by
  have hm' : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  have hA := (word s.mem base (a + 8 * i)).isLt
  have hAB : (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [show roundM M a b i = (([.mov .rcx (.mem (sc (a + 8 * i)))] : List Instr) ++
      (mulRow ((List.range M.n).map (win M.n i)) b ++ carryUp (win M.n i M.n) (win M.n i (M.n + 1)))) ++
        redRound M i by simp only [roundM, List.append_assoc], WP.block_append_iff]
  refine WP.mono (prod_ok hs hn ha hb hm' hB hT) fun s₂ ⟨e₂, hs₂, k₂⟩ => ?_
  have hmem : s₂.mem = s.mem := k₂.2.1
  -- From `2⁶⁴ T' = T + a_i B + u m` for a word `u`.
  have fin : ∀ {s' : State} (u : Nat), u < 2 ^ 64 →
      2 ^ 64 * regsVal s' (wins M.n (i + 1)) = regsVal s₂ (wins M.n i) + u * m →
      (∃ u, 2 ^ 64 * regsVal s' (wins M.n (i + 1)) = regsVal s (wins M.n i) +
        (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n + u * m) ∧
      regsVal s' (wins M.n (i + 1)) < 2 * m := fun u hu e => by
    rw [e₂] at e
    have hum : u * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by omega) (Nat.le_refl _)
    refine ⟨⟨u, e⟩, Nat.lt_of_mul_lt_mul_left (a := 2 ^ 64) ?_⟩
    rw [e]; omega
  unfold redRound
  dsimp only
  split
  · rename_i hsp
    obtain ⟨hn6, hm6⟩ := Mod.ok_sparse hok hsp
    refine WP.mono (redS_ok hn6 hm6 (by rw [e₂]; omega))
      fun s' ⟨⟨u, hu, eu⟩, k⟩ => ⟨(fin u hu eu).1, (fin u hu eu).2, k₂.trans k⟩
  have hred := Mod.ok_red hok
  split
  · rename_i hg
    refine WP.mono (redGen_ok hs₂ hn hmo (by rw [hmem, hm]) hinv (by rw [e₂]; omega))
      fun s' ⟨⟨u, hu, eu⟩, k⟩ => ⟨(fin u hu eu).1, (fin u hu eu).2, k₂.trans k⟩
  · rename_i ws hf
    rw [hf] at hred
    have ht0 := (s₂.gpr (win M.n i 0)).isLt
    have hum : (s₂.gpr (win M.n i 0)).toNat * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by omega) (Nat.le_refl _)
    refine WP.mono (redF_ok false hn hred hm' (by rw [e₂]; omega)) fun s' ⟨e, k⟩ =>
      ⟨(fin _ ht0 e).1, (fin _ ht0 e).2, k₂.trans (k.mono (by sub_regs))⟩

end VG.Proof.Mont.X86_64
