import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Env

/-!
# X25519 on x86-64: multiplication with BMI2 and ADX

The product's rows (`mul4_ok`, `MulProd.lean`), the reduction (`reduceX`), and
the multiplication `mulX o a b`, as `mul_ok` states `mul`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-! ## The reduction -/

theorem reduceLo_eq : reduceLo = ([.mov32 .rdx (.imm 38)] : List Instr) ++ (([clear] : List Instr) ++
    (madd .r8 .r9 (.reg .r12) ++ (madd .r9 .r10 (.reg .r13) ++ (madd .r10 .r11 (.reg .r14) ++
      maddLast .r11 .r12 (.reg .r15))))) := by
  simp only [reduceLo, List.append_assoc]; rfl

/-- `r8–r11 + 2²⁵⁶ r12 = r8–r11 + 38 · r12–r15`, with `r12 < 39` and `rdx = 38`. -/
theorem reduceLo_ok (s : State) :
    WP isa (.block reduceLo) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * (s'.gpr .r12).toNat =
        val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          38 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) ∧
      (s'.gpr .r12).toNat < 39 ∧ (s'.gpr .rdx).toNat = 38 ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rcx, .rdx, .rbp] s s' := by
  rw [reduceLo_eq, WP.block_append_iff]
  refine WP.mono (movRdxImm_ok s 38) fun s1 ⟨d1, _, _, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (clear_ok s1) fun s2 ⟨z2, c2, o2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok s2 rfl (noImm_reg _) c2 o2 (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s3 ⟨c3, o3, hc3, ho3, e3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok s3 rfl (noImm_reg _) hc3 ho3 (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s4 ⟨c4, o4, hc4, ho4, e4, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok s4 rfl (noImm_reg _) hc4 ho4 (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s5 ⟨c5, o5, hc5, ho5, e5, k5⟩ => ?_
  have z5 : s5.gpr .rbp = 0 := by
    rw [k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide), z2]
  refine WP.mono (maddLast_ok s5 rfl (noImm_reg _) hc5 ho5 z5 (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s6 ⟨c6, o6, _, _, e6, k6⟩ => ?_
  -- `rdx = 38` along the way.
  have D : ∀ x : State, x.gpr .rdx = s1.gpr .rdx → (x.gpr .rdx).toNat = 38 := fun x h => h ▸ d1
  have D2 := D s2 (k2.1 _ (by decide))
  have D3 := D s3 ((k3.1 _ (by decide)).trans (k2.1 _ (by decide)))
  have D4 := D s4 ((k4.1 _ (by decide)).trans ((k3.1 _ (by decide)).trans (k2.1 _ (by decide))))
  have D5 := D s5 ((k5.1 _ (by decide)).trans ((k4.1 _ (by decide)).trans
    ((k3.1 _ (by decide)).trans (k2.1 _ (by decide)))))
  have D6 := D s6 ((k6.1 _ (by decide)).trans ((k5.1 _ (by decide)).trans ((k4.1 _ (by decide)).trans
    ((k3.1 _ (by decide)).trans (k2.1 _ (by decide))))))
  rw [D2, k2.1 .r12 (by decide), k1.1 .r12 (by decide), k2.1 .r8 (by decide), k1.1 .r8 (by decide),
    k2.1 .r9 (by decide), k1.1 .r9 (by decide)] at e3
  rw [D3, k3.1 .r13 (by decide), k2.1 .r13 (by decide), k1.1 .r13 (by decide),
    k3.1 .r10 (by decide), k2.1 .r10 (by decide), k1.1 .r10 (by decide)] at e4
  rw [D4, k4.1 .r14 (by decide), k3.1 .r14 (by decide), k2.1 .r14 (by decide),
    k1.1 .r14 (by decide), k4.1 .r11 (by decide), k3.1 .r11 (by decide), k2.1 .r11 (by decide),
    k1.1 .r11 (by decide)] at e5
  rw [D5, k5.1 .r15 (by decide), k4.1 .r15 (by decide), k3.1 .r15 (by decide),
    k2.1 .r15 (by decide), k1.1 .r15 (by decide)] at e6
  simp only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e3
  have hB : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
      38 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) < 39 * 2 ^ 256 := by
    simp only [val4]
    have := (s.gpr .r8).isLt; have := (s.gpr .r9).isLt; have := (s.gpr .r10).isLt
    have := (s.gpr .r11).isLt; have := (s.gpr .r12).isLt; have := (s.gpr .r13).isLt
    have := (s.gpr .r14).isLt; have := (s.gpr .r15).isLt
    omega_arith
  have hv : val4 (s6.gpr .r8) (s6.gpr .r9) (s6.gpr .r10) (s6.gpr .r11) +
      2 ^ 256 * (s6.gpr .r12).toNat =
        val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          38 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) := by
    rw [k6.1 .r8 (by decide), k5.1 .r8 (by decide), k4.1 .r8 (by decide), k6.1 .r9 (by decide),
      k5.1 .r9 (by decide), k6.1 .r10 (by decide)]
    simp only [val4] at hB ⊢
    have := (s6.gpr .r11).isLt; have := (s6.gpr .r12).isLt
    have := Bool.toNat_le c6; have := Bool.toNat_le o6
    omega_arith
  have h12 : (s6.gpr .r12).toNat < 39 := by
    simp only [val4] at hv hB
    omega_arith
  exact ⟨hv, h12, D6, (((((k1.mono (by decide)).trans (k2.mono (by decide))).trans
    (k3.mono (by decide))).trans (k4.mono (by decide))).trans (k5.mono (by decide))).trans
    (k6.mono (by decide))⟩

theorem reduceX_eq : reduceX = reduceLo ++ (([.mulx .rcx .rax (.reg .r12)] : List Instr) ++ carry38) := by
  simp only [reduceX, List.append_assoc]

open VG.Spec.X25519 (P) in
/-- The last fold: `r8–r11 + 2²⁵⁶ r12` with `r12 < 79` and `rdx = 38`, folded into `r8–r11`. -/
theorem foldX_ok (s : State) (h12 : (s.gpr .r12).toNat < 79) (hd : (s.gpr .rdx).toNat = 38) :
    WP isa (.block (([.mulx .rcx .rax (.reg .r12)] : List Instr) ++ carry38)) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P =
        (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) + 2 ^ 256 * (s.gpr .r12).toNat) % P ∧
      Keeps [.r8, .r9, .r10, .r11, .rax, .rcx] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (mulx_ok s rfl (noImm_reg _) (by decide)) fun s7 ⟨e7, _, _, k7⟩ => ?_
  rw [hd] at e7
  have hax : (s7.gpr .rax).toNat = 38 * (s.gpr .r12).toNat := by
    have := (s7.gpr .rax).isLt
    omega_arith
  refine WP.mono (carry38_ok s7 (by omega_arith)) fun s8 ⟨e8, k8⟩ => ?_
  refine ⟨?_, (k7.mono (by decide)).trans (k8.mono (by decide))⟩
  rw [e8, hax, k7.1 .r8 (by decide), k7.1 .r9 (by decide), k7.1 .r10 (by decide),
    k7.1 .r11 (by decide), fold256]

open VG.Spec.X25519 (P) in
/-- `r8–r11 + 2²⁵⁶ r12–r15`, reduced into `r8–r11` (modulo `p`). -/
theorem reduceX_ok (s : State) :
    WP isa (.block reduceX) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P =
        (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          2 ^ 256 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15)) % P ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rcx, .rdx, .rbp] s s' := by
  rw [reduceX_eq, WP.block_append_iff]
  refine WP.mono (reduceLo_ok s) fun s6 ⟨hv, h12, hd, k6⟩ => ?_
  refine WP.mono (foldX_ok s6 (by omega) hd) fun s8 ⟨e8, k8⟩ => ?_
  refine ⟨?_, k6.trans (k8.mono (by decide))⟩
  rw [e8, hv, fold256]

/-- `r8–r12` doubled, for `r12 < 2⁶³`. -/
theorem dbl5_ok (s : State) (h12 : (s.gpr .r12).toNat < 2 ^ 63) :
    WP isa (.block dbl5) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * (s'.gpr .r12).toNat =
        2 * (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          2 ^ 256 * (s.gpr .r12).toNat) ∧
      (s'.gpr .r12).toNat ≤ 2 * (s.gpr .r12).toNat + 1 ∧
      Keeps [.r8, .r9, .r10, .r11, .r12] s s' := by
  apply WP.of_runBlock
  simp only [dbl5, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left']
  have e8 := add_carry (s.gpr .r8) (s.gpr .r8)
  generalize decide (2 ^ 64 ≤ (s.gpr .r8).toNat + (s.gpr .r8).toNat) = c8 at e8 ⊢
  have e9 := adc_carry (s.gpr .r9) (s.gpr .r9) c8
  generalize decide (2 ^ 64 ≤ (s.gpr .r9).toNat + (s.gpr .r9).toNat + c8.toNat) = c9 at e9 ⊢
  have e10 := adc_carry (s.gpr .r10) (s.gpr .r10) c9
  generalize decide (2 ^ 64 ≤ (s.gpr .r10).toNat + (s.gpr .r10).toNat + c9.toNat) = c10 at e10 ⊢
  have e11 := adc_carry (s.gpr .r11) (s.gpr .r11) c10
  generalize decide (2 ^ 64 ≤ (s.gpr .r11).toNat + (s.gpr .r11).toNat + c10.toNat) = c11 at e11 ⊢
  have e12 := adc_carry (s.gpr .r12) (s.gpr .r12) c11
  generalize decide (2 ^ 64 ≤ (s.gpr .r12).toNat + (s.gpr .r12).toNat + c11.toNat) = c12 at e12 ⊢
  have := Bool.toNat_le c8; have := Bool.toNat_le c9; have := Bool.toNat_le c10
  have := Bool.toNat_le c11; have := Bool.toNat_le c12
  refine ⟨?_, ?_, fun r hr => ?_, by trivial, by trivial, by trivial⟩
  · simp only [val4]; omega
  · omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

theorem reduceX2_eq : reduceX2 = reduceLo ++ (dbl5 ++
    (([.mulx .rcx .rax (.reg .r12)] : List Instr) ++ carry38)) := by
  simp only [reduceX2, List.append_assoc]

open VG.Spec.X25519 (P) in
/-- `2 (r8–r11 + 2²⁵⁶ r12–r15)`, reduced into `r8–r11` (modulo `p`). -/
theorem reduceX2_ok (s : State) :
    WP isa (.block reduceX2) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P =
        (2 * (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          2 ^ 256 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15))) % P ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rcx, .rdx, .rbp] s s' := by
  rw [reduceX2_eq, WP.block_append_iff]
  refine WP.mono (reduceLo_ok s) fun s6 ⟨hv, h12, hd, k6⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dbl5_ok s6 (by omega)) fun s7 ⟨e7, h7, k7⟩ => ?_
  refine WP.mono (foldX_ok s7 (by have := (s7.gpr .r12).isLt; omega)
    (by rw [k7.1 .rdx (by decide)]; exact hd)) fun s8 ⟨e8, k8⟩ => ?_
  refine ⟨?_, (k6.trans (k7.mono (by decide))).trans (k8.mono (by decide))⟩
  rw [e8, e7, hv, Nat.mul_mod, Nat.mul_mod (2 : Nat) (_ + 2 ^ 256 * _), fold256]

/-! ## The multiplication -/

open VG.Spec.X25519 (P) in
/-- Twice a product. -/
theorem toFe_mul2 {a b c : Nat} (h : c % P = 2 * (a * b) % P) :
    toFe c = toFe a * toFe b + toFe a * toFe b := by
  rw [← toFe_mul (c := a * b) rfl]
  exact toFe_add (by rw [h, Nat.two_mul])

theorem mulX_eq (o a b : Nat) : mulX o a b = (rowX0 a b ++ (rowR' a b 1 .r9 .r10 .r11 .r12 .r13 ++
    (rowR' a b 2 .r10 .r11 .r12 .r13 .r14 ++ rowR' a b 3 .r11 .r12 .r13 .r14 .r15))) ++
      (reduceX ++ store4 o) := by
  simp only [mulX, rowX_eq, List.append_assoc]; rfl

/-- `[o] = [a] · [b]`. -/
theorem mulX_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (mulX o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base b := by
  rw [mulX_eq, WP.block_append_iff]
  refine WP.mono (mul4_ok hs ha hb) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduceX_ok s₄) fun s₅ ⟨e5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by decide)
  refine WP.mono (store4_ok hs₅ ho) fun s₆ ⟨m6, g6, rd6, wr6⟩ => ?_
  have M : s₅.mem = s.mem := k5.2.1.trans k4.2.1
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [g6, k5.1 r (by simp [*]), k4.1 r (by simp [*])]
  · rw [rd6, k5.2.2.1, k4.2.2.1]
  · rw [wr6, k5.2.2.2, k4.2.2.2]
  · rw [m6, M]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul
    rw [m6, fe_st4 _ _ (by omega), e5, e4]

theorem mul2X_eq (o a b : Nat) : mul2X o a b = (rowX0 a b ++ (rowR' a b 1 .r9 .r10 .r11 .r12 .r13 ++
    (rowR' a b 2 .r10 .r11 .r12 .r13 .r14 ++ rowR' a b 3 .r11 .r12 .r13 .r14 .r15))) ++
      (reduceX2 ++ store4 o) := by
  simp only [mul2X, rowX_eq, List.append_assoc]; rfl

/-- `[o] = 2 · [a] · [b]`. -/
theorem mul2X_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (mul2X o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o =
        F s.mem base a * F s.mem base b + F s.mem base a * F s.mem base b := by
  rw [mul2X_eq, WP.block_append_iff]
  refine WP.mono (mul4_ok hs ha hb) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduceX2_ok s₄) fun s₅ ⟨e5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by decide)
  refine WP.mono (store4_ok hs₅ ho) fun s₆ ⟨m6, g6, rd6, wr6⟩ => ?_
  have M : s₅.mem = s.mem := k5.2.1.trans k4.2.1
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [g6, k5.1 r (by simp [*]), k4.1 r (by simp [*])]
  · rw [rd6, k5.2.2.1, k4.2.2.1]
  · rw [wr6, k5.2.2.2, k4.2.2.2]
  · rw [m6, M]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul2
    rw [m6, fe_st4 _ _ (by omega), e5]
    exact congrArg (fun x => 2 * x % VG.Spec.X25519.P) e4

end VG.Proof.X25519.X86_64
