module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P384Order
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Fn
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Fn
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words

/-!
# Arithmetic modulo P-384's order on RISC-V: the operations

The operations of `Impl/Weierstrass/RISCV64/P384Order.lean` meet `CoreOk`
(`mulCore_core`, `addCore_core`, `subCore_core`) by the lemmas of P-384's
field for any modulus `2³⁸⁴ - M` (`reduceWith_ok`, `mulWith_ok`,
`csubWith_ok`, `subWith_ok`), given the blocks that differ:

* the quotient word `q = w n' mod 2⁶⁴`, for which `q c ≡ w (mod 2⁶⁴)`
  (`quotN_ok`, `quot_low`), and the words 1 to 3 of `q c` (`qc_ok`), which
  make the rounds' `QOk` (`qOkN`);
* the words of `c = 2³⁸⁴ - n` into `t0` (`kN_ok`), and those of `n` under
  the mask (`kmN_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P384Order

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide
open VG.Impl.Weierstrass.RISCV64.P384Field (rw)
open VG.Impl.Weierstrass.RISCV64.P384Order (qc quotN sumNKs subNKs NINV C0 C1 C2 N0 N1 N2)
open VG.Proof.Weierstrass.RISCV64.P384Field
open VG.Proof.X25519.RISCV64 (Ctx Rest wp_mul wp_and)
open VG.Proof.X448.RISCV64.R64 (colsV al8)
open VG.Proof.Weierstrass.RISCV64.P256Order (wp_li64 wp_mulhu ofNat_lt add_toNat)
open VG.Proof.Weierstrass.RISCV64.P256Field (upd_keeps)
open VG.Impl.Words.RISCV64 (li64)

/-- `c = 2³⁸⁴ - n`. -/
abbrev Cn : Nat := 0x389cb27e0bc8d220a7e5f24db74f58851313e695333ad68d

/-- P-384's order. -/
abbrev N : Nat := 2 ^ 384 - Cn

theorem N_add_Cn : N + Cn = 2 ^ 384 := by unfold N Cn; omega

/-! ## The rounds' blocks -/

/-- `q = w n' mod 2⁶⁴` has `q c ≡ w (mod 2⁶⁴)`. -/
theorem quot_low (w : Nat) (hw : w < 2 ^ 64) : w * 0x6ed46089e88fdc45 % 2 ^ 64 * Cn % 2 ^ 64 = w := by
  rw [Nat.mod_mul_mod, show w * 0x6ed46089e88fdc45 * Cn =
      w + 2 ^ 64 * (w * 0x18824bcf3baaa877832b8caedc269632fbcd05f35fc4f751) by unfold Cn; omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw]

/-- `quotN r`: the quotient word of `r`, in place. -/
theorem quotN_ok {s : State} {r : Reg} (h0 : r ≠ .t0) (ha : r ≠ .a0) :
    WP isa (.block (quotN r)) s fun s' =>
      (s'.gpr r).toNat * Cn % 2 ^ 64 = (s.gpr r).toNat ∧ Keeps [.t0, .a0, r] s s' := by
  unfold quotN
  refine wp_li64 (by decide) NINV fun s1 e1 k1 => wp_mul fun s2 u2 => WP.block_nil ⟨?_, ?_⟩
  · rw [u2.gpr, e1, k1.1 _ (by simp [h0, ha]), BitVec.toNat_mul,
      show NINV.toNat = 0x6ed46089e88fdc45 from rfl]
    exact quot_low _ (BitVec.isLt _)
  · exact (k1.trans (upd_keeps u2)).mono fun x hx => by simpa using hx

/-- `q c / 2⁶⁴` from the products of `q` and `c`'s words. -/
theorem qc_div (q : Nat) : q * Cn / 2 ^ 64 =
    q * 0x1313e695333ad68d / 2 ^ 64 + (q * 0xa7e5f24db74f5885 + 2 ^ 64 * (q * 0x389cb27e0bc8d220)) := by
  rw [show Cn = 0x1313e695333ad68d + 2 ^ 64 * (0xa7e5f24db74f5885 + 2 ^ 64 * 0x389cb27e0bc8d220) from rfl,
    Nat.mul_add, Nat.mul_left_comm, Nat.mul_add, Nat.mul_left_comm q (2 ^ 64),
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos 64)]

/-- The words 1 to 3 of `q c`, from its products' words `P1 = q c₁` and `P2 = q c₂`. -/
theorem qc_arith {H0 P1 P2 L1 H1 S1 c1 Y L2 H2 S2 c2 Z : Nat}
    (F1 : L1 + 2 ^ 64 * H1 = P1) (F2 : S1 + 2 ^ 64 * c1 = H0 + L1) (F3 : Y = H1 + c1)
    (F4 : L2 + 2 ^ 64 * H2 = P2) (hP2 : P2 < 2 ^ 64 * 0x389cb27e0bc8d220)
    (F5 : S2 + 2 ^ 64 * c2 = Y + L2) (F6 : Z = c2 + H2) (hc2 : c2 ≤ 1) :
    S1 + 2 ^ 64 * S2 + 2 ^ 128 * Z = H0 + (P1 + 2 ^ 64 * P2) ∧ Z < 2 ^ 62 := by
  omega

/-- `qc r`: `a4 + 2⁶⁴ a5 + 2¹²⁸ a6 = q c / 2⁶⁴` for `q` in `r`. -/
theorem qc_ok {s : State} {r : Reg} (h0 : r ≠ .t0) (ha : r ≠ .a0) (h4 : r ≠ .a4) (h5 : r ≠ .a5)
    (h6 : r ≠ .a6) (h7 : r ≠ .a7) :
    WP isa (.block (qc r)) s fun s' =>
      (s'.gpr .a4).toNat + 2 ^ 64 * (s'.gpr .a5).toNat + 2 ^ 128 * (s'.gpr .a6).toNat =
        (s.gpr r).toNat * Cn / 2 ^ 64 ∧ (s'.gpr .a6).toNat < 2 ^ 62 ∧
      Keeps [.t0, .a0, .a4, .a5, .a6, .a7] s s' := by
  unfold qc
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_li64 (by decide) C0 fun s1 e1 k1 => wp_mulhu fun s2 u2 => ?_
  refine wp_li64 (by decide) C1 fun s3 e3 k3 => wp_mul fun s4 u4 => wp_mulhu fun s5 u5 => ?_
  refine wp_add fun s6 u6 => wp_sltu fun s7 u7 => wp_add fun s8 u8 => ?_
  refine wp_li64 (by decide) C2 fun s9 e9 k9 => wp_mul fun s10 u10 => wp_mulhu fun s11 u11 => ?_
  refine wp_add fun s12 u12 => wp_sltu fun s13 u13 => wp_add fun s14 u14 => WP.block_nil ?_
  -- The multiplier, through the steps.
  have q1 : s1.gpr r = s.gpr r := k1.1 _ (by simp [h0, ha])
  have q3 : s3.gpr r = s.gpr r := by rw [k3.1 _ (by simp [h0, ha]), u2.other _ h4, q1]
  have q4 : s4.gpr r = s.gpr r := by rw [u4.other _ h5, q3]
  have q9 : s9.gpr r = s.gpr r := by
    rw [k9.1 _ (by simp [h0, ha]), u8.other _ h6, u7.other _ h5, u6.other _ h4, u5.other _ h6, q4]
  have q10 : s10.gpr r = s.gpr r := by rw [u10.other _ h7, q9]
  -- The words.
  have hA4 : s2.gpr .a4 = BitVec.ofNat 64 ((s.gpr r).toNat * C0.toNat / 2 ^ 64) := by rw [u2.gpr, q1, e1]
  have hL1 : s4.gpr .a5 = s.gpr r * C1 := by rw [u4.gpr, q3, e3]
  have hH1 : s5.gpr .a6 = BitVec.ofNat 64 ((s.gpr r).toNat * C1.toNat / 2 ^ 64) := by
    rw [u5.gpr, q4, u4.other .t0 (by decide), e3]
  have a4_5 : s5.gpr .a4 = s2.gpr .a4 := by
    rw [u5.other _ (by decide), u4.other _ (by decide), k3.1 _ (by decide)]
  have a5_5 : s5.gpr .a5 = s4.gpr .a5 := u5.other _ (by decide)
  have hS1 : s6.gpr .a4 = s5.gpr .a4 + s5.gpr .a5 := u6.gpr
  have hc1 : s7.gpr .a5 = if s5.gpr .a4 + s5.gpr .a5 < s5.gpr .a5 then 1 else 0 := by
    rw [u7.gpr, u6.other .a5 (by decide), hS1]
  have hY : s8.gpr .a6 = s7.gpr .a6 + s7.gpr .a5 := u8.gpr
  have a6_7 : s7.gpr .a6 = s5.gpr .a6 := by rw [u7.other _ (by decide), u6.other _ (by decide)]
  have hL2 : s10.gpr .a7 = s.gpr r * C2 := by rw [u10.gpr, q9, e9]
  have hH2 : s11.gpr .a0 = BitVec.ofNat 64 ((s.gpr r).toNat * C2.toNat / 2 ^ 64) := by
    rw [u11.gpr, q10, u10.other .t0 (by decide), e9]
  have a6_11 : s11.gpr .a6 = s8.gpr .a6 := by
    rw [u11.other _ (by decide), u10.other _ (by decide), k9.1 _ (by decide)]
  have a7_11 : s11.gpr .a7 = s10.gpr .a7 := u11.other _ (by decide)
  have hS2 : s12.gpr .a5 = s11.gpr .a6 + s11.gpr .a7 := u12.gpr
  have hc2 : s13.gpr .a6 = if s11.gpr .a6 + s11.gpr .a7 < s11.gpr .a7 then 1 else 0 := by
    rw [u13.gpr, u12.other .a7 (by decide), hS2]
  have hZ : s14.gpr .a6 = s13.gpr .a6 + s13.gpr .a0 := u14.gpr
  have a0_13 : s13.gpr .a0 = s11.gpr .a0 := by rw [u13.other _ (by decide), u12.other _ (by decide)]
  have o4 : s14.gpr .a4 = s6.gpr .a4 := by
    rw [u14.other _ (by decide), u13.other _ (by decide), u12.other _ (by decide), u11.other _ (by decide),
      u10.other _ (by decide), k9.1 _ (by decide), u8.other _ (by decide), u7.other _ (by decide)]
  have o5 : s14.gpr .a5 = s12.gpr .a5 := by rw [u14.other _ (by decide), u13.other _ (by decide)]
  -- Their numbers.
  have bq := (s.gpr r).isLt
  have c1 := carry (s5.gpr .a4) (s5.gpr .a5)
  rw [← hc1, ← hS1, a4_5, a5_5, hA4, ofNat_lt (Nat.div_lt_of_lt_mul (by
    rw [show C0.toNat = 0x1313e695333ad68d from rfl]; omega)),
    show C0.toNat = 0x1313e695333ad68d from rfl] at c1
  have m1 := mul_words (s.gpr r) C1
  rw [← hL1, ← hH1] at m1
  have bH1 : (s5.gpr .a6).toNat + 1 < 2 ^ 64 := by
    have := (s4.gpr .a5).isLt
    have : (s.gpr r).toNat * C1.toNat < 2 ^ 64 * (2 ^ 64 - 2) := by
      rw [show C1.toNat = 0xa7e5f24db74f5885 from rfl]; omega
    omega
  have eY : (s8.gpr .a6).toNat = (s5.gpr .a6).toNat + (s7.gpr .a5).toNat := by
    rw [hY, a6_7]; exact add_toNat (by have := carry_le (s5.gpr .a4 + s5.gpr .a5 < s5.gpr .a5); rw [← hc1] at this; omega)
  have m2 := mul_words (s.gpr r) C2
  rw [← hL2, ← hH2] at m2
  have c2 := carry (s11.gpr .a6) (s11.gpr .a7)
  rw [← hc2, ← hS2, a6_11, a7_11] at c2
  have bH2 : (s11.gpr .a0).toNat + 1 < 2 ^ 64 := by
    have := (s10.gpr .a7).isLt
    have : (s.gpr r).toNat * C2.toNat < 2 ^ 64 * (2 ^ 64 - 2) := by
      rw [show C2.toNat = 0x389cb27e0bc8d220 from rfl]; omega
    omega
  have lc2 : (s13.gpr .a6).toNat ≤ 1 := by rw [hc2]; exact carry_le _
  have eZ : (s14.gpr .a6).toNat = (s13.gpr .a6).toNat + (s11.gpr .a0).toNat := by
    rw [hZ, a0_13]; exact add_toNat (by omega)
  rw [show C1.toNat = 0xa7e5f24db74f5885 from rfl] at m1
  rw [show C2.toNat = 0x389cb27e0bc8d220 from rfl] at m2
  obtain ⟨v, l⟩ := qc_arith m1 c1 eY m2 (Nat.mul_lt_mul_of_pos_right bq (by decide)) c2 eZ lc2
  refine ⟨by rw [o4, o5, qc_div]; exact v, l, ?_⟩
  exact (((((((((((((k1.trans (upd_keeps u2)).trans k3).trans (upd_keeps u4)).trans (upd_keeps u5)).trans
    (upd_keeps u6)).trans (upd_keeps u7)).trans (upd_keeps u8)).trans k9).trans (upd_keeps u10)).trans
    (upd_keeps u11)).trans (upd_keeps u12)).trans (upd_keeps u13)).trans (upd_keeps u14)).mono
    fun x hx => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]

/-- The rounds' blocks modulo `n`. -/
theorem qOkN : QOk quotN qc Cn where
  quot i hi s := by
    obtain ⟨-, -, -, -, -, n0t, -, -, n0a⟩ := (rw_facts i hi).2.2.2.2.2.2 0 (by decide)
    simp only [Nat.add_zero] at n0t n0a
    exact quotN_ok n0t n0a
  qm i hi s := by
    obtain ⟨-, n4, n5, n6, n7, n0t, -, -, n0a⟩ := (rw_facts i hi).2.2.2.2.2.2 0 (by decide)
    simp only [Nat.add_zero] at n4 n5 n6 n7 n0t n0a
    exact qc_ok n0t n0a n4 n5 n6 n7

/-! ## The words of `c` and of `n` -/

/-- The words of `c`. -/
def NN (j : Nat) : Nat := [0x1313e695333ad68d, 0xa7e5f24db74f5885, 0x389cb27e0bc8d220, 0, 0, 0].getD j 0

theorem NN_lt (j : Nat) : NN j < 2 ^ 64 := by
  unfold NN
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp

theorem NN_val : colsV NN 6 + N = 2 ^ 384 := by
  simp only [colsV, NN, List.getD_cons_zero, List.getD_cons_succ]
  unfold N Cn
  omega

theorem kN_ok : ∀ j < 6, KOk (sumNKs.getD j []) j NN := by
  intro j hj s h
  obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  · show WP isa (.block (li64 .t0 .a6 C0)) s _
    rw [← List.append_nil (li64 .t0 .a6 C0)]
    exact wp_li64 (by decide) C0 fun s1 e1 k1 => WP.block_nil ⟨by rw [e1]; rfl, k1⟩
  · show WP isa (.block (li64 .t0 .a6 C1)) s _
    rw [← List.append_nil (li64 .t0 .a6 C1)]
    exact wp_li64 (by decide) C1 fun s1 e1 k1 => WP.block_nil ⟨by rw [e1]; rfl, k1⟩
  · show WP isa (.block (li64 .t0 .a6 C2)) s _
    rw [← List.append_nil (li64 .t0 .a6 C2)]
    exact wp_li64 (by decide) C2 fun s1 e1 k1 => WP.block_nil ⟨by rw [e1]; rfl, k1⟩
  · exact wp_li (imm := 0) (by decide) fun s1 u1 => WP.block_nil ⟨by rw [u1.gpr]; decide, (upd_keeps u1).mono⟩
  all_goals
    have h' : (s.gpr .t0).toNat = 0 := by
      rcases h with h | h
      · omega
      · exact h
    exact WP.block_nil ⟨h', ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The words of `n`. -/
def PWn (j : Nat) : Nat :=
  [0xecec196accc52973, 0x581a0db248b0a77a, 0xc7634d81f4372ddf, 2 ^ 64 - 1, 2 ^ 64 - 1, 2 ^ 64 - 1].getD j 0

theorem PWn_lt (j : Nat) : PWn j < 2 ^ 64 := by
  unfold PWn
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp

theorem PWn_val : colsV PWn 6 = N := by
  simp only [colsV, PWn, List.getD_cons_zero, List.getD_cons_succ]
  unfold N Cn
  omega

/-- `li64 a6 a0 w` and `a6 ∧ t0`, for a mask in `t0`. -/
theorem kmW (w : BitVec 64) {s : State} (hm : IsMask (s.gpr .t0)) :
    WP isa (.block (li64 .a6 .a0 w ++ ([.logic .and .a6 .a6 .t0] : List Instr))) s fun s' =>
      (s'.gpr .a6).toNat = (if s.gpr .t0 = BitVec.allOnes 64 then w.toNat else 0) ∧ Keeps [.a6, .a0] s s' := by
  refine wp_li64 (by decide) w fun s1 e1 k1 => wp_and fun s2 u2 => WP.block_nil ⟨?_, ?_⟩
  · rw [u2.gpr, e1, k1.1 .t0 (by decide)]
    rcases hm with h | h <;> rw [h]
    · simp
    · simp only [BitVec.and_allOnes, ↓reduceIte]
  · exact (k1.trans (upd_keeps u2)).mono fun x hx => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h <;> simp [h]

theorem kmN_ok : ∀ j < 6, KMOk (subNKs.getD j []) j PWn := by
  intro j hj s hm
  obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  · exact kmW N0 hm
  · exact kmW N1 hm
  · exact kmW N2 hm
  all_goals exact wp_addi (imm := 0) (by decide) fun s1 u1 => WP.block_nil ⟨by
      rw [u1.gpr]; rcases hm with h | h <;> rw [h] <;> decide, (upd_keeps u1).mono⟩

/-! ## The operations -/

theorem N_pos : 0 < N := by unfold N Cn; omega

/-- Montgomery's product modulo `n`. -/
abbrev mulRes (A B r : Nat) : Prop := r < N ∧ r * 2 ^ 384 % N = A * B % N

theorem mulCore_core : CoreOk Impl.Weierstrass.RISCV64.P384Order.mulCore (fun _ B => B < N) mulRes :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB =>
    WP.mono (mulWith_ok (red := Impl.Weierstrass.RISCV64.P384Order.reduce) (ks := sumNKs) N_pos NN_lt kN_ok
      NN_val (fun hc => WP.mono (reduceWith_ok qOkN N_add_Cn hc) fun _ ⟨c, r, f, x, q⟩ =>
        ⟨c, r.mono (by decide), f, x, q⟩) hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB)
      fun _ ⟨v1, v2, f, g, rd, wr, sp⟩ => ⟨⟨v1, v2⟩, f, g, rd, wr, sp⟩

theorem addCore_core : CoreOk (.block Impl.Weierstrass.RISCV64.P384Order.addCore) (fun A B => A + B < 2 * N)
    (fun A B r => r = (A + B) % N) := by
  intro W s a bb o hw h4 h5 h2 ha8 hb8 ho8 ha hb ho _ hab
  unfold Impl.Weierstrass.RISCV64.P384Order.addCore Impl.Weierstrass.RISCV64.P384Order.csub
  refine WP.block_append (WP.mono (addSum_ok hw h4 h5 ha8 hb8 ha hb) fun s1 ⟨v1, c1, r1, m1⟩ => ?_)
  have hw1 : WsAt W s1 := hw.of_rest r1 (by decide)
  refine WP.mono (csubWith_ok NN_lt kN_ok NN_val (O := W + BitVec.ofNat 64 o) (by rw [r1.gpr _ (by decide), h2])
    (al8 hw.al ho8) (hw1.inW ho) c1 (by rw [v1]; exact hab)) fun s2 ⟨v2, f2, g2, rd2, wr2, sp2⟩ => ?_
  refine ⟨by rw [v2, v1], by rw [← m1]; exact f2.mono (by simp), fun r hr => ?_, by rw [rd2, r1.rd],
    by rw [wr2, r1.wr], by rw [sp2, r1.sp]⟩
  have hC : r ∉ clobC := fun h => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h | h | h | h <;> simp [h])
  rw [g2 r hC, r1.gpr r hr]

theorem subCore_core : CoreOk (.block Impl.Weierstrass.RISCV64.P384Order.subCore) (fun A B => A < N ∧ B < N)
    (fun A B r => r = (A + N - B) % N) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho _ hAB =>
    WP.mono (subWith_ok (ks := subNKs) PWn_lt kmN_ok PWn_val hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hAB.1 hAB.2)
      fun _ ⟨v, f, g, rd, wr, sp⟩ => ⟨v, f.mono (by simp), g, rd, wr, sp⟩

end VG.Proof.Weierstrass.RISCV64.P384Order
