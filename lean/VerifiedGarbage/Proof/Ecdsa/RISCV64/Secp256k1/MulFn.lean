module

public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Secp256k1Field
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Secp256k1Field.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# secp256k1's field on RISC-V, for `vg_secp256k1_mul` and its callers

The facts the proofs of `vg_secp256k1_mul` (`Proof/Ecdsa/RISCV64/Secp256k1/Window.lean`)
and its callers share: secp256k1's field functions meet the contracts by register
(`field_ok`), and `R = 2²⁵⁶` is a unit modulo `p` (`unit`).
-/

@[expose] public section

/-!
## Arithmetic modulo `p`

The operations of `Impl/Weierstrass/RISCV64/Secp256k1Field.lean` meet
`CoreOk` (`mulCore_core`, `addCore_core`, `subCore_core`) as `Gen4`'s do, by
the lemmas of P-256's field, from the reduction (`reduce_ok`), the sum
`x + c` (`sum_ok`) and `p`'s words under a mask (`kW`, `kP0`).

The reduction keeps `Gen4`'s invariant (`RedInv`, with `p`, and `KInv` with
the constants in `t0` and `a6`) and adds `q p` in
a round (`round_ok`) as `q 2²⁵⁶ - q c`: the low word of `q c` is the round's
low word (`low_eq`), so the quotient `q`, the high word `h` of `q c`,
`h` subtracted with its borrow through three words (`bor_ok`), and `q` less
the borrow added into the top word (`Gen4.top_ok`) add up (`round_arith`).
Then `mul_rv`, `add_rv` and `sub_rv` give the contracts by register, as
`Gen4`'s.
-/

namespace VG.Proof.Weierstrass.RISCV64.Secp256k1Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide
open VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Impl.Weierstrass.RISCV64.Secp256k1Field (c sum)
open VG.Proof.Weierstrass.RISCV64.P256Field
open VG.Proof.Weierstrass.RISCV64.P256Order (wp_li64 wp_mulhu rw_ne ofNat_lt add_toNat kp idx pow64_succ kW)
open VG.Proof.Weierstrass.RISCV64.Gen4 (wd wd_lt words4 Ok mont_mod round_val prod_le top_ok RedInv loads_ok
  sum_arith)
open VG.Proof.X25519.RISCV64 (Ctx Rest wp_mul)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok clob64 Keeps.rest)
open VG.Impl.Words.RISCV64 (li64)

abbrev P : Nat := Spec.Secp256k1.p

theorem p_eq : P = 2 ^ 256 - c := by decide

theorem p_ok : Ok P := ⟨by decide, by decide, by decide⟩

theorem ni_eq : (BitVec.ofNat 64 (Impl.Weierstrass.RISCV64.Gen4.negInv P)).toNat =
    Impl.Weierstrass.RISCV64.Gen4.negInv P % 2 ^ 64 := BitVec.toNat_ofNat _ _

/-! ## Arithmetic -/

/-- The low word of `q c` is `w`, for the quotient word `q` of `w`. -/
theorem low_eq {w q : Nat} (hw : w < 2 ^ 64) (h0 : (w + q * wd P 0) % 2 ^ 64 = 0) :
    q * c = w + 2 ^ 64 * (q * c / 2 ^ 64) := by
  have e : wd P 0 = 2 ^ 64 - c := by decide
  rw [e] at h0
  have hs : q * (2 ^ 64 - c) + q * c = 2 ^ 64 * q := by
    rw [← Nat.mul_add, show 2 ^ 64 - c + c = 2 ^ 64 by decide, Nat.mul_comm]
  have := Nat.div_add_mod (q * c) (2 ^ 64)
  generalize q * (2 ^ 64 - c) = Y at *
  generalize q * c = X at *
  omega

/-- The numbers of a round. -/
theorem round_arith {q w0 w1 w2 w3 w4 cy U h b1 b2 b3 w1' w2' w3' w4' cy' : Nat}
    (hqc : q * c = w0 + 2 ^ 64 * h) (hqp : q * P + q * c = 2 ^ 256 * q)
    (B1 : w1' + h = w1 + 2 ^ 64 * b1) (B2 : w2' + b1 = w2 + 2 ^ 64 * b2) (B3 : w3' + b2 = w3 + 2 ^ 64 * b3)
    (hb : b3 ≤ q) (F4 : w4' + 2 ^ 64 * cy' = w4 + (q - b3) + cy) :
    2 ^ 64 * (w1' + 2 ^ 64 * w2' + 2 ^ 128 * w3' + 2 ^ 192 * w4' + 2 ^ 256 * (cy' + U)) =
      w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3 + 2 ^ 256 * (cy + (w4 + 2 ^ 64 * U)) + q * P := by
  omega

/-! ## Steps -/

set_option linter.unusedSimpArgs false in
/-- `x := x - y` and its borrow into `b`. -/
theorem bor_ok {x y b : Reg} (hxy : x ≠ y) (hxb : x ≠ b) (hyb : y ≠ b) {s : State} :
    WP isa (.block [.sltu b x y, .sub x x y]) s fun s' =>
      (s'.gpr x).toNat + (s.gpr y).toNat = (s.gpr x).toNat + 2 ^ 64 * (s'.gpr b).toNat ∧
      (s'.gpr b).toNat ≤ 1 ∧ s'.gpr y = s.gpr y ∧ Keeps [x, b] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_sub, exec_sltu,
    RegUpd.gpr_write, hxy, hxb, hyb, Ne.symm hxy, Ne.symm hxb, Ne.symm hyb, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [sub_borrow, sltu_toNat]
  · rw [sltu_toNat]; split <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-! ## The reduction -/

/-- `m'` in `t0`. -/
abbrev NI : BitVec 64 := BitVec.ofNat 64 (Impl.Weierstrass.RISCV64.Gen4.negInv P)

/-- `c` in `a6`. -/
abbrev CV : BitVec 64 := BitVec.ofNat 64 c

/-- `Gen4`'s invariant, with `m'` in `t0` and `c` in `a6`. -/
structure KInv (b : Addr) (s0 : State) (i : Nat) (s : State) : Prop where
  red : RedInv P b s0 i s
  t0 : s.gpr .t0 = NI
  a6 : s.gpr .a6 = CV

theorem cv_toNat : CV.toNat = c := by decide

/-- Round `i`. -/
theorem round_ok {b : Addr} {s0 : State} {i : Nat} (hi : i < 4) {s : State} (h : KInv b s0 i s) :
    WP isa (.block (Impl.Weierstrass.RISCV64.Secp256k1Field.round i)) s (KInv b s0 (i + 1)) := by
  obtain ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34, dk⟩ := rw_facts i hi
  obtain ⟨n02, n04, n05, n06, n07, n0t, n03, c0⟩ := dk 0 (by decide)
  obtain ⟨n12, n14, n15, n16, n17, n1t, n13, c1⟩ := dk 1 (by decide)
  obtain ⟨n22, n24, n25, n26, n27, n2t, n23, c2⟩ := dk 2 (by decide)
  obtain ⟨n32, n34, n35, n36, n37, n3t, n33, c3⟩ := dk 3 (by decide)
  obtain ⟨n42, n44, n45, n46, n47, n4t, n43, c4⟩ := dk 4 (by decide)
  simp only [Nat.add_zero] at n02 n04 n05 n06 n07 n0t n03 c0
  have hc := h.red.ctx
  have hd : ACC + 8 * (i + 4) + 8 ≤ 2048 := by simp only [ACC]; omega
  unfold Impl.Weierstrass.RISCV64.Secp256k1Field.round
  show WP isa (.block (.load .d (rw (i + 4)) .a3 (ACC + 8 * (i + 4)) :: .mul (rw i) (rw i) .t0 ::
    .mulhu .a4 (rw i) .a6 :: ([.sltu .a5 (rw (i + 1)) .a4, .sub (rw (i + 1)) (rw (i + 1)) .a4] ++
    ([.sltu .a7 (rw (i + 2)) .a5, .sub (rw (i + 2)) (rw (i + 2)) .a5] ++
    ([.sltu .a5 (rw (i + 3)) .a7, .sub (rw (i + 3)) (rw (i + 3)) .a7] ++
    (.sub .a4 (rw i) .a5 :: Impl.Weierstrass.RISCV64.Gen4.top (rw (i + 4)))))))) s _
  refine ld_ok hc hd (by simp only [ACC]; omega) fun s1 u1 => ?_
  refine wp_mul fun s2 u2 => wp_mulhu fun s3 u3 => ?_
  refine WP.block_append (WP.mono (bor_ok (x := rw (i + 1)) (y := .a4) (b := .a5) n14 n15 (by decide))
    fun s4 ⟨B1, b1, _, k4⟩ => ?_)
  refine WP.block_append (WP.mono (bor_ok (x := rw (i + 2)) (y := .a5) (b := .a7) n25 n27 (by decide))
    fun s5 ⟨B2, b2, _, k5⟩ => ?_)
  refine WP.block_append (WP.mono (bor_ok (x := rw (i + 3)) (y := .a7) (b := .a5) n37 n35 (by decide))
    fun s6 ⟨B3, b3, _, k6⟩ => ?_)
  refine wp_sub fun s7 u7 => ?_
  refine WP.mono (top_ok (d := rw (i + 4)) (by simp [n42, n44, n47])) fun s8 ⟨e8, k8⟩ => ?_
  have k1 := upd_keeps u1
  have k2 := upd_keeps u2
  have k3 := upd_keeps u3
  have k7 := upd_keeps u7
  -- What each step read.
  have hT4 : (s1.gpr (rw (i + 4))).toNat = T s0.mem b (i + 4) := by
    rw [u1.gpr, ← h.red.mem]; rfl
  have q2 : (s2.gpr (rw i)).toNat = (s.gpr (rw i)).toNat * (Impl.Weierstrass.RISCV64.Gen4.negInv P % 2 ^ 64) %
      2 ^ 64 := by
    rw [u2.gpr, BitVec.toNat_mul, kp k1 (by simp [d04]), kp k1 (by simp [Ne.symm n4t]), h.t0, ni_eq]
  have a6_2 : s2.gpr .a6 = CV := by
    rw [kp k2 (by simp [Ne.symm n06]), kp k1 (by simp [Ne.symm n46]), h.a6]
  have hq := (s2.gpr (rw i)).isLt
  have hh : (s3.gpr .a4).toNat = (s2.gpr (rw i)).toNat * c / 2 ^ 64 := by
    rw [u3.gpr, a6_2, cv_toNat]
    exact ofNat_lt (Nat.div_lt_of_lt_mul (by simp only [c]; omega))
  have w1 : s3.gpr (rw (i + 1)) = s.gpr (rw (i + 1)) := by
    rw [kp k3 (by simp [n14]), kp k2 (by simp [Ne.symm d01]), kp k1 (by simp [d14])]
  have w2 : s4.gpr (rw (i + 2)) = s.gpr (rw (i + 2)) := by
    rw [kp k4 (by simp [Ne.symm d12, n25]), kp k3 (by simp [n24]), kp k2 (by simp [Ne.symm d02]),
      kp k1 (by simp [d24])]
  have w3 : s5.gpr (rw (i + 3)) = s.gpr (rw (i + 3)) := by
    rw [kp k5 (by simp [Ne.symm d23, n37]), kp k4 (by simp [Ne.symm d13, n35]), kp k3 (by simp [n34]),
      kp k2 (by simp [Ne.symm d03]), kp k1 (by simp [d34])]
  have q6 : s6.gpr (rw i) = s2.gpr (rw i) := by
    rw [kp k6 (by simp [d03, n05]), kp k5 (by simp [d02, n07]), kp k4 (by simp [d01, n05]),
      kp k3 (by simp [n04])]
  have w4 : s7.gpr (rw (i + 4)) = s1.gpr (rw (i + 4)) := by
    rw [kp k7 (by simp [n44]), kp k6 (by simp [Ne.symm d34, n45]), kp k5 (by simp [Ne.symm d24, n47]),
      kp k4 (by simp [Ne.symm d14, n45]), kp k3 (by simp [n44]), kp k2 (by simp [Ne.symm d04])]
  have cy7 : s7.gpr .a2 = s.gpr .a2 := by
    rw [kp k7 (by simp), kp k6 (by simp [Ne.symm n32]), kp k5 (by simp [Ne.symm n22]),
      kp k4 (by simp [Ne.symm n12]), kp k3 (by simp), kp k2 (by simp [Ne.symm n02]),
      kp k1 (by simp [Ne.symm n42])]
  rw [w1, hh] at B1
  rw [w2] at B2
  rw [w3] at B3
  obtain ⟨F4, cy8⟩ := e8 (by rw [cy7]; exact h.red.cy)
  rw [w4, hT4, cy7, u7.gpr, q6, BitVec.toNat_sub] at F4
  -- The new registers, read from the last state.
  have o1 : s8.gpr (rw (i + 1)) = s4.gpr (rw (i + 1)) := by
    rw [kp k8 (by simp [d14, n12, n17]), kp k7 (by simp [n14]), kp k6 (by simp [d13, n15]),
      kp k5 (by simp [d12, n17])]
  have o2 : s8.gpr (rw (i + 2)) = s5.gpr (rw (i + 2)) := by
    rw [kp k8 (by simp [d24, n22, n27]), kp k7 (by simp [n24]), kp k6 (by simp [d23, n25])]
  have o3 : s8.gpr (rw (i + 3)) = s6.gpr (rw (i + 3)) := by
    rw [kp k8 (by simp [d34, n32, n37]), kp k7 (by simp [n34])]
  have t8 : s8.gpr .t0 = s.gpr .t0 := by
    rw [kp k8 (by simp [Ne.symm n4t]), kp k7 (by simp), kp k6 (by simp [Ne.symm n3t]), kp k5 (by simp [Ne.symm n2t]),
      kp k4 (by simp [Ne.symm n1t]), kp k3 (by simp), kp k2 (by simp [Ne.symm n0t]),
      kp k1 (by simp [Ne.symm n4t])]
  have a68 : s8.gpr .a6 = s.gpr .a6 := by
    rw [kp k8 (by simp [Ne.symm n46]), kp k7 (by simp), kp k6 (by simp [Ne.symm n36]),
      kp k5 (by simp [Ne.symm n26]), kp k4 (by simp [Ne.symm n16]), kp k3 (by simp),
      kp k2 (by simp [Ne.symm n06]), kp k1 (by simp [Ne.symm n46])]
  -- The frame.
  have sub : ∀ r ∈ clob64, r ∈ clobM := by decide
  have cons : ∀ {r : Reg} {l : List Reg}, r ∈ clob64 → (∀ x ∈ l, x ∈ clobM) → ∀ x ∈ r :: l, x ∈ clobM :=
    fun hr hl x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact sub _ hr
      · exact hl x hx
  have hrest : Rest clobM s s8 :=
    ((Keeps.rest k1).mono (cons c4 (by decide))).trans <| ((Keeps.rest k2).mono (cons c0 (by decide))).trans <|
      ((Keeps.rest k3).mono (by decide)).trans <| ((Keeps.rest k4).mono (cons c1 (by decide))).trans <|
      ((Keeps.rest k5).mono (cons c2 (by decide))).trans <| ((Keeps.rest k6).mono (cons c3 (by decide))).trans <|
      ((Keeps.rest k7).mono (by decide)).trans ((Keeps.rest k8).mono (cons c4 (by decide)))
  have hmem : s8.mem = s0.mem := by
    rw [k8.2.1, k7.2.1, k6.2.1, k5.2.1, k4.2.1, k3.2.1, k2.2.1, k1.2.1, h.red.mem]
  -- The numbers.
  have hw0 := (s.gpr (rw i)).isLt
  have hw1 := (s.gpr (rw (i + 1))).isLt
  have hw2 := (s.gpr (rw (i + 2))).isLt
  have hw3 := (s.gpr (rw (i + 3))).isLt
  have hy1 := (s4.gpr (rw (i + 1))).isLt
  have hy2 := (s5.gpr (rw (i + 2))).isLt
  have hy3 := (s6.gpr (rw (i + 3))).isLt
  have h0 := mont_mod p_ok.inv (s.gpr (rw i)).toNat
  rw [← q2] at h0
  have hqc := low_eq hw0 h0
  have hqp : (s2.gpr (rw i)).toNat * P + (s2.gpr (rw i)).toNat * c = 2 ^ 256 * (s2.gpr (rw i)).toNat := by
    rw [← Nat.mul_add, show P + c = 2 ^ 256 by decide, Nat.mul_comm]
  generalize (s2.gpr (rw i)).toNat = q at hq hqc hqp F4 B1 q2
  have hb : (s6.gpr .a5).toNat ≤ q := by
    simp only [c] at hqc
    omega
  rw [show (2 ^ 64 - (s6.gpr .a5).toNat + q) % 2 ^ 64 = q - (s6.gpr .a5).toNat by omega] at F4
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := idx i
  have hup : upW s0.mem b (i + 4) (4 - i) = T s0.mem b (i + 4) + 2 ^ 64 * upW s0.mem b (i + 5) (3 - i) := by
    rw [i6 hi]; rfl
  have key : 2 ^ 64 * wv s0.mem b (i + 1) s8 = wv s0.mem b i s + q * P := by
    simp only [wv, i1, i2, i3, i4, i5 hi, hup, o1, o2, o3]
    exact round_arith hqc hqp B1 B2 B3 hb F4
  obtain ⟨Q, hQ, hv⟩ := h.red.val
  obtain ⟨v1, v2⟩ := round_val hQ hq hv key
  exact ⟨⟨hc.of_rest hrest (by decide), h.red.rest.trans hrest, hmem, cy8,
    ⟨Q + q * 2 ^ (64 * i), by rw [pow64_succ]; exact v1, by rw [pow64_succ]; exact v2⟩⟩,
    by rw [t8, h.t0], by rw [a68, h.a6]⟩

/-- The rounds, by induction. -/
theorem rounds_ok {b : Addr} {s0 : State} : ∀ n ≤ 4, ∀ s, KInv b s0 0 s →
    WP isa (.block ((List.range n).flatMap Impl.Weierstrass.RISCV64.Secp256k1Field.round)) s (KInv b s0 n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (rounds_ok n (by omega) s h) fun s1 h1 => round_ok (by omega) h1)

/-- The invariant, across steps that keep the words and the carry. -/
theorem red_keeps {b : Addr} {s0 s s' : State} {i : Nat} {rs : List Reg} (h : RedInv P b s0 i s)
    (k : Keeps rs s s') (hc : ∀ r ∈ rs, r ∈ clobM) (hw : ∀ j, rw j ∉ rs) (h2 : Reg.a2 ∉ rs) :
    RedInv P b s0 i s' := by
  have hr : Rest clobM s s' := (Keeps.rest k).mono hc
  refine ⟨h.ctx.of_rest hr (by decide), h.rest.trans hr, by rw [k.2.1, h.mem], by rw [kp k h2]; exact h.cy, ?_⟩
  obtain ⟨Q, hQ, hv⟩ := h.val
  have e : ∀ j, s'.gpr (rw j) = s.gpr (rw j) := fun j => kp k (hw j)
  refine ⟨Q, hQ, ?_⟩
  simp only [wv, e, kp k h2]
  exact hv

theorem rw_ne_t0 (j : Nat) : rw j ∉ [Reg.t0, .a0] := by
  have := rw_ne j
  simp [this.1, this.2.1]

theorem rw_ne_a6 (j : Nat) : rw j ∉ [Reg.a6, .a0] := by
  have := rw_ne j
  simp [this.2.2.2.2.2.2.1, this.2.1]

/-- `reduce`: as `Gen4`'s. -/
theorem reduce_ok {b : Addr} {s : State} (hc : Ctx b s) :
    WP isa (.block Impl.Weierstrass.RISCV64.Secp256k1Field.reduce) s fun s' =>
      Ctx b s' ∧ Rest clobM s s' ∧ s'.mem = s.mem ∧ (s'.gpr XC).toNat ≤ 1 ∧
      ∃ Q, Q < 2 ^ 256 ∧
        ((s'.gpr X0).toNat + 2 ^ 64 * (s'.gpr X1).toNat + 2 ^ 128 * (s'.gpr X2).toNat +
          2 ^ 192 * (s'.gpr X3).toNat + 2 ^ 256 * (s'.gpr XC).toNat) * 2 ^ 256 = prodV s.mem b + Q * P := by
  unfold Impl.Weierstrass.RISCV64.Secp256k1Field.reduce
  simp only [List.append_assoc]
  rw [← List.append_assoc]
  refine WP.block_append (WP.mono (loads_ok (m := P) hc) fun s1 h1 => ?_)
  refine wp_li64 (by decide) _ fun s2 e2 k2 => wp_li64 (by decide) _ fun s3 e3 k3 => ?_
  have h3 : KInv b s 0 s3 :=
    ⟨red_keeps (red_keeps h1 k2 (by decide) rw_ne_t0 (by decide)) k3 (by decide) rw_ne_a6 (by decide),
      by rw [kp k3 (by decide), e2], e3⟩
  refine WP.mono (rounds_ok 4 (Nat.le_refl _) s3 h3) fun s4 h4 => ?_
  obtain ⟨Q, hQ, hv⟩ := h4.red.val
  refine ⟨h4.red.ctx, h4.red.rest, h4.red.mem, h4.red.cy, Q, by simpa using hQ, ?_⟩
  simpa [wv, upW, X0, X1, X2, X3, XC, rw, RW] using hv

/-! ## The final subtraction -/

set_option linter.unusedSimpArgs false in
/-- `d + 2⁶⁴ c := x + y`. -/
theorem addc_ok {d x y c : Reg} (hdy : d ≠ y) (hdc : d ≠ c) {s : State} :
    WP isa (.block [.add d x y, .sltu c d y]) s fun s' =>
      (s'.gpr d).toNat + 2 ^ 64 * (s'.gpr c).toNat = (s.gpr x).toNat + (s.gpr y).toNat ∧
      (s'.gpr c).toNat ≤ 1 ∧ Keeps [d, c] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, hdy, hdc, Ne.symm hdy, Ne.symm hdc, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨carry _ _, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [sltu_toNat]; split <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- `x + c` into `t6`, `a4`–`a6`, its carry into `a7`. -/
theorem sum_ok {s : State} :
    WP isa (.block sum) s fun s' =>
      v4 s' .t6 .a4 .a5 .a6 + 2 ^ 256 * (s'.gpr .a7).toNat = v4 s X0 X1 X2 X3 + (2 ^ 256 - P) ∧
      (s'.gpr .a7).toNat ≤ 1 ∧ Keeps clobC s s' := by
  unfold sum
  refine wp_li64 (by decide) _ fun s1 e1 k1 => ?_
  show WP isa (.block ([.add .t6 X0 .t0, .sltu .a7 .t6 .t0] ++ ([.add .a4 X1 .a7, .sltu .a7 .a4 .a7] ++
    ([.add .a5 X2 .a7, .sltu .a7 .a5 .a7] ++ [.add .a6 X3 .a7, .sltu .a7 .a6 .a7])))) s1 _
  refine WP.block_append (WP.mono (addc_ok (d := .t6) (x := X0) (y := .t0) (c := .a7) (by decide) (by decide))
    fun s2 ⟨f2, _, k2⟩ => ?_)
  refine WP.block_append (WP.mono (addc_ok (d := .a4) (x := X1) (y := .a7) (c := .a7) (by decide) (by decide))
    fun s3 ⟨f3, _, k3⟩ => ?_)
  refine WP.block_append (WP.mono (addc_ok (d := .a5) (x := X2) (y := .a7) (c := .a7) (by decide) (by decide))
    fun s4 ⟨f4, _, k4⟩ => ?_)
  refine WP.mono (addc_ok (d := .a6) (x := X3) (y := .a7) (c := .a7) (by decide) (by decide))
    fun s5 ⟨f5, b5, k5⟩ => ?_
  rw [kp k1 (by decide), e1, cv_toNat] at f2
  rw [kp k2 (by decide), kp k1 (by decide)] at f3
  rw [kp k3 (by decide), kp k2 (by decide), kp k1 (by decide)] at f4
  rw [kp k4 (by decide), kp k3 (by decide), kp k2 (by decide), kp k1 (by decide)] at f5
  have o0 : s5.gpr .t6 = s2.gpr .t6 := by rw [kp k5 (by decide), kp k4 (by decide), kp k3 (by decide)]
  have o1 : s5.gpr .a4 = s3.gpr .a4 := by rw [kp k5 (by decide), kp k4 (by decide)]
  have o2 : s5.gpr .a5 = s4.gpr .a5 := kp k5 (by decide)
  refine ⟨?_, b5, ((((k1.trans k2).trans k3).trans k4).trans k5).mono⟩
  simp only [v4, o0, o1, o2, show 2 ^ 256 - P = c by decide]
  omega

/-! ## The operations -/

theorem k0_ok : KOk (li64 .t6 .a0 (BitVec.ofNat 64 (2 ^ 64 - c)) ++ ([.logic .and .t6 .t6 .t0] : List Instr)) (2 ^ 64 - c) := by
  have h := kW (BitVec.ofNat 64 (2 ^ 64 - c))
  rw [show (BitVec.ofNat 64 (2 ^ 64 - c)).toNat = 2 ^ 64 - c by decide] at h
  exact h

theorem mulCore_core : CoreOk Impl.Weierstrass.RISCV64.Secp256k1Field.mulCore (fun _ B => B < P) (Gen4.mulRes P) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB =>
    WP.mono (mulWith_ok p_ok.pos (Nat.le_of_lt p_ok.lt) reduce_ok (fun _ => sum_ok) hw h4 h5 h2 ha8 hb8
      ho8 ha hb ho hdb hB) fun _ ⟨v1, v2, f, g, rd, wr, sp⟩ => ⟨⟨v1, v2⟩, f, g, rd, wr, sp⟩

theorem addCore_core :
    CoreOk (.block Impl.Weierstrass.RISCV64.Secp256k1Field.addCore) (fun A B => A + B < 2 * P) (fun A B r => r = (A + B) % P) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho _ hAB =>
    WP.mono (addWith_ok (sum := sum) (Nat.le_of_lt p_ok.lt) (fun _ => sum_ok) hw h4 h5 h2 ha8 hb8 ho8 ha
      hb ho hAB) fun _ ⟨v, f, g, rd, wr, sp⟩ => ⟨v, f.mono (by simp), g, rd, wr, sp⟩

theorem subCore_core :
    CoreOk (.block Impl.Weierstrass.RISCV64.Secp256k1Field.subCore) (fun A B => A < P ∧ B < P) (fun A B r => r = (A + P - B) % P) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho _ hAB =>
    WP.mono (subWith_ok (m0 := 2 ^ 64 - c) (m1 := 2 ^ 64 - 1) (m2 := 2 ^ 64 - 1) (m3 := 2 ^ 64 - 1)
      (by decide) (by decide) (by decide) (by decide) (by decide) k0_ok kP0 kP0 kP0
      hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hAB.1 hAB.2)
      fun _ ⟨v, f, g, rd, wr, sp⟩ => ⟨v, f.mono (by simp), g, rd, wr, sp⟩

/-! ## The contracts -/

open VG.Proof.Weierstrass.RISCV64 (res mulRV addRV subRV)

variable {S : Impl.Weierstrass.Mont.Modulus}

theorem mul_rv (hk : S.k = 4) (hp : S.m = P) (s : State) (hs : (mulRV S).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.Secp256k1Field.mulFn s t s' ∧ abiPreserved s s' ∧ (mulRV S).post s s' := by
  have hc : CoreOk Impl.Weierstrass.RISCV64.Secp256k1Field.mulCore (fun _ B => B < S.m) (Gen4.mulRes S.m) := by rw [hp]; exact mulCore_core
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := Gen4.fn_rv hk @hc hs.1 (by exact hs.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v1,
    by rw [res, Impl.Weierstrass.Mont.Modulus.R, hk]; exact v2, by rw [hk]; exact k⟩

theorem add_rv (hk : S.k = 4) (hp : S.m = P) (s : State) (hs : (addRV S).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.Secp256k1Field.addFn s t s' ∧ abiPreserved s s' ∧ (addRV S).post s s' := by
  have hc : CoreOk (.block Impl.Weierstrass.RISCV64.Secp256k1Field.addCore) (fun A B => A + B < 2 * S.m) (fun A B r => r = (A + B) % S.m) := by
    rw [hp]; exact addCore_core
  obtain ⟨t, s', he, a, v, k⟩ := Gen4.fn_rv hk @hc hs.1 (by exact hs.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

theorem sub_rv (hk : S.k = 4) (hp : S.m = P) (s : State) (hs : (subRV S).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.Secp256k1Field.subFn s t s' ∧ abiPreserved s s' ∧ (subRV S).post s s' := by
  have hc : CoreOk (.block Impl.Weierstrass.RISCV64.Secp256k1Field.subCore) (fun A B => A < S.m ∧ B < S.m) (fun A B r => r = (A + S.m - B) % S.m) := by
    rw [hp]; exact subCore_core
  obtain ⟨t, s', he, a, v, k⟩ := Gen4.fn_rv hk @hc hs.1 (by exact hs.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

theorem mulA_rv (hk : S.k = 4) (hp : S.m = P) (s : State)
    (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV S)).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.Secp256k1Field.mulFnA s t s' ∧ abiPreserved s s' ∧ (mulRV S).post s s' := by
  have hc : CoreOk Impl.Weierstrass.RISCV64.Secp256k1Field.mulCore (fun _ B => B < S.m) (Gen4.mulRes S.m) := by
    rw [hp]; exact mulCore_core
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := P256Field.fnA_rv hk @hc hs.1.1 hs.2 (by exact hs.1.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v1,
    by rw [res, Impl.Weierstrass.Mont.Modulus.R, hk]; exact v2, by rw [hk]; exact k⟩

theorem addA_rv (hk : S.k = 4) (hp : S.m = P) (s : State)
    (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV S)).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.Secp256k1Field.addFnA s t s' ∧ abiPreserved s s' ∧ (addRV S).post s s' := by
  have hc : CoreOk (.block Impl.Weierstrass.RISCV64.Secp256k1Field.addCore) (fun A B => A + B < 2 * S.m)
      (fun A B r => r = (A + B) % S.m) := by
    rw [hp]; exact addCore_core
  obtain ⟨t, s', he, a, v, k⟩ := P256Field.fnA_rv hk @hc hs.1.1 hs.2 (by exact hs.1.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

theorem subA_rv (hk : S.k = 4) (hp : S.m = P) (s : State)
    (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV S)).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.Secp256k1Field.subFnA s t s' ∧ abiPreserved s s' ∧ (subRV S).post s s' := by
  have hc : CoreOk (.block Impl.Weierstrass.RISCV64.Secp256k1Field.subCore) (fun A B => A < S.m ∧ B < S.m)
      (fun A B r => r = (A + S.m - B) % S.m) := by
    rw [hp]; exact subCore_core
  obtain ⟨t, s', he, a, v, k⟩ := P256Field.fnA_rv hk @hc hs.1.1 hs.2 (by exact hs.1.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

end VG.Proof.Weierstrass.RISCV64.Secp256k1Field

namespace VG.Proof.Ecdsa.RISCV64.Secp256k1

open VG VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- secp256k1. -/
abbrev W : Curve := Spec.Secp256k1.curve

theorem field_ok : FieldOk secp256k1Field :=
  ⟨VG.Proof.Weierstrass.RISCV64.Secp256k1Field.mul_rv rfl rfl, VG.Proof.Weierstrass.RISCV64.Secp256k1Field.add_rv rfl rfl, VG.Proof.Weierstrass.RISCV64.Secp256k1Field.sub_rv rfl rfl,
    Impl.Weierstrass.RISCV64.Secp256k1Field.mulFn_noFrames,
    Impl.Weierstrass.RISCV64.Secp256k1Field.addFn_noFrames, Impl.Weierstrass.RISCV64.Secp256k1Field.subFn_noFrames,
    VG.Proof.Weierstrass.RISCV64.Secp256k1Field.mulA_rv rfl rfl, VG.Proof.Weierstrass.RISCV64.Secp256k1Field.addA_rv rfl rfl, VG.Proof.Weierstrass.RISCV64.Secp256k1Field.subA_rv rfl rfl,
    Impl.Weierstrass.RISCV64.Secp256k1Field.mulFnA_noFrames,
    Impl.Weierstrass.RISCV64.Secp256k1Field.addFnA_noFrames, Impl.Weierstrass.RISCV64.Secp256k1Field.subFnA_noFrames⟩

instance : NeZero secp256k1Field.S.m := ⟨by decide⟩

theorem p_odd : W.p % 2 = 1 := by decide

theorem unit : UnitMod W.p (2 ^ (64 * 4)) := unitMod_pow_two p_odd _

/-- The number at slot `i`. -/
abbrev sv (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (secp256k1.sl i) 4

end VG.Proof.Ecdsa.RISCV64.Secp256k1
