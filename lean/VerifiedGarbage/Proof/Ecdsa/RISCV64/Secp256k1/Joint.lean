module

-- separate module: its proofs (about 7 s) cost more than its imports, and its importer's
-- changes need not re-check them
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Joint.Table
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.RISCV64.Ecdsa
public import VerifiedGarbage.Proof.Weierstrass.Joint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Secp256k1.Point
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law3
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Secp256k1Field
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Rows
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Secp256k1Field.Lit
import VerifiedGarbage.Proof.Framework.Apart

/-! ### `Ecdsa.RISCV64.Secp256k1.MulFn`, which this module and modules that import it used -/

section

/-!
# secp256k1's field on RISC-V, for `vg_secp256k1_mul` and its callers

The facts the proofs of `vg_secp256k1_mul` (`Proof/Ecdh/RISCV64/Secp256k1/Tail.lean`)
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
For aligned offsets, the product by rows is reduced in one pass
(`redTail_ok`, from `tail_nat`).

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

theorem p_ok : Ok P := ⟨by decide, by decide, by decide⟩

theorem ni_eq : (BitVec.ofNat 64 (Impl.Weierstrass.RISCV64.Gen4.negInv P)).toNat =
    Impl.Weierstrass.RISCV64.Gen4.negInv P % 2 ^ 64 := BitVec.toNat_ofNat _ _

/-! ## Arithmetic -/

/-- The low word of `q c` is `w`, for the quotient word `q` of `w`. -/
theorem low_eq {w q : Nat} (hw : w < 2 ^ 64) (h0 : (w + q * wd P 0) % 2 ^ 64 = 0) :
    q * c = w + 2 ^ 64 * (q * c / 2 ^ 64) := by
  obtain e : wd P 0 = 2 ^ 64 - c := by decide
  rw [e] at h0
  obtain hs : q * (2 ^ 64 - c) + q * c = 2 ^ 64 * q := by
    rw [← Nat.mul_add, show 2 ^ 64 - c + c = 2 ^ 64 by decide, Nat.mul_comm]
  have := Nat.div_add_mod (q * c) (2 ^ 64)
  generalize q * (2 ^ 64 - c) = Y at *
  generalize q * c = X at *
  omega_using [hw, h0, hs]

/-- The numbers of a round. -/
theorem round_arith {q w0 w1 w2 w3 w4 cy U h b1 b2 b3 w1' w2' w3' w4' cy' : Nat}
    (hqc : q * c = w0 + 2 ^ 64 * h) (hqp : q * P + q * c = 2 ^ 256 * q)
    (B1 : w1' + h = w1 + 2 ^ 64 * b1) (B2 : w2' + b1 = w2 + 2 ^ 64 * b2) (B3 : w3' + b2 = w3 + 2 ^ 64 * b3)
    (hb : b3 ≤ q) (F4 : w4' + 2 ^ 64 * cy' = w4 + (q - b3) + cy) :
    2 ^ 64 * (w1' + 2 ^ 64 * w2' + 2 ^ 128 * w3' + 2 ^ 192 * w4' + 2 ^ 256 * (cy' + U)) =
      w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3 + 2 ^ 256 * (cy + (w4 + 2 ^ 64 * U)) + q * P := by
  omega_using [hqc, hqp, B1, B2, B3, hb, F4]

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
  obtain hd : ACC + 8 * (i + 4) + 8 ≤ 2048 := by simp only [ACC]; omega_using [hi]
  unfold Impl.Weierstrass.RISCV64.Secp256k1Field.round
  show WP isa (.block (.load .d (rw (i + 4)) .a3 (ACC + 8 * (i + 4)) :: .mul (rw i) (rw i) .t0 ::
    .mulhu .a4 (rw i) .a6 :: ([.sltu .a5 (rw (i + 1)) .a4, .sub (rw (i + 1)) (rw (i + 1)) .a4] ++
    ([.sltu .a7 (rw (i + 2)) .a5, .sub (rw (i + 2)) (rw (i + 2)) .a5] ++
    ([.sltu .a5 (rw (i + 3)) .a7, .sub (rw (i + 3)) (rw (i + 3)) .a7] ++
    (.sub .a4 (rw i) .a5 :: Impl.Weierstrass.RISCV64.Gen4.top (rw (i + 4)))))))) s _
  refine ld_ok hc hd (by simp only [ACC]; omega_using []) fun s1 u1 => ?_
  refine wp_mul fun s2 u2 => wp_mulhu fun s3 u3 => ?_
  refine WP.block_append (WP.mono (bor_ok (x := rw (i + 1)) (y := .a4) (b := .a5) n14 n15 (by decide))
    fun s4 ⟨B1, b1, _, k4⟩ => ?_)
  refine WP.block_append (WP.mono (bor_ok (x := rw (i + 2)) (y := .a5) (b := .a7) n25 n27 (by decide))
    fun s5 ⟨B2, b2, _, k5⟩ => ?_)
  refine WP.block_append (WP.mono (bor_ok (x := rw (i + 3)) (y := .a7) (b := .a5) n37 n35 (by decide))
    fun s6 ⟨B3, b3, _, k6⟩ => ?_)
  refine wp_sub fun s7 u7 => ?_
  refine WP.mono (top_ok (d := rw (i + 4)) (by simp [n42, n44, n47])) fun s8 ⟨e8, k8⟩ => ?_
  obtain k1 := upd_keeps u1
  obtain k2 := upd_keeps u2
  obtain k3 := upd_keeps u3
  obtain k7 := upd_keeps u7
  -- What each step read.
  obtain hT4 : (s1.gpr (rw (i + 4))).toNat = T s0.mem b (i + 4) := by
    rw [u1.gpr, ← h.red.mem]; rfl
  obtain q2 : (s2.gpr (rw i)).toNat = (s.gpr (rw i)).toNat * (Impl.Weierstrass.RISCV64.Gen4.negInv P % 2 ^ 64) %
      2 ^ 64 := by
    rw [u2.gpr, BitVec.toNat_mul, kp k1 (by simp [d04]), kp k1 (by simp [Ne.symm n4t]), h.t0, ni_eq]
  obtain a6_2 : s2.gpr .a6 = CV := by
    rw [kp k2 (by simp [Ne.symm n06]), kp k1 (by simp [Ne.symm n46]), h.a6]
  obtain hq := (s2.gpr (rw i)).isLt
  obtain hh : (s3.gpr .a4).toNat = (s2.gpr (rw i)).toNat * c / 2 ^ 64 := by
    rw [u3.gpr, a6_2, cv_toNat]
    exact ofNat_lt (Nat.div_lt_of_lt_mul (by simp only [c]; omega_using []))
  obtain w1 : s3.gpr (rw (i + 1)) = s.gpr (rw (i + 1)) := by
    rw [kp k3 (by simp [n14]), kp k2 (by simp [Ne.symm d01]), kp k1 (by simp [d14])]
  obtain w2 : s4.gpr (rw (i + 2)) = s.gpr (rw (i + 2)) := by
    rw [kp k4 (by simp [Ne.symm d12, n25]), kp k3 (by simp [n24]), kp k2 (by simp [Ne.symm d02]),
      kp k1 (by simp [d24])]
  obtain w3 : s5.gpr (rw (i + 3)) = s.gpr (rw (i + 3)) := by
    rw [kp k5 (by simp [Ne.symm d23, n37]), kp k4 (by simp [Ne.symm d13, n35]), kp k3 (by simp [n34]),
      kp k2 (by simp [Ne.symm d03]), kp k1 (by simp [d34])]
  obtain q6 : s6.gpr (rw i) = s2.gpr (rw i) := by
    rw [kp k6 (by simp [d03, n05]), kp k5 (by simp [d02, n07]), kp k4 (by simp [d01, n05]),
      kp k3 (by simp [n04])]
  obtain w4 : s7.gpr (rw (i + 4)) = s1.gpr (rw (i + 4)) := by
    rw [kp k7 (by simp [n44]), kp k6 (by simp [Ne.symm d34, n45]), kp k5 (by simp [Ne.symm d24, n47]),
      kp k4 (by simp [Ne.symm d14, n45]), kp k3 (by simp [n44]), kp k2 (by simp [Ne.symm d04])]
  obtain cy7 : s7.gpr .a2 = s.gpr .a2 := by
    rw [kp k7 (by simp), kp k6 (by simp [Ne.symm n32]), kp k5 (by simp [Ne.symm n22]),
      kp k4 (by simp [Ne.symm n12]), kp k3 (by simp), kp k2 (by simp [Ne.symm n02]),
      kp k1 (by simp [Ne.symm n42])]
  rw [w1, hh] at B1
  rw [w2] at B2
  rw [w3] at B3
  obtain ⟨F4, cy8⟩ := e8 (by rw [cy7]; exact h.red.cy)
  rw [w4, hT4, cy7, u7.gpr, q6, BitVec.toNat_sub] at F4
  -- The new registers, read from the last state.
  obtain o1 : s8.gpr (rw (i + 1)) = s4.gpr (rw (i + 1)) := by
    rw [kp k8 (by simp [d14, n12, n17]), kp k7 (by simp [n14]), kp k6 (by simp [d13, n15]),
      kp k5 (by simp [d12, n17])]
  obtain o2 : s8.gpr (rw (i + 2)) = s5.gpr (rw (i + 2)) := by
    rw [kp k8 (by simp [d24, n22, n27]), kp k7 (by simp [n24]), kp k6 (by simp [d23, n25])]
  obtain o3 : s8.gpr (rw (i + 3)) = s6.gpr (rw (i + 3)) := by
    rw [kp k8 (by simp [d34, n32, n37]), kp k7 (by simp [n34])]
  obtain t8 : s8.gpr .t0 = s.gpr .t0 := by
    rw [kp k8 (by simp [Ne.symm n4t]), kp k7 (by simp), kp k6 (by simp [Ne.symm n3t]), kp k5 (by simp [Ne.symm n2t]),
      kp k4 (by simp [Ne.symm n1t]), kp k3 (by simp), kp k2 (by simp [Ne.symm n0t]),
      kp k1 (by simp [Ne.symm n4t])]
  obtain a68 : s8.gpr .a6 = s.gpr .a6 := by
    rw [kp k8 (by simp [Ne.symm n46]), kp k7 (by simp), kp k6 (by simp [Ne.symm n36]),
      kp k5 (by simp [Ne.symm n26]), kp k4 (by simp [Ne.symm n16]), kp k3 (by simp),
      kp k2 (by simp [Ne.symm n06]), kp k1 (by simp [Ne.symm n46])]
  -- The frame.
  obtain sub : ∀ r ∈ clob64, r ∈ clobM := by decide
  obtain cons : ∀ {r : Reg} {l : List Reg}, r ∈ clob64 → (∀ x ∈ l, x ∈ clobM) → ∀ x ∈ r :: l, x ∈ clobM :=
    fun hr hl x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact sub _ hr
      · exact hl x hx
  obtain hrest : Rest clobM s s8 :=
    ((Keeps.rest k1).mono (cons c4 (by decide))).trans <| ((Keeps.rest k2).mono (cons c0 (by decide))).trans <|
      ((Keeps.rest k3).mono (by decide)).trans <| ((Keeps.rest k4).mono (cons c1 (by decide))).trans <|
      ((Keeps.rest k5).mono (cons c2 (by decide))).trans <| ((Keeps.rest k6).mono (cons c3 (by decide))).trans <|
      ((Keeps.rest k7).mono (by decide)).trans ((Keeps.rest k8).mono (cons c4 (by decide)))
  obtain hmem : s8.mem = s0.mem := by
    rw [k8.2.1, k7.2.1, k6.2.1, k5.2.1, k4.2.1, k3.2.1, k2.2.1, k1.2.1, h.red.mem]
  -- The numbers.
  obtain hw0 := (s.gpr (rw i)).isLt
  obtain hw1 := (s.gpr (rw (i + 1))).isLt
  obtain hw2 := (s.gpr (rw (i + 2))).isLt
  obtain hw3 := (s.gpr (rw (i + 3))).isLt
  obtain hy1 := (s4.gpr (rw (i + 1))).isLt
  obtain hy2 := (s5.gpr (rw (i + 2))).isLt
  obtain hy3 := (s6.gpr (rw (i + 3))).isLt
  obtain h0 := mont_mod p_ok.inv (s.gpr (rw i)).toNat
  rw [← q2] at h0
  obtain hqc := low_eq hw0 h0
  obtain hqp : (s2.gpr (rw i)).toNat * P + (s2.gpr (rw i)).toNat * c = 2 ^ 256 * (s2.gpr (rw i)).toNat := by
    rw [← Nat.mul_add, show P + c = 2 ^ 256 by decide, Nat.mul_comm]
  generalize (s2.gpr (rw i)).toNat = q at hq hqc hqp F4 B1 q2
  obtain hb : (s6.gpr .a5).toNat ≤ q := by
    simp only [c] at hqc
    omega_using [b1, B2, b2, B3, b3, e8, hT4, hh, cy8, hw0, hw1, hw3, hy1, hy3, h0, hq, hqc, hqp, F4, B1, q2]
  rw [show (2 ^ 64 - (s6.gpr .a5).toNat + q) % 2 ^ 64 = q - (s6.gpr .a5).toNat by omega_using [hq, hb]] at F4
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := idx i
  obtain hup : upW s0.mem b (i + 4) (4 - i) = T s0.mem b (i + 4) + 2 ^ 64 * upW s0.mem b (i + 5) (3 - i) := by
    rw [i6 hi]; rfl
  obtain key : 2 ^ 64 * wv s0.mem b (i + 1) s8 = wv s0.mem b i s + q * P := by
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
    exact WP.block_append (WP.mono (rounds_ok n (by omega_using [hn]) s h) fun s1 h1 => round_ok (by omega_using [hn]) h1)

/-- The invariant, across steps that keep the words and the carry. -/
theorem red_keeps {b : Addr} {s0 s s' : State} {i : Nat} {rs : List Reg} (h : RedInv P b s0 i s)
    (k : Keeps rs s s') (hc : ∀ r ∈ rs, r ∈ clobM) (hw : ∀ j, rw j ∉ rs) (h2 : Reg.a2 ∉ rs) :
    RedInv P b s0 i s' := by
  obtain hr : Rest clobM s s' := (Keeps.rest k).mono hc
  refine ⟨h.ctx.of_rest hr (by decide), h.rest.trans hr, by rw [k.2.1, h.mem], by rw [kp k h2]; exact h.cy, ?_⟩
  obtain ⟨Q, hQ, hv⟩ := h.val
  obtain e : ∀ j, s'.gpr (rw j) = s.gpr (rw j) := fun j => kp k (hw j)
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
  obtain h3 : KInv b s 0 s3 :=
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
  obtain o0 : s5.gpr .t6 = s2.gpr .t6 := by rw [kp k5 (by decide), kp k4 (by decide), kp k3 (by decide)]
  obtain o1 : s5.gpr .a4 = s3.gpr .a4 := by rw [kp k5 (by decide), kp k4 (by decide)]
  obtain o2 : s5.gpr .a5 = s4.gpr .a5 := kp k5 (by decide)
  refine ⟨?_, b5, ((((k1.trans k2).trans k3).trans k4).trans k5).mono⟩
  simp only [v4, o0, o1, o2, show 2 ^ 256 - P = c by decide]
  omega_using [f2, f3, f4, f5]

/-! ## The operations -/

theorem k0_ok : KOk (li64 .t6 .a0 (BitVec.ofNat 64 (2 ^ 64 - c)) ++ ([.logic .and .t6 .t6 .t0] : List Instr)) (2 ^ 64 - c) := by
  obtain h := kW (BitVec.ofNat 64 (2 ^ 64 - c))
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

/-! ## The multiplication for aligned offsets -/

open VG.Impl.Weierstrass.RISCV64.Secp256k1Field (lay redTail qStep sumStep selStep loads quots sums cands sels order)
open VG.Proof.Weierstrass.RISCV64.GenWide (wp_xor' ov mont_nat)
open VG.Proof.X25519.RISCV64 (wp_and)
open VG.Proof.X448.RISCV64.R64 (al8 colsV dw_write_self dw_write_other)

theorem lay_ok : Rows.LOk lay :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `q c = w + 2⁶⁴ h` for the quotient word `q` of `w`. -/
theorem quot_eq {w q : BitVec 64} (h : q = w * NI) : q.toNat * c = w.toNat + 2 ^ 64 * (q.toNat * c / 2 ^ 64) := by
  refine low_eq w.isLt ?_
  obtain h0 := mont_mod p_ok.inv w.toNat
  rwa [← ni_eq, ← BitVec.toNat_mul, ← h] at h0

/-- A word of the quotient. -/
theorem qStep_ok {w : Reg} (hw : w ∉ [Reg.t3, .t5, .t6, .s8]) {s : State} (h5 : s.gpr .t5 = NI) (h7 : s.gpr .s8 = CV) :
    WP isa (.block (qStep w)) s fun s' =>
      (s'.gpr w).toNat * c + (s.gpr .t3).toNat = (s.gpr w).toNat + 2 ^ 64 * (s'.gpr .t3).toNat ∧
      (s'.gpr .t3).toNat ≤ c ∧ Keeps [w, .t3, .t6] s s' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
  obtain ⟨n3, n5, n6, n7⟩ := hw
  unfold qStep
  show WP isa (.block ([.sltu .t6 w .t3, .sub w w .t3] ++ ([.mul w w .t5, .mulhu .t3 w .s8, .add .t3 .t3 .t6] : List Instr))) s _
  refine WP.block_append (WP.mono (bor_ok (x := w) (y := .t3) (b := .t6) n3 n6 (by decide)) fun s1 ⟨B1, b1, _, k1⟩ => ?_)
  refine wp_mul fun s2 u2 => wp_mulhu fun s3 u3 => wp_add fun s4 u4 => WP.block_nil ?_
  obtain q2 : s2.gpr w = s1.gpr w * NI := by rw [u2.gpr, kp k1 (r := .t5) (by simp [Ne.symm n5]), h5]
  obtain hq := quot_eq q2
  obtain h3 : (s3.gpr .t3).toNat = (s2.gpr w).toNat * c / 2 ^ 64 := by
    rw [u3.gpr, u2.other _ (Ne.symm n7), kp k1 (r := .s8) (by simp [Ne.symm n7]), h7, cv_toNat]
    exact ofNat_lt (Nat.div_lt_of_lt_mul (by have := (s2.gpr w).isLt; simp only [c]; omega_using [this]))
  obtain w4 : s4.gpr w = s2.gpr w := by rw [u4.other _ n3, u3.other _ n3]
  obtain t6 : s3.gpr .t6 = s1.gpr .t6 := by rw [u3.other _ (by decide), u2.other _ (Ne.symm n6)]
  obtain lh : (s2.gpr w).toNat * c / 2 ^ 64 < c :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_right (s2.gpr w).isLt (by decide))
  obtain t4 : (s4.gpr .t3).toNat = (s2.gpr w).toNat * c / 2 ^ 64 + (s1.gpr .t6).toNat := by
    rw [u4.gpr, BitVec.toNat_add, h3, t6]
    exact Nat.mod_eq_of_lt (by simp only [c] at lh ⊢; omega_using [lh, b1])
  refine ⟨?_, by rw [t4]; omega_using [lh, b1],
    ((k1.trans (upd_keeps u2)).trans ((upd_keeps u3).trans (upd_keeps u4))).mono (by simp)⟩
  rw [w4, t4]
  omega_using [hq, B1]

/-- The quotient: `q c = L + 2²⁵⁶ h` for the product's low half `L`. -/
theorem quots_ok {s : State} (h5 : s.gpr .t5 = NI) (h7 : s.gpr .s8 = CV) :
    WP isa (.block quots) s fun s' =>
      v4 s' .a0 .a1 .a2 .a4 * c = v4 s .a0 .a1 .a2 .a4 + 2 ^ 256 * (s'.gpr .t3).toNat ∧ (s'.gpr .t3).toNat ≤ c ∧
      Keeps [.a0, .a1, .a2, .a4, .t3, .t6] s s' := by
  unfold quots
  simp only [List.cons_append, List.nil_append]
  refine wp_mul fun s1 u1 => wp_mulhu fun s2 u2 => ?_
  obtain q1 : s1.gpr .a0 = s.gpr .a0 * NI := by rw [u1.gpr, h5]
  obtain hq := quot_eq q1
  obtain lh : (s1.gpr .a0).toNat * c / 2 ^ 64 < c :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_right (s1.gpr .a0).isLt (by decide))
  obtain h3 : (s2.gpr .t3).toNat = (s1.gpr .a0).toNat * c / 2 ^ 64 := by
    rw [u2.gpr, u1.other .s8 (by decide), h7, cv_toNat]
    exact ofNat_lt (by simp only [c] at lh ⊢; omega_using [lh])
  rw [← h3] at hq lh
  obtain k2 : Keeps [.a0, .t3] s s2 := (upd_keeps u1).trans (upd_keeps u2)
  refine WP.block_append (WP.mono (qStep_ok (w := .a1) (by decide) (by rw [kp k2 (by decide), h5])
    (by rw [kp k2 (by decide), h7])) fun s3 ⟨e3, _, k3⟩ => ?_)
  obtain k3' := k2.trans k3
  refine WP.block_append (WP.mono (qStep_ok (w := .a2) (by decide) (by rw [kp k3' (by decide), h5])
    (by rw [kp k3' (by decide), h7])) fun s4 ⟨e4, _, k4⟩ => ?_)
  obtain k4' := k3'.trans k4
  refine WP.mono (qStep_ok (w := .a4) (by decide) (by rw [kp k4' (by decide), h5])
    (by rw [kp k4' (by decide), h7])) fun s5 ⟨e5, c5, k5⟩ => ?_
  rw [kp k2 (r := .a1) (by decide)] at e3
  rw [kp k3' (r := .a2) (by decide)] at e4
  rw [kp k4' (r := .a4) (by decide)] at e5
  obtain o0 : s5.gpr .a0 = s1.gpr .a0 := by
    rw [kp k5 (by decide), kp k4 (by decide), kp k3 (by decide), u2.other _ (by decide)]
  obtain o1 : s5.gpr .a1 = s3.gpr .a1 := by rw [kp k5 (by decide), kp k4 (by decide)]
  obtain o2 : s5.gpr .a2 = s4.gpr .a2 := kp k5 (by decide)
  refine ⟨?_, c5, (k4'.trans k5).mono⟩
  simp only [v4, o0, o1, o2, Nat.add_mul, Nat.mul_assoc]
  omega_using [hq, e3, e4, e5]

theorem sumStep_ok {v a : Reg} (hv : v ∉ [Reg.t4, .t6]) (hva : v ≠ a) {s : State}
    (hc : (s.gpr .t4).toNat ≤ 1) :
    WP isa (.block (sumStep v a)) s fun s' =>
      (s'.gpr v).toNat + 2 ^ 64 * (s'.gpr .t4).toNat = (s.gpr v).toNat + (s.gpr a).toNat + (s.gpr .t4).toNat ∧
      (s'.gpr .t4).toNat ≤ 1 ∧ Keeps [v, .t4, .t6] s s' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
  unfold sumStep
  show WP isa (.block ([.add v v a, .sltu .t6 v a] ++ ([.add v v .t4, .sltu .t4 v .t4] ++ ([.add .t4 .t4 .t6] : List Instr)))) s _
  refine WP.block_append (WP.mono (addc_ok (d := v) (x := v) (y := a) (c := .t6) hva hv.2) fun s1 ⟨e1, c1, k1⟩ => ?_)
  refine WP.block_append (WP.mono (addc_ok (d := v) (x := v) (y := .t4) (c := .t4) hv.1 hv.1) fun s2 ⟨e2, c2, k2⟩ => ?_)
  refine wp_add fun s3 u3 => WP.block_nil ?_
  rw [kp k1 (r := .t4) (by simp [Ne.symm hv.1])] at e2
  obtain t6 : s2.gpr .t6 = s1.gpr .t6 := kp k2 (by simp [Ne.symm hv.2])
  obtain v3 : s3.gpr v = s2.gpr v := u3.other _ hv.1
  obtain t4 : (s3.gpr .t4).toNat = (s2.gpr .t4).toNat + (s1.gpr .t6).toNat := by
    rw [u3.gpr, BitVec.toNat_add, t6]
    exact Nat.mod_eq_of_lt (by omega_using [c1, c2])
  obtain l0 := (s.gpr v).isLt
  obtain l1 := (s.gpr a).isLt
  obtain l3 := (s2.gpr v).isLt
  refine ⟨by rw [v3, t4]; omega_using [e1, e2], by rw [t4]; omega_using [e1, e2, c1, c2, l0, l1, l3, hc],
    ((k1.trans k2).trans (upd_keeps u3)).mono (by simp)⟩

/-- The high half plus the quotient. -/
theorem sums_ok {s : State} :
    WP isa (.block sums) s fun s' =>
      v4 s' .t0 .a7 .a5 .a6 + 2 ^ 256 * (s'.gpr .t4).toNat = v4 s .t0 .a7 .a5 .a6 + v4 s .a0 .a1 .a2 .a4 ∧
      (s'.gpr .t4).toNat ≤ 1 ∧ Keeps [.t0, .a7, .a5, .a6, .t4, .t6] s s' := by
  unfold sums
  refine WP.block_append (WP.mono (addc_ok (d := .t0) (x := .t0) (y := .a0) (c := .t4) (by decide) (by decide))
    fun s1 ⟨e1, c1, k1⟩ => ?_)
  refine WP.block_append (WP.mono (sumStep_ok (v := .a7) (a := .a1) (by decide) (by decide) c1)
    fun s2 ⟨e2, c2, k2⟩ => ?_)
  refine WP.block_append (WP.mono (sumStep_ok (v := .a5) (a := .a2) (by decide) (by decide) c2)
    fun s3 ⟨e3, c3, k3⟩ => ?_)
  refine WP.mono (sumStep_ok (v := .a6) (a := .a4) (by decide) (by decide) c3) fun s4 ⟨e4, c4, k4⟩ => ?_
  obtain k2' := k1.trans k2
  obtain k3' := k2'.trans k3
  rw [kp k1 (r := .a7) (by decide), kp k1 (r := .a1) (by decide)] at e2
  rw [kp k2' (r := .a5) (by decide), kp k2' (r := .a2) (by decide)] at e3
  rw [kp k3' (r := .a6) (by decide), kp k3' (r := .a4) (by decide)] at e4
  obtain o0 : s4.gpr .t0 = s1.gpr .t0 := by rw [kp k4 (by decide), kp k3 (by decide), kp k2 (by decide)]
  obtain o1 : s4.gpr .a7 = s2.gpr .a7 := by rw [kp k4 (by decide), kp k3 (by decide)]
  obtain o2 : s4.gpr .a5 = s3.gpr .a5 := kp k4 (by decide)
  refine ⟨?_, c4, (k3'.trans k4).mono⟩
  simp only [v4, o0, o1, o2]
  omega_using [e1, e2, e3, e4]

/-- The two candidates. -/
theorem cands_ok {s : State} (h7 : s.gpr .s8 = CV) (hc : (s.gpr .t3).toNat ≤ c) :
    WP isa (.block cands) s fun s' =>
      v4 s' .a0 .a1 .a2 .a4 + 2 ^ 256 * (s'.gpr .t6).toNat + (s.gpr .t3).toNat = v4 s .t0 .a7 .a5 .a6 + c ∧
      (s'.gpr .t6).toNat ≤ 1 ∧
      (∃ b, v4 s' .t0 .a7 .a5 .a6 + (s.gpr .t3).toNat = v4 s .t0 .a7 .a5 .a6 + 2 ^ 256 * b) ∧
      Keeps [.t0, .a7, .a5, .a6, .a0, .a1, .a2, .a4, .t3, .t5, .t6, .s8] s s' := by
  unfold cands
  refine WP.block_append (wp_sub fun s1 u1 => WP.block_nil ?_)
  refine WP.block_append (WP.mono (addc_ok (d := .a0) (x := .t0) (y := .s8) (c := .t6) (by decide) (by decide))
    fun s2 ⟨e2, _, k2⟩ => ?_)
  refine WP.block_append (WP.mono (addc_ok (d := .a1) (x := .a7) (y := .t6) (c := .t6) (by decide) (by decide))
    fun s3 ⟨e3, _, k3⟩ => ?_)
  refine WP.block_append (WP.mono (addc_ok (d := .a2) (x := .a5) (y := .t6) (c := .t6) (by decide) (by decide))
    fun s4 ⟨e4, _, k4⟩ => ?_)
  refine WP.block_append (WP.mono (addc_ok (d := .a4) (x := .a6) (y := .t6) (c := .t6) (by decide) (by decide))
    fun s5 ⟨e5, c5, k5⟩ => ?_)
  refine WP.block_append (WP.mono (bor_ok (x := .t0) (y := .t3) (b := .t5) (by decide) (by decide) (by decide))
    fun s6 ⟨e6, _, _, k6⟩ => ?_)
  refine WP.block_append (WP.mono (bor_ok (x := .a7) (y := .t5) (b := .t3) (by decide) (by decide) (by decide))
    fun s7 ⟨e7, _, _, k7⟩ => ?_)
  refine WP.block_append (WP.mono (bor_ok (x := .a5) (y := .t3) (b := .t5) (by decide) (by decide) (by decide))
    fun s8 ⟨e8, _, _, k8⟩ => ?_)
  refine wp_sub fun s9 u9 => WP.block_nil ?_
  obtain k1 := upd_keeps u1
  obtain k9 := upd_keeps u9
  obtain K5 : Keeps [.s8, .a0, .a1, .a2, .a4, .t6] s s5 := ((((k1.trans k2).trans k3).trans k4).trans k5).mono
  obtain v1 : (s1.gpr .s8).toNat + (s.gpr .t3).toNat = c := by
    rw [u1.gpr, h7, BitVec.toNat_sub, cv_toNat]
    simp only [c] at hc ⊢
    omega_using [hc]
  rw [kp k1 (r := .t0) (by decide)] at e2
  rw [kp k2 (r := .a7) (by decide), kp k1 (r := .a7) (by decide)] at e3
  rw [kp k3 (r := .a5) (by decide), kp k2 (r := .a5) (by decide), kp k1 (r := .a5) (by decide)] at e4
  rw [kp k4 (r := .a6) (by decide), kp k3 (r := .a6) (by decide), kp k2 (r := .a6) (by decide), kp k1 (r := .a6) (by decide)] at e5
  rw [kp K5 (r := .t0) (by decide), kp K5 (r := .t3) (by decide)] at e6
  rw [kp k6 (r := .a7) (by decide), kp K5 (r := .a7) (by decide)] at e7
  rw [kp k7 (r := .a5) (by decide), kp k6 (r := .a5) (by decide), kp K5 (r := .a5) (by decide)] at e8
  obtain a8 : s8.gpr .a6 = s.gpr .a6 := by rw [kp k8 (by decide), kp k7 (by decide), kp k6 (by decide), kp K5 (by decide)]
  obtain ⟨b, e9⟩ : ∃ b, (s9.gpr .a6).toNat + (s8.gpr .t5).toNat = (s.gpr .a6).toNat + 2 ^ 64 * b := by
    obtain l1 := (s8.gpr .t5).isLt
    obtain l2 := (s.gpr .a6).isLt
    refine ⟨if (s.gpr .a6).toNat < (s8.gpr .t5).toNat then 1 else 0, ?_⟩
    rw [u9.gpr, BitVec.toNat_sub, a8]
    split <;> omega_arith
  obtain K9 : Keeps [.t0, .a7, .a5, .a6, .t3, .t5] s5 s9 := (((k6.trans k7).trans k8).trans k9).mono
  obtain o0 : s9.gpr .a0 = s2.gpr .a0 := by rw [kp K9 (by decide), kp k5 (by decide), kp k4 (by decide), kp k3 (by decide)]
  obtain o1 : s9.gpr .a1 = s3.gpr .a1 := by rw [kp K9 (by decide), kp k5 (by decide), kp k4 (by decide)]
  obtain o2 : s9.gpr .a2 = s4.gpr .a2 := by rw [kp K9 (by decide), kp k5 (by decide)]
  obtain o4 : s9.gpr .a4 = s5.gpr .a4 := kp K9 (by decide)
  obtain o6 : s9.gpr .t6 = s5.gpr .t6 := kp K9 (by decide)
  obtain p0 : s9.gpr .t0 = s6.gpr .t0 := by rw [kp k9 (by decide), kp k8 (by decide), kp k7 (by decide)]
  obtain p7 : s9.gpr .a7 = s7.gpr .a7 := by rw [kp k9 (by decide), kp k8 (by decide)]
  obtain p5 : s9.gpr .a5 = s8.gpr .a5 := kp k9 (by decide)
  refine ⟨?_, by rw [o6]; exact c5, ⟨b, ?_⟩, (K5.trans K9).mono⟩
  · simp only [v4, o0, o1, o2, o4, o6]
    omega_using [v1, e2, e3, e4, e5]
  · simp only [v4, p0, p7, p5]
    omega_using [e6, e7, e8, e9]

theorem selStep_ok {O : Addr} {j : Nat} {a v : Reg} (ha : a ∉ [Reg.t4, .t2]) (hav : a ≠ v) (hj : j < 4) {s : State}
    (h2 : s.gpr .t2 = O) (oal : O.toNat % 8 = 0) (ow : InRegions s.wr (O + BitVec.ofNat 64 (8 * j)) 8)
    (hm : P256Field.IsMask (s.gpr .t4)) :
    WP isa (.block (selStep j a v)) s fun s' =>
      s'.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j))
        (if s.gpr .t4 = BitVec.allOnes 64 then s.gpr a else s.gpr v) ∧
      (∀ r, r ≠ a → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
  unfold selStep
  refine wp_xor' fun s2 u2 => wp_and fun s3 u3 => wp_xor' fun s4 u4 => ?_
  refine wp_sd (by omega_arith) (by rw [u4.other _ (Ne.symm ha.2), u3.other _ (Ne.symm ha.2), u2.other _ (Ne.symm ha.2),
    h2]) (al8 oal (by omega_arith)) (by rw [u4.wr, u3.wr, u2.wr]; exact ow) fun s5 u5 => WP.block_nil ?_
  obtain v4 : s4.gpr a = if s.gpr .t4 = BitVec.allOnes 64 then s.gpr a else s.gpr v := by
    rw [u4.gpr, u3.gpr, u3.other _ (Ne.symm hav), u2.other _ (Ne.symm hav), u2.gpr, u2.other _ (Ne.symm ha.1)]
    exact P256Field.sel_mask hm
  refine ⟨by rw [u5.mem, u4.mem, u3.mem, u2.mem, v4], fun r hr => ?_, by rw [u5.rd, u4.rd, u3.rd, u2.rd],
    by rw [u5.wr, u4.wr, u3.wr, u2.wr], by rw [u5.sp, u4.sp, u3.sp, u2.sp]⟩
  rw [u5.gpr, u4.other r hr, u3.other r hr, u2.other r hr]

/-- The selection: the candidate in `a0`–`a2`, `a4` if a carry is one, or the other. -/
theorem sels_ok {O : Addr} {s : State} (h2 : s.gpr .t2 = O) (oal : O.toNat % 8 = 0)
    (ow : ∀ i < 4, InRegions s.wr (O + BitVec.ofNat 64 (8 * i)) 8) (c4 : (s.gpr .t4).toNat ≤ 1)
    (c6 : (s.gpr .t6).toNat ≤ 1) :
    WP isa (.block sels) s fun s' =>
      (∀ r, r ∉ [Reg.a0, .a1, .a2, .a4, .t4, .t6] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨O, 32⟩] s.mem s'.mem ∧
      ov s'.mem O 4 = if (s.gpr .t4).toNat + (s.gpr .t6).toNat = 0 then v4 s .t0 .a7 .a5 .a6 else v4 s .a0 .a1 .a2 .a4 := by
  unfold sels
  simp only [List.cons_append, List.nil_append]
  refine wp_or fun s1 u1 => wp_li (imm := 0) (by decide) fun s2 u2 => wp_sub fun s3 u3 => ?_
  obtain K3 : Keeps [.t4, .t6] s s3 := (((upd_keeps u1).trans (upd_keeps u2)).trans (upd_keeps u3)).mono
  obtain b1 : ∀ {x : BitVec 64}, x.toNat ≤ 1 → x = 0 ∨ x = 1 := fun {x} h => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with e | e
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  obtain ⟨hm, hs⟩ : P256Field.IsMask (s3.gpr .t4) ∧
      (s3.gpr .t4 = BitVec.allOnes 64 ↔ ¬ (s.gpr .t4).toNat + (s.gpr .t6).toNat = 0) := by
    rw [u3.gpr, u2.gpr, u2.other .t4 (by decide), u1.gpr]
    rcases b1 c4 with e | e <;> rcases b1 c6 with e' | e' <;> rw [e, e'] <;>
      exact ⟨by unfold P256Field.IsMask; decide, by decide⟩
  refine WP.block_append (WP.mono (selStep_ok (O := O) (j := 0) (a := .a0) (v := .t0) (by decide) (by decide) (by decide)
    (by rw [kp K3 (by decide), h2]) oal (by rw [K3.2.2.2.1]; exact ow 0 (by decide)) hm)
    fun s4 ⟨m4, g4, rd4, wr4, sp4⟩ => ?_)
  obtain t4 : s4.gpr .t4 = s3.gpr .t4 := g4 _ (by decide)
  refine WP.block_append (WP.mono (selStep_ok (O := O) (j := 1) (a := .a1) (v := .a7) (by decide) (by decide) (by decide)
    (by rw [g4 _ (by decide), kp K3 (by decide), h2]) oal (by rw [wr4, K3.2.2.2.1]; exact ow 1 (by decide))
    (by rw [t4]; exact hm)) fun s5 ⟨m5, g5, rd5, wr5, sp5⟩ => ?_)
  obtain t5 : s5.gpr .t4 = s3.gpr .t4 := (g5 _ (by decide)).trans t4
  refine WP.block_append (WP.mono (selStep_ok (O := O) (j := 2) (a := .a2) (v := .a5) (by decide) (by decide) (by decide)
    (by rw [g5 _ (by decide), g4 _ (by decide), kp K3 (by decide), h2]) oal
    (by rw [wr5, wr4, K3.2.2.2.1]; exact ow 2 (by decide)) (by rw [t5]; exact hm)) fun s6 ⟨m6, g6, rd6, wr6, sp6⟩ => ?_)
  obtain t6 : s6.gpr .t4 = s3.gpr .t4 := (g6 _ (by decide)).trans t5
  refine WP.mono (selStep_ok (O := O) (j := 3) (a := .a4) (v := .a6) (by decide) (by decide) (by decide)
    (by rw [g6 _ (by decide), g5 _ (by decide), g4 _ (by decide), kp K3 (by decide), h2]) oal
    (by rw [wr6, wr5, wr4, K3.2.2.2.1]; exact ow 3 (by decide)) (by rw [t6]; exact hm))
    fun s7 ⟨m7, g7, rd7, wr7, sp7⟩ => ?_
  rw [kp K3 (r := .a0) (by decide), kp K3 (r := .t0) (by decide)] at m4
  rw [t4, g4 .a1 (by decide), g4 .a7 (by decide), kp K3 (r := .a1) (by decide), kp K3 (r := .a7) (by decide)] at m5
  rw [t5, g5 .a2 (by decide), g5 .a5 (by decide), g4 .a2 (by decide), g4 .a5 (by decide), kp K3 (r := .a2) (by decide),
    kp K3 (r := .a5) (by decide)] at m6
  rw [t6, g6 .a4 (by decide), g6 .a6 (by decide), g5 .a4 (by decide), g5 .a6 (by decide), g4 .a4 (by decide), g4 .a6 (by decide),
    kp K3 (r := .a4) (by decide), kp K3 (r := .a6) (by decide)] at m7
  refine ⟨fun r hr => ?_, by rw [rd7, rd6, rd5, rd4, K3.2.2.1], by rw [wr7, wr6, wr5, wr4, K3.2.2.2.1],
    by rw [sp7, sp6, sp5, sp4, K3.2.2.2.2], ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g7 r hr.2.2.2.1, g6 r hr.2.2.1, g5 r hr.2.1, g4 r hr.1, kp K3 (by simp [hr.2.2.2.2.1, hr.2.2.2.2.2])]
  · rw [m7, m6, m5, m4, K3.2.1]
    obtain ct : ∀ j < 4, (⟨O, 32⟩ : Region).Contains (O + BitVec.ofNat 64 (8 * j)) 8 := fun j hj => by
      rw [show (⟨O, 32⟩ : Region) = ⟨O + BitVec.ofNat 64 0, 32⟩ by simp]
      exact Offset.contains O (by omega_arith) (by omega_arith) (by omega_arith)
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 0 (by decide))).writeW (List.mem_singleton_self _) _
      (ct 1 (by decide))).writeW (List.mem_singleton_self _) _ (ct 2 (by decide))).writeW (List.mem_singleton_self _) _
      (ct 3 (by decide))
  · obtain d3 : dw s7.mem O (8 * 3) = (if s3.gpr .t4 = BitVec.allOnes 64 then s.gpr .a4 else s.gpr .a6).toNat := by
      rw [m7, dw_write_self]
    obtain d2 : dw s7.mem O (8 * 2) = (if s3.gpr .t4 = BitVec.allOnes 64 then s.gpr .a2 else s.gpr .a5).toNat := by
      rw [m7, dw_write_other _ _ _ (by decide) (by decide) (by decide), m6, dw_write_self]
    obtain d1 : dw s7.mem O (8 * 1) = (if s3.gpr .t4 = BitVec.allOnes 64 then s.gpr .a1 else s.gpr .a7).toNat := by
      rw [m7, dw_write_other _ _ _ (by decide) (by decide) (by decide), m6,
        dw_write_other _ _ _ (by decide) (by decide) (by decide), m5, dw_write_self]
    obtain d0 : dw s7.mem O (8 * 0) = (if s3.gpr .t4 = BitVec.allOnes 64 then s.gpr .a0 else s.gpr .t0).toNat := by
      rw [m7, dw_write_other _ _ _ (by decide) (by decide) (by decide), m6,
        dw_write_other _ _ _ (by decide) (by decide) (by decide), m5,
        dw_write_other _ _ _ (by decide) (by decide) (by decide), m4, dw_write_self]
    simp only [ov, colsV, d0, d1, d2, d3, v4]
    by_cases h : (s.gpr .t4).toNat + (s.gpr .t6).toNat = 0
    · obtain n : ¬ s3.gpr .t4 = BitVec.allOnes 64 := fun e => hs.mp e h
      simp only [ite_eq_right n, ite_eq_left h]
      omega_using []
    · simp only [ite_eq_left (hs.mpr h), ite_eq_right h]
      omega_using []

/-- The numbers of the reduction: `S = H + Q - h`, for a product `L + 2²⁵⁶ H` and the quotient `Q`. -/
theorem tail_nat {L H Q h V t D u E b XZ r : Nat} (hL : L + 2 ^ 256 * H = XZ) (hq : Q * c = L + 2 ^ 256 * h)
    (hs : V + 2 ^ 256 * t = H + Q) (hd : D + 2 ^ 256 * u + h = V + c) (he : E + h = V + 2 ^ 256 * b)
    (hh : h ≤ c) (hQ : Q < 2 ^ 256) (hV : V < 2 ^ 256) (hD : D < 2 ^ 256) (hE : E < 2 ^ 256)
    (hlt : ∀ S, S * 2 ^ 256 = XZ + Q * P → S < 2 * P) (hr : r = if t + u = 0 then E else D) :
    r < P ∧ ∃ S, S * 2 ^ 256 = XZ + Q * P ∧ r = S % P := by
  obtain hp : Q * P + Q * c = 2 ^ 256 * Q := by
    rw [← Nat.mul_add, show P + c = 2 ^ 256 by decide, Nat.mul_comm]
  obtain ⟨S, hS⟩ : ∃ S, S + h = H + Q := ⟨H + Q - h, by omega_using [hq, hp, hL, hh, hQ]⟩
  obtain hS' : S * 2 ^ 256 = XZ + Q * P := by omega_using [hS, hp, hq, hL]
  obtain hS2 := hlt S hS'
  simp only [show P = 2 ^ 256 - 4294968273 by decide, show c = 4294968273 by decide] at *
  obtain hrs : r = S ∨ r + (2 ^ 256 - 4294968273) = S := by
    split at hr
    · left; omega_using [hr, hs, hd, he, hh, hS, hV, hE, hD, ‹t + u = 0›]
    · right; omega_using [hr, hs, hd, he, hh, hS, hV, hE, hD, hS2, ‹¬ t + u = 0›]
  obtain hlr : r < 2 ^ 256 - 4294968273 := by
    split at hr <;> omega_arith
  refine ⟨hlr, S, hS', ?_⟩
  rcases hrs with e | e
  · rw [← e, Nat.mod_eq_of_lt hlr]
  · rw [← e, Nat.add_mod_right, Nat.mod_eq_of_lt hlr]

/-- The product in registers. -/
theorem loads8_ok {b : Addr} {s : State} (hc : Ctx b s) :
    WP isa (.block loads) s fun s' =>
      v4 s' .a0 .a1 .a2 .a4 + 2 ^ 256 * v4 s' .t0 .a7 .a5 .a6 = Rows.pw lay s.mem b ∧
      Keeps [.a0, .a1, .a2, .a4, .t0, .a7, .a5, .a6] s s' := by
  unfold loads
  refine ld_ok hc (by decide) (by decide) fun s1 u1 => ?_
  obtain h1 := GenWide.ctx_of hc (u1.other _ (by decide)) u1.wr
  refine ld_ok h1 (by decide) (by decide) fun s2 u2 => ?_
  obtain h2 := GenWide.ctx_of h1 (u2.other _ (by decide)) u2.wr
  refine ld_ok h2 (by decide) (by decide) fun s3 u3 => ?_
  obtain h3 := GenWide.ctx_of h2 (u3.other _ (by decide)) u3.wr
  refine ld_ok h3 (by decide) (by decide) fun s4 u4 => ?_
  obtain h4 := GenWide.ctx_of h3 (u4.other _ (by decide)) u4.wr
  refine ld_ok h4 (by decide) (by decide) fun s5 u5 => ?_
  obtain h5 := GenWide.ctx_of h4 (u5.other _ (by decide)) u5.wr
  refine ld_ok h5 (by decide) (by decide) fun s6 u6 => ?_
  obtain h6 := GenWide.ctx_of h5 (u6.other _ (by decide)) u6.wr
  refine ld_ok h6 (by decide) (by decide) fun s7 u7 => ?_
  obtain h7 := GenWide.ctx_of h6 (u7.other _ (by decide)) u7.wr
  refine ld_ok h7 (by decide) (by decide) fun s8 u8 => WP.block_nil ?_
  obtain K2 : Keeps [.a0, .a1] s s2 := (upd_keeps u1).trans (upd_keeps u2)
  obtain K4 : Keeps [.a0, .a1, .a2, .a4] s s4 := (K2.trans (upd_keeps u3)).trans (upd_keeps u4)
  obtain K6 : Keeps [.t0, .a7] s4 s6 := (upd_keeps u5).trans (upd_keeps u6)
  obtain K8 : Keeps [.t0, .a7, .a5, .a6] s4 s8 := (K6.trans (upd_keeps u7)).trans (upd_keeps u8)
  obtain m1 : s1.mem = s.mem := u1.mem
  obtain m2 : s2.mem = s.mem := K2.2.1
  obtain m3 : s3.mem = s.mem := u3.mem.trans m2
  obtain m4 : s4.mem = s.mem := K4.2.1
  obtain m5 : s5.mem = s.mem := u5.mem.trans m4
  obtain m6 : s6.mem = s.mem := K6.2.1.trans m4
  obtain m7 : s7.mem = s.mem := u7.mem.trans m6
  obtain w0 : (s8.gpr .a0).toNat = dw s.mem b 1856 := by
    rw [kp K8 (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; rfl
  obtain w1 : (s8.gpr .a1).toNat = dw s.mem b 1864 := by
    rw [kp K8 (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr, m1]; rfl
  obtain w2 : (s8.gpr .a2).toNat = dw s.mem b 1872 := by
    rw [kp K8 (by decide), u4.other _ (by decide), u3.gpr, m2]; rfl
  obtain w3 : (s8.gpr .a4).toNat = dw s.mem b 1880 := by rw [kp K8 (by decide), u4.gpr, m3]; rfl
  obtain w4 : (s8.gpr .t0).toNat = dw s.mem b 1888 := by
    rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.gpr, m4]; rfl
  obtain w5 : (s8.gpr .a7).toNat = dw s.mem b 1896 := by
    rw [u8.other _ (by decide), u7.other _ (by decide), u6.gpr, m5]; rfl
  obtain w6 : (s8.gpr .a5).toNat = dw s.mem b 1904 := by rw [u8.other _ (by decide), u7.gpr, m6]; rfl
  obtain w7 : (s8.gpr .a6).toNat = dw s.mem b 1912 := by rw [u8.gpr, m7]; rfl
  refine ⟨?_, (K4.trans K8).mono⟩
  simp only [v4, w0, w1, w2, w3, w4, w5, w6, w7, Rows.pw, lay, Impl.Weierstrass.RISCV64.Rows.Lay.P, Nat.reduceMul, colsV,
    Nat.reduceAdd, ← Nat.pow_mul, Nat.mul_zero]
  omega_using []

theorem redTail_ok : Rows.TailOk lay P redTail :=
  fun {b O s X Z} hc ht2 oal ow _ hX hZ hp => by
  unfold redTail
  refine WP.block_append (WP.mono (loads8_ok hc) fun s1 ⟨v1, k1⟩ => ?_)
  refine wp_li64 (by decide) _ fun s2 e2 k2 => wp_li64 (by decide) _ fun s3 e3 k3 => ?_
  obtain e23 : s3.gpr .t5 = NI := by rw [kp k3 (by decide), e2]
  refine WP.block_append (WP.mono (quots_ok e23 e3) fun s4 ⟨v4', c4, k4⟩ => ?_)
  refine WP.block_append (WP.mono sums_ok fun s5 ⟨v5, c5, k5⟩ => ?_)
  obtain t35 : s5.gpr .t3 = s4.gpr .t3 := kp k5 (by decide)
  refine WP.block_append (WP.mono (cands_ok (by rw [kp k5 (by decide), kp k4 (by decide), e3]) (by rw [t35]; exact c4))
    fun s6 ⟨v6, c6, ⟨bo, v6'⟩, k6⟩ => ?_)
  obtain K3 : Keeps [.a0, .a1, .a2, .a4, .t0, .a7, .a5, .a6, .t5, .t6, .s8] s s3 := ((k1.trans k2).trans k3).mono
  obtain K6 : Keeps [.a0, .a1, .a2, .a4, .t0, .a7, .a5, .a6, .t3, .t4, .t5, .t6, .s8] s s6 :=
    (((K3.trans k4).trans k5).trans k6).mono
  obtain t46 : s6.gpr .t4 = s5.gpr .t4 := kp k6 (by decide)
  refine WP.mono (sels_ok (O := O) (by rw [kp K6 (by decide), ht2]) oal (by rw [K6.2.2.2.1]; exact ow)
    (by rw [t46]; exact c5) c6) fun s7 ⟨g7, rd7, wr7, sp7, f7, v7⟩ => ?_
  obtain l3 : v4 s3 .a0 .a1 .a2 .a4 = v4 s1 .a0 .a1 .a2 .a4 := by
    simp only [v4, kp k3 (r := .a0) (by decide), kp k3 (r := .a1) (by decide), kp k3 (r := .a2) (by decide),
      kp k3 (r := .a4) (by decide), kp k2 (r := .a0) (by decide), kp k2 (r := .a1) (by decide),
      kp k2 (r := .a2) (by decide), kp k2 (r := .a4) (by decide)]
  obtain h4 : v4 s4 .t0 .a7 .a5 .a6 = v4 s1 .t0 .a7 .a5 .a6 := by
    simp only [v4, kp k4 (r := .t0) (by decide), kp k4 (r := .a7) (by decide), kp k4 (r := .a5) (by decide),
      kp k4 (r := .a6) (by decide), kp k3 (r := .t0) (by decide), kp k3 (r := .a7) (by decide), kp k3 (r := .a5) (by decide),
      kp k3 (r := .a6) (by decide), kp k2 (r := .t0) (by decide), kp k2 (r := .a7) (by decide),
      kp k2 (r := .a5) (by decide), kp k2 (r := .a6) (by decide)]
  have hX' : X < 2 ^ 256 := hX
  rw [l3] at v4'
  rw [h4] at v5
  rw [t35] at v6 v6'
  rw [t46] at v7
  obtain ⟨r1, S, hS, r2⟩ := tail_nat (v1.trans hp) v4' v5 v6 v6' c4 (v4_lt ..) (v4_lt ..) (v4_lt ..) (v4_lt ..)
    (fun S hS => (mont_nat hS hX' hZ (v4_lt s4 .a0 .a1 .a2 .a4)).1) v7
  refine ⟨fun r hr => ?_, by rw [rd7, K6.2.2.1], by rw [wr7, K6.2.2.2.1], by rw [sp7, K6.2.2.2.2],
    by rw [← K6.2.1]; exact f7.mono (by simp [lay]), r1, ?_⟩
  · obtain hs : ∀ r ∉ Rows.clobP lay, r ∉ [Reg.a0, .a1, .a2, .a4, .t4, .t6] ∧
        r ∉ [Reg.a0, .a1, .a2, .a4, .t0, .a7, .a5, .a6, .t3, .t4, .t5, .t6, .s8] := by
      intro r; cases r <;> decide
    rw [g7 r (hs r hr).1, kp K6 (hs r hr).2]
  · show ov s7.mem O 4 * 2 ^ 256 % P = X * Z % P
    rw [r2]
    exact (mont_nat hS hX' hZ (v4_lt s4 .a0 .a1 .a2 .a4)).2

theorem fast_core : CoreOkA (Impl.Weierstrass.RISCV64.Rows.fastWith lay redTail order) (fun _ B => B < P)
    (Gen4.mulRes P) :=
  @Gen4.rows_core P _ _ lay_ok rfl rfl rfl (by intro r; cases r <;> decide) _ redTail_ok

/-! ## The contracts -/

open VG.Proof.Weierstrass.RISCV64 (res mulRV addRV subRV)

variable {S : Impl.Weierstrass.Mont.Modulus}

theorem mul_rv (hk : S.k = 4) (hp : S.m = P) (s : State) (hs : (mulRV S).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.Secp256k1Field.mulFn s t s' ∧ abiPreserved s s' ∧ (mulRV S).post s s' := by
  obtain hc : CoreOk Impl.Weierstrass.RISCV64.Secp256k1Field.mulCore (fun _ B => B < S.m) (Gen4.mulRes S.m) := by rw [hp]; exact mulCore_core
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := Gen4.fn_rv hk @hc hs.1 (by exact hs.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v1,
    by rw [res, Impl.Weierstrass.Mont.Modulus.R, hk]; exact v2, by rw [hk]; exact k⟩

theorem add_rv (hk : S.k = 4) (hp : S.m = P) (s : State) (hs : (addRV S).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.Secp256k1Field.addFn s t s' ∧ abiPreserved s s' ∧ (addRV S).post s s' := by
  obtain hc : CoreOk (.block Impl.Weierstrass.RISCV64.Secp256k1Field.addCore) (fun A B => A + B < 2 * S.m) (fun A B r => r = (A + B) % S.m) := by
    rw [hp]; exact addCore_core
  obtain ⟨t, s', he, a, v, k⟩ := Gen4.fn_rv hk @hc hs.1 (by exact hs.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

theorem sub_rv (hk : S.k = 4) (hp : S.m = P) (s : State) (hs : (subRV S).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.Secp256k1Field.subFn s t s' ∧ abiPreserved s s' ∧ (subRV S).post s s' := by
  obtain hc : CoreOk (.block Impl.Weierstrass.RISCV64.Secp256k1Field.subCore) (fun A B => A < S.m ∧ B < S.m) (fun A B r => r = (A + S.m - B) % S.m) := by
    rw [hp]; exact subCore_core
  obtain ⟨t, s', he, a, v, k⟩ := Gen4.fn_rv hk @hc hs.1 (by exact hs.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

theorem mulA_rv (hk : S.k = 4) (hp : S.m = P) (s : State)
    (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV S)).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.Secp256k1Field.mulFnA s t s' ∧ abiPreserved s s' ∧ (mulRV S).post s s' := by
  obtain hc : CoreOkA (Impl.Weierstrass.RISCV64.Rows.fastWith lay redTail order) (fun _ B => B < S.m) (Gen4.mulRes S.m) := by
    rw [hp]; exact fast_core
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := P256Field.fnA_rv hk @hc hs.1.1 hs.2 (by exact hs.1.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v1,
    by rw [res, Impl.Weierstrass.Mont.Modulus.R, hk]; exact v2, by rw [hk]; exact k⟩

theorem addA_rv (hk : S.k = 4) (hp : S.m = P) (s : State)
    (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV S)).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.Secp256k1Field.addFnA s t s' ∧ abiPreserved s s' ∧ (addRV S).post s s' := by
  obtain hc : CoreOk (.block Impl.Weierstrass.RISCV64.Secp256k1Field.addCore) (fun A B => A + B < 2 * S.m)
      (fun A B r => r = (A + B) % S.m) := by
    rw [hp]; exact addCore_core
  obtain ⟨t, s', he, a, v, k⟩ := P256Field.fnA_rv hk (@P256Field.CoreOk.toA _ _ _ @hc) hs.1.1 hs.2 (by exact hs.1.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

theorem subA_rv (hk : S.k = 4) (hp : S.m = P) (s : State)
    (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV S)).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.Secp256k1Field.subFnA s t s' ∧ abiPreserved s s' ∧ (subRV S).post s s' := by
  obtain hc : CoreOk (.block Impl.Weierstrass.RISCV64.Secp256k1Field.subCore) (fun A B => A < S.m ∧ B < S.m)
      (fun A B r => r = (A + S.m - B) % S.m) := by
    rw [hp]; exact subCore_core
  obtain ⟨t, s', he, a, v, k⟩ := P256Field.fnA_rv hk (@P256Field.CoreOk.toA _ _ _ @hc) hs.1.1 hs.2 (by exact hs.1.2)
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

end

end

/-!
# ECDSA verification on RISC-V: the joint ladder

The pieces of the joint ladder of `Impl/Ecdsa/RISCV64/Verify.lean`, which
`JointJ.lean` puts together (`jointJ_ok`), with each step's `4 R` by Jacobian
doublings:

* `copyTo_ok`, `storePt_ok`: a point's slots to an entry of the table, through
  `a6 = s0 + JT`;
* `window_ok`: the window's entry number `4 u_j + v_j`, its
  masks, and the entry to `E`, by the comb's tree (`tree_ok`);
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.Secp256k1.Joint

open VG.Proof.Ecdsa.RISCV64.Joint

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.Secp256k1 (W field_ok unit)
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point mul onCurve)
open VG.Impl.Ecdsa.RISCV64.Comb (maskReg treeRegs)

/-! ## The complete additions -/

/-- A point in the slots `p`: its coordinates below `p`, representing `P`. -/
structure PtOk (base : Addr) (s : State) (p : Pt) (P : Point W) : Prop where
  rep : Rep W (tmv W 4 base s p.x) (tmv W 4 base s p.y) (tmv W 4 base s p.z) P
  x : wordsVal s.mem base p.x 4 < W.p
  y : wordsVal s.mem base p.y 4 < W.p
  z : wordsVal s.mem base p.z 4 < W.p

/-- The slots of the joint ladder's additions. -/
abbrev jSl : List Nat :=
  [secp256k1.sl AP, secp256k1.sl B3P, secp256k1.sl T0, secp256k1.sl T1, secp256k1.sl T2, secp256k1.sl T3, secp256k1.sl T4, secp256k1.sl T5,
    secp256k1.sl RX, secp256k1.sl RY, secp256k1.sl RZ, secp256k1.sl DX, secp256k1.sl DY, secp256k1.sl DZ, secp256k1.sl TX, secp256k1.sl TY, secp256k1.sl TZ,
    secp256k1.sl GX, secp256k1.sl GY, secp256k1.sl ONEP, secp256k1.sl CPX, secp256k1.sl CPY,
    secp256k1.sl G2X, secp256k1.sl G2Y, secp256k1.sl G2Z, secp256k1.sl G3X, secp256k1.sl G3Y, secp256k1.sl G3Z,
    secp256k1.sl Q2X, secp256k1.sl Q2Y, secp256k1.sl Q2Z, secp256k1.sl secp256k1.Q3X, secp256k1.sl secp256k1.Q3Y, secp256k1.sl secp256k1.Q3Z,
    secp256k1.sl secp256k1.EX, secp256k1.sl secp256k1.EY, secp256k1.sl secp256k1.EZ]

theorem jLay : Lay secp256k1.MP' (own 4) (· ∈ jSl) :=
  ⟨by decide, fun x y hx hy => apart_of (n := 8 * 4) (l := jSl) (by decide +kernel) x hx y hy, by decide, by decide⟩

theorem jShort : Short (· ∈ jSl) := by decide

/-- What the additions write. -/
abbrev addW (o : Pt) : List (Nat × Nat) :=
  (rcbW (Cfg.rcbSlots secp256k1) o).map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)]

/-- `o = p + q` by the complete addition, for points in slots of `jSl`. -/
theorem addPt_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base)
    (hap : wordsVal s.mem base (secp256k1.sl AP) 4 = W.a * 2 ^ 256 % W.p)
    (hbp : wordsVal s.mem base (secp256k1.sl B3P) 4 = 3 * W.b * 2 ^ 256 % W.p)
    {p q o : Pt} (hA : RcbApart (Cfg.rcbSlots secp256k1) p q o)
    (hsl : ∀ x ∈ rcbW (Cfg.rcbSlots secp256k1) o ++ rcbR (Cfg.rcbSlots secp256k1) p q, x ∈ jSl)
    {P P' : Point W} (hP : onCurve W P = true) (hP' : onCurve W P' = true)
    (hp : PtOk base s p P) (hq : PtOk base s q P') :
    WP isa (Cfg.addPt secp256k1 p q o) s fun s' =>
      Kp s s' ∧ Unch base (addW o) s.mem s'.mem ∧ PtOk base s' o (Spec.Weierstrass.add P P') := by
  have hp0 : 0 < W.p := by decide
  rw [Cfg.addPt_gen _ rfl]
  have hI : Inv 4 base W.p (· ∈ jSl) (rcbR (Cfg.rcbSlots secp256k1) p q)
      (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) s := by
    refine ⟨hw, fun x hx => hsl x (List.mem_append_right _ hx), fun x hx => ?_, fun x _ => rfl⟩
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show wordsVal _ _ (secp256k1.sl AP) 4 < _; rw [hap]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ (secp256k1.sl B3P) 4 < _; rw [hbp]; exact Nat.mod_lt _ hp0
    exacts [hp.x, hp.y, hp.z, hq.x, hq.y, hq.z]
  refine WP.mono (rcb_ok (F := secp256k1Field) field_ok rfl jLay jShort unit hA hsl hI (fun x hx => hx))
    fun s₁ ⟨k₁, I₁, t₁⟩ => ?_
  have ea : toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base (secp256k1.sl AP) 4) = Fin.ofNat W.p W.a := by
    rw [hap, toM_mont unit]
  have eb : toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base (secp256k1.sl B3P) 4) = Fin.ofNat W.p (3 * W.b) := by
    rw [hbp, toM_mont unit]
  generalize hE : (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) = E at I₁ t₁
  have hrep := Rep.add hL hP hP' hp.rep hq.rep (X3 := runOps (rcb (Cfg.rcbSlots secp256k1) p q o) E o.x)
    (Y3 := runOps (rcb (Cfg.rcbSlots secp256k1) p q o) E o.y) (Z3 := runOps (rcb (Cfg.rcbSlots secp256k1) p q o) E o.z)
    (by
      subst hE
      show rcbAdd (Fin.ofNat W.p W.a) (Fin.ofNat W.p (3 * W.b)) _ _ _ _ _ _ = _
      rw [← ea, ← eb]
      exact t₁.1.symm)
  have hm : ∀ x ∈ [o.x, o.y, o.z], x ∈ rcbW (Cfg.rcbSlots secp256k1) o ++ rcbR (Cfg.rcbSlots secp256k1) p q :=
    fun x hx => List.mem_append_left _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [rcbW])
  refine ⟨k₁.kp, k₁.mem, ⟨?_, I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp))⟩⟩
  have vx : tmv W 4 base s₁ o.x = _ := I₁.val _ (hm _ (by simp))
  have vy : tmv W 4 base s₁ o.y = _ := I₁.val _ (hm _ (by simp))
  have vz : tmv W 4 base s₁ o.z = _ := I₁.val _ (hm _ (by simp))
  rw [vx, vy, vz]
  exact hrep

theorem PtOk.of_eq {base : Addr} {s s' : State} {p : Pt} {P : Point W} (h : PtOk base s p P)
    (hx : wordsVal s'.mem base p.x 4 = wordsVal s.mem base p.x 4)
    (hy : wordsVal s'.mem base p.y 4 = wordsVal s.mem base p.y 4)
    (hz : wordsVal s'.mem base p.z 4 = wordsVal s.mem base p.z 4) : PtOk base s' p P :=
  ⟨by simp only [tmv]; rw [hx, hy, hz]; exact h.rep, by rw [hx]; exact h.x, by rw [hy]; exact h.y,
    by rw [hz]; exact h.z⟩

/-- A point copied to other slots. -/
theorem PtOk.move {base : Addr} {s s' : State} {p q : Pt} {P : Point W} (h : PtOk base s p P)
    (hx : wordsVal s'.mem base q.x 4 = wordsVal s.mem base p.x 4)
    (hy : wordsVal s'.mem base q.y 4 = wordsVal s.mem base p.y 4)
    (hz : wordsVal s'.mem base q.z 4 = wordsVal s.mem base p.z 4) : PtOk base s' q P :=
  ⟨by simp only [tmv]; rw [hx, hy, hz]; exact h.rep, by rw [hx]; exact h.x, by rw [hy]; exact h.y,
    by rw [hz]; exact h.z⟩

/-! ## The table's construction -/

section
variable {C : Spec.Weierstrass.Curve}

theorem mul_zero' (P : Point C) : mul 0 P = .infinity := by rw [Spec.Weierstrass.mul]; rfl

theorem mul_one' (P : Point C) : mul 1 P = P := by
  rw [Spec.Weierstrass.mul, ite_eq_right (by decide), show (1 : Nat) / 2 = 0 from rfl, mul_zero',
    ite_eq_right (by decide)]
  rfl

end

/-- What the construction reads: the constants, `G` and `Q`. -/
structure JPre (base : Addr) (s : State) (Q : Point W) : Prop where
  ws : WsReg s base
  ap : wordsVal s.mem base (secp256k1.sl AP) 4 = W.a * 2 ^ 256 % W.p
  bp : wordsVal s.mem base (secp256k1.sl B3P) 4 = 3 * W.b * 2 ^ 256 % W.p
  zero : wordsVal s.mem base (secp256k1.sl ZERO) 4 = 0
  onep : wordsVal s.mem base (secp256k1.sl ONEP) 4 = 1 * 2 ^ 256 % W.p
  gx : wordsVal s.mem base (secp256k1.sl GX) 4 = W.gx * 2 ^ 256 % W.p
  gy : wordsVal s.mem base (secp256k1.sl GY) 4 = W.gy * 2 ^ 256 % W.p
  qx : wordsVal s.mem base (secp256k1.sl CPX) 4 < W.p
  qy : wordsVal s.mem base (secp256k1.sl CPY) 4 < W.p
  q : Point.affine (tmv W 4 base s (secp256k1.sl CPX)) (tmv W 4 base s (secp256k1.sl CPY)) = Q
  on : onCurve W Q = true

/-- Slots apart from what code writes are kept. -/
theorem keepU {base : Addr} {Wl : List (Nat × Nat)} {m m' : Mem} (U : Unch base Wl m m') {D : List Nat}
    (hD : ∀ d ∈ D, (∀ w ∈ Wl, d + 8 * 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) ∧ d + 32 ≤ 2048) :
    ∀ d ∈ D, wordsVal m' base d 4 = wordsVal m base d 4 := fun d hd =>
  U.wordsVal (hD d hd).1 (by have := (hD d hd).2; omega_using [this])

/-- The registers `select` writes. -/
abbrev selRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4]

end VG.Proof.Ecdsa.RISCV64.Secp256k1.Joint
