module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Fn
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Verified
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.FieldRV
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.X448.RISCV64.R64.Product
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Arithmetic modulo a four-word modulus on RISC-V

The operations of `Impl/Weierstrass/RISCV64/Gen4.lean` meet `CoreOk`
(`mulCore_core`, `addCore_core`, `subCore_core`) for every modulus `m` with
`Ok m` (odd, below `2²⁵⁶`, its quotient constant right), by the lemmas of
P-256's field (`mulWith_ok`, `addWith_ok`, `subWith_ok`), from the reduction
(`reduce_ok`), the sum `x + (2²⁵⁶ - m)` (`sumC_ok`) and `m`'s words under a
mask (P-256's order's `kW`).

The reduction is P-256's order's (`RedInv`, with `m`), with `q m` added in a
round (`round_ok`): the quotient word and the carry out of `w + q m₀`
(`qword_ok`, `mont_carry`), each `q mⱼ` added with its carries (`mac_ok`),
the carries into the top word (`top_ok`), and the sums, whose numbers add up
(`round_arith`).

The functions then meet the shared contracts of
`Proof/Weierstrass/MontContract.lean` for a modulus `S` of four words with
`Ok S.m` as P-256's do (`Proof/Weierstrass/RISCV64/P256Field/Verified.lean`,
whose lemmas this uses), given that the taint analysis finds each operation
constant time (`CtOk`), which a modulus's own module proves of its code
(`by taint_decide`): `mul_verified`, `add_verified`, `sub_verified`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.Gen4

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide
open VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Impl.Weierstrass.RISCV64.Gen4 (wordOf negInv qword mac top sumC kword)
open VG.Proof.Weierstrass.RISCV64.P256Field
open VG.Proof.Weierstrass.RISCV64.P256Order (wp_li64 wp_mulhu rw_ne ofNat_lt add_toNat kp idx pow64_succ kW)
open VG.Proof.X25519.RISCV64 (Ctx Rest wp_mul)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok clob64 Keeps.rest)
open VG.Impl.Words.RISCV64 (li64 mulWide)

/-! ## Arithmetic -/

/-- Word `j` of `x`, as a number. -/
abbrev wd (x j : Nat) : Nat := x / 2 ^ (64 * j) % 2 ^ 64

theorem wordOf_toNat (x j : Nat) : (wordOf x j).toNat = wd x j := by
  rw [wordOf, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]

theorem wd_lt (x j : Nat) : wd x j < 2 ^ 64 := Nat.mod_lt _ (by decide)

theorem words4 {x : Nat} (h : x < 2 ^ 256) :
    x = wd x 0 + 2 ^ 64 * wd x 1 + 2 ^ 128 * wd x 2 + 2 ^ 192 * wd x 3 := by
  simp only [wd, show 64 * 0 = 0 from rfl, show 64 * 1 = 64 from rfl, show 64 * 2 = 128 from rfl,
    show 64 * 3 = 192 from rfl, Nat.pow_zero, Nat.div_one]
  omega

/-- What the code needs of a modulus: odd, below `2²⁵⁶`, and `negInv m` its
quotient constant, `-m⁻¹ mod 2⁶⁴`. -/
structure Ok (m : Nat) : Prop where
  pos : 0 < m
  lt : m < 2 ^ 256
  inv : (wd m 0 * (negInv m % 2 ^ 64) + 1) % 2 ^ 64 = 0

theorem mont_mod {m0 ni : Nat} (hi : (m0 * ni + 1) % 2 ^ 64 = 0) (w : Nat) :
    (w + (w * ni % 2 ^ 64) * m0) % 2 ^ 64 = 0 := by
  rw [Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod,
    show w + w * ni * m0 = w * (m0 * ni + 1) by rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm m0, Nat.mul_assoc,
      Nat.add_comm],
    Nat.mul_mod, hi, Nat.mul_zero, Nat.zero_mod]

/-- The carry out of `w + q m₀`, for the quotient word `q = w m' mod 2⁶⁴`, is `q ≠ 0`. -/
theorem mont_carry {m0 ni w : Nat} (hi : (m0 * ni + 1) % 2 ^ 64 = 0) (hw : w < 2 ^ 64) :
    w + (w * ni % 2 ^ 64) * m0 =
      2 ^ 64 * ((w * ni % 2 ^ 64) * m0 / 2 ^ 64 + if 0 < w * ni % 2 ^ 64 then 1 else 0) := by
  have h0 := mont_mod hi w
  have hz : w = 0 → w * ni % 2 ^ 64 = 0 := by rintro rfl; simp
  generalize w * ni % 2 ^ 64 = q at *
  have hd := Nat.div_add_mod (q * m0) (2 ^ 64)
  have hl := Nat.mod_lt (q * m0) (show 0 < 2 ^ 64 by decide)
  have hq0 : q = 0 → q * m0 = 0 := by rintro rfl; simp
  generalize q * m0 / 2 ^ 64 = H at *
  generalize q * m0 % 2 ^ 64 = L at *
  generalize q * m0 = X at *
  split <;> omega

theorem mul4 (q a b c d : Nat) :
    q * (a + 2 ^ 64 * b + 2 ^ 128 * c + 2 ^ 192 * d) =
      q * a + 2 ^ 64 * (q * b) + 2 ^ 128 * (q * c) + 2 ^ 192 * (q * d) := by
  simp only [Nat.mul_add, Nat.mul_left_comm q]

/-- The numbers of a round. -/
theorem round_arith {M q w0 w1 w2 w3 w4 cy U c0 c1 c2 c3 w1' w2' w3' w4' cy' P0 P1 P2 P3 : Nat}
    (hP : q * M = P0 + 2 ^ 64 * P1 + 2 ^ 128 * P2 + 2 ^ 192 * P3)
    (F0 : w0 + P0 = 2 ^ 64 * c0) (F1 : w1' + 2 ^ 64 * c1 = w1 + P1 + c0)
    (F2 : w2' + 2 ^ 64 * c2 = w2 + P2 + c1) (F3 : w3' + 2 ^ 64 * c3 = w3 + P3 + c2)
    (F4 : w4' + 2 ^ 64 * cy' = w4 + c3 + cy) :
    2 ^ 64 * (w1' + 2 ^ 64 * w2' + 2 ^ 128 * w3' + 2 ^ 192 * w4' + 2 ^ 256 * (cy' + U)) =
      w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3 + 2 ^ 256 * (cy + (w4 + 2 ^ 64 * U)) + q * M := by
  rw [hP]
  omega

theorem round_val {M Q q E W W' Pr : Nat} (hQ : Q < E) (hq : q < 2 ^ 64) (hv : W * E = Pr + Q * M)
    (key : 2 ^ 64 * W' = W + q * M) : Q + q * E < E * 2 ^ 64 ∧ W' * (E * 2 ^ 64) = Pr + (Q + q * E) * M := by
  constructor
  · have : (q + 1) * E ≤ 2 ^ 64 * E := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    rw [Nat.mul_comm E]
    omega
  · have : W' * (E * 2 ^ 64) = (2 ^ 64 * W') * E := by
      rw [Nat.mul_comm E, ← Nat.mul_assoc, Nat.mul_comm W']
    rw [this, key, Nat.add_mul, hv]
    grind

theorem prod_le (a b : BitVec 64) : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
  Nat.mul_le_mul (by have := a.isLt; omega) (by have := b.isLt; omega)

/-! ## Steps -/

/-- The quotient word `q = w m'` of `w` in `r`, in place, and in `a4` the
carry word of `w + q m₀`. -/
theorem qword_ok {r : Reg} {ni m0 : BitVec 64} (hinv : (m0.toNat * ni.toNat + 1) % 2 ^ 64 = 0)
    (hr : r ∉ [Reg.t0, .a0, .a4]) {s : State} :
    WP isa (.block (li64 .t0 .a0 ni ++ ([.mul r r .t0] : List Instr) ++ li64 .a4 .a0 m0 ++
        ([.mulhu .a4 r .a4] : List Instr) ++ ([.li .a0 0, .sltu .a0 .a0 r, .add .a4 .a4 .a0] : List Instr))) s
      fun s' =>
      (s'.gpr r).toNat = (s.gpr r).toNat * ni.toNat % 2 ^ 64 ∧
      (s.gpr r).toNat + (s'.gpr r).toNat * m0.toNat = 2 ^ 64 * (s'.gpr .a4).toNat ∧
      Keeps [r, .t0, .a0, .a4] s s' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨r0, ra, r4⟩ := hr
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_li64 (by decide) ni fun s1 e1 k1 => wp_mul fun s2 u2 => ?_
  refine wp_li64 (by decide) m0 fun s3 e3 k3 => wp_mulhu fun s4 u4 => ?_
  refine wp_li (imm := 0) (by decide) fun s5 u5 => wp_sltu fun s6 u6 => wp_add fun s7 u7 => WP.block_nil ?_
  have hq2 : s2.gpr r = s.gpr r * ni := by rw [u2.gpr, e1, k1.1 _ (by simp [r0, ra])]
  have q3 : s3.gpr r = s2.gpr r := k3.1 _ (by simp [r4, ra])
  have q7 : s7.gpr r = s2.gpr r := by
    rw [u7.other _ r4, u6.other _ ra, u5.other _ ra, u4.other _ r4, q3]
  have hqn : (s2.gpr r).toNat = (s.gpr r).toNat * ni.toNat % 2 ^ 64 := by rw [hq2, BitVec.toNat_mul]
  have hA4 : s4.gpr .a4 = BitVec.ofNat 64 ((s2.gpr r).toNat * m0.toNat / 2 ^ 64) := by
    rw [u4.gpr, q3, e3]
  have hB : (s6.gpr .a0).toNat = if 0 < (s2.gpr r).toNat then 1 else 0 := by
    rw [u6.gpr, sltu_toNat, u5.gpr, u5.other _ ra, u4.other _ r4, q3]; rfl
  have a4_6 : s6.gpr .a4 = s4.gpr .a4 := by rw [u6.other _ (by decide), u5.other _ (by decide)]
  have pl := prod_le (s2.gpr r) m0
  have bA4 : (s2.gpr r).toNat * m0.toNat / 2 ^ 64 < 2 ^ 64 - 1 := Nat.div_lt_of_lt_mul (by omega)
  have eA4 : (s4.gpr .a4).toNat = (s2.gpr r).toNat * m0.toNat / 2 ^ 64 := by
    rw [hA4]; exact ofNat_lt (by omega)
  have bB : (s6.gpr .a0).toNat ≤ 1 := by rw [hB]; split <;> decide
  have e7 : (s7.gpr .a4).toNat = (s4.gpr .a4).toNat + (s6.gpr .a0).toNat := by
    rw [u7.gpr, a4_6]; exact add_toNat (by rw [a4_6] at *; omega)
  have mc := mont_carry hinv (s.gpr r).isLt
  rw [← hqn] at mc
  refine ⟨by rw [q7, hqn], ?_, ?_⟩
  · rw [q7, e7, eA4, hB]; exact mc
  · exact ((((((k1.trans (upd_keeps u2)).trans k3).trans (upd_keeps u4)).trans (upd_keeps u5)).trans
      (upd_keeps u6)).trans (upd_keeps u7)).mono (by simp)

/-- `d += q w + c` for `q` in `q` and the carry word `c` in `a4`, in and out. -/
theorem mac_ok {q d : Reg} (w : BitVec 64) (hq : q ∉ [Reg.a0, .a4, .a5, .a6, .a7])
    (hd : d ∉ [Reg.a0, .a4, .a5, .a6, .a7]) {s : State} :
    WP isa (.block (li64 .a6 .a0 w ++ mulWide .a5 .a6 q .a6 ++
        ([.add .a5 .a5 .a4, .sltu .a7 .a5 .a4, .add .a6 .a6 .a7, .add d d .a5, .sltu .a7 d .a5, .add .a4 .a6 .a7] :
          List Instr)))
      s fun s' =>
      (s'.gpr d).toNat + 2 ^ 64 * (s'.gpr .a4).toNat =
        (s.gpr d).toNat + (s.gpr q).toNat * w.toNat + (s.gpr .a4).toNat ∧
      Keeps [d, .a0, .a4, .a5, .a6, .a7] s s' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq hd
  obtain ⟨q0, q4, q5, q6, q7⟩ := hq
  obtain ⟨d0, d4, d5, d6, d7⟩ := hd
  rw [List.append_assoc]
  refine wp_li64 (by decide) w fun s1 e1 k1 => ?_
  refine WP.block_append (WP.mono (mulWide_ok (lo := .a5) (hi := .a6) (a := q) (b := .a6) (Ne.symm q5)
    (by decide) (by decide)) fun s2 ⟨m2, k2⟩ => ?_)
  show WP isa (.block ([.add .a5 .a5 .a4, .sltu .a7 .a5 .a4] ++
    (.add .a6 .a6 .a7 :: ([.add d d .a5, .sltu .a7 d .a5] ++ [.add .a4 .a6 .a7])))) s2 _
  refine WP.block_append (WP.mono (add1_ok (d := .a5) (y := .a4) (c := .a7)) fun s3 ⟨e3, k3⟩ => ?_)
  refine wp_add fun s4 u4 => ?_
  refine WP.block_append (WP.mono (add1_ok (d := d) (y := .a5) (c := .a7) d5 d7) fun s5 ⟨e5, k5⟩ => ?_)
  refine wp_add fun s6 u6 => WP.block_nil ?_
  have hq1 : s1.gpr q = s.gpr q := k1.1 _ (by simp [q6, q0])
  rw [hq1, e1] at m2
  have a4_2 : s2.gpr .a4 = s.gpr .a4 := by rw [k2.1 _ (by decide), k1.1 _ (by decide)]
  rw [a4_2] at e3
  have a6_3 : s3.gpr .a6 = s2.gpr .a6 := k3.1 _ (by decide)
  have d4' : s4.gpr d = s.gpr d := by
    rw [u4.other _ d6, k3.1 _ (by simp [d5, d7]), k2.1 _ (by simp [d5, d6]), k1.1 _ (by simp [d6, d0])]
  have a5_4 : s4.gpr .a5 = s3.gpr .a5 := u4.other _ (by decide)
  rw [d4', a5_4] at e5
  have a6_5 : s5.gpr .a6 = s4.gpr .a6 := k5.1 _ (by simp [Ne.symm d6])
  have pl := prod_le (s.gpr q) w
  have := (s.gpr .a4).isLt; have := (s.gpr d).isLt; have := (s5.gpr d).isLt; have := (s3.gpr .a5).isLt
  have := (s2.gpr .a5).isLt
  have e4 : (s4.gpr .a6).toNat = (s2.gpr .a6).toNat + (s3.gpr .a7).toNat := by
    rw [u4.gpr, a6_3]; exact add_toNat (by omega)
  have e6 : (s6.gpr .a4).toNat = (s4.gpr .a6).toNat + (s5.gpr .a7).toNat := by
    rw [u6.gpr, a6_5]; exact add_toNat (by omega)
  refine ⟨?_, ?_⟩
  · rw [u6.other _ d4, e6]; omega
  · exact (((((k1.trans k2).trans k3).trans (upd_keeps u4)).trans k5).trans (upd_keeps u6)).mono (by simp)

/-- The carry word `a4` and the carry `a2` into `d`, their carries into `a2`. -/
theorem top_ok {d : Reg} (hd : d ∉ [Reg.a2, .a4, .a7]) {s : State} :
    WP isa (.block (top d)) s fun s' =>
      ((s.gpr .a2).toNat ≤ 1 →
        (s'.gpr d).toNat + 2 ^ 64 * (s'.gpr .a2).toNat = (s.gpr d).toNat + (s.gpr .a4).toNat + (s.gpr .a2).toNat ∧
        (s'.gpr .a2).toNat ≤ 1) ∧
      Keeps [d, .a2, .a7] s s' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨d2, d4, d7⟩ := hd
  unfold top
  show WP isa (.block ([.add d d .a4, .sltu .a7 d .a4] ++ ([.add d d .a2, .sltu .a2 d .a2] ++
    [.add .a2 .a2 .a7]))) s _
  refine WP.block_append (WP.mono (add1_ok (d := d) (y := .a4) (c := .a7) d4 d7) fun s1 ⟨e1, k1⟩ => ?_)
  refine WP.block_append (WP.mono (add1_ok (d := d) (y := .a2) (c := .a2) d2 d2) fun s2 ⟨e2, k2⟩ => ?_)
  refine wp_add fun s3 u3 => WP.block_nil ?_
  have a2_1 : s1.gpr .a2 = s.gpr .a2 := k1.1 _ (by simp [Ne.symm d2])
  have a7_2 : s2.gpr .a7 = s1.gpr .a7 := k2.1 _ (by simp [Ne.symm d7])
  rw [a2_1] at e2
  refine ⟨fun hc => ?_, (((k1.trans k2).trans (upd_keeps u3)).mono (by simp))⟩
  have := (s.gpr d).isLt; have := (s.gpr .a4).isLt; have := (s1.gpr d).isLt; have := (s2.gpr d).isLt
  have := (s2.gpr .a2).isLt; have := (s1.gpr .a7).isLt
  have e3 : (s3.gpr .a2).toNat = (s2.gpr .a2).toNat + (s1.gpr .a7).toNat := by
    rw [u3.gpr, a7_2]; exact add_toNat (by omega)
  rw [u3.other _ d2, e3]
  omega

/-! ## The reduction -/

/-- After `i` rounds, from `s0`: P-256's invariant (`RedInv`) with `m`. -/
structure RedInv (m : Nat) (b : Addr) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clobM s0 s
  mem : s.mem = s0.mem
  cy : (s.gpr .a2).toNat ≤ 1
  val : ∃ Q, Q < 2 ^ (64 * i) ∧ wv s0.mem b i s * 2 ^ (64 * i) = prodV s0.mem b + Q * m

variable {m : Nat}

theorem qword_m (hm : Ok m) (i : Nat) {s : State} :
    WP isa (.block (qword m i)) s fun s' =>
      (s'.gpr (rw i)).toNat = (s.gpr (rw i)).toNat * (negInv m % 2 ^ 64) % 2 ^ 64 ∧
      (s.gpr (rw i)).toNat + (s'.gpr (rw i)).toNat * wd m 0 = 2 ^ 64 * (s'.gpr .a4).toNat ∧
      Keeps [rw i, .t0, .a0, .a4] s s' := by
  obtain ⟨n0, na0, -, -, n4, -, -, -, -⟩ := rw_ne i
  have h := qword_ok (r := rw i) (ni := BitVec.ofNat 64 (negInv m)) (m0 := wordOf m 0) (s := s)
    (by rw [wordOf_toNat, BitVec.toNat_ofNat]; exact hm.inv) (by simp [n0, na0, n4])
  rw [wordOf_toNat, BitVec.toNat_ofNat] at h
  exact h

theorem mac_m (i j : Nat) {s : State} :
    WP isa (.block (mac m i j)) s fun s' =>
      (s'.gpr (rw (i + j))).toNat + 2 ^ 64 * (s'.gpr .a4).toNat =
        (s.gpr (rw (i + j))).toNat + (s.gpr (rw i)).toNat * wd m j + (s.gpr .a4).toNat ∧
      Keeps [rw (i + j), .a0, .a4, .a5, .a6, .a7] s s' := by
  obtain ⟨-, na0, -, -, n4, n5, n6, n7, -⟩ := rw_ne i
  obtain ⟨-, ma0, -, -, m4, m5, m6, m7, -⟩ := rw_ne (i + j)
  have h := mac_ok (q := rw i) (d := rw (i + j)) (wordOf m j) (s := s) (by simp [na0, n4, n5, n6, n7])
    (by simp [ma0, m4, m5, m6, m7])
  rw [wordOf_toNat] at h
  exact h

/-- Round `i`. -/
theorem round_ok (hm : Ok m) {b : Addr} {s0 : State} {i : Nat} (hi : i < 4) {s : State}
    (h : RedInv m b s0 i s) :
    WP isa (.block (Impl.Weierstrass.RISCV64.Gen4.round m i)) s (RedInv m b s0 (i + 1)) := by
  obtain ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34, dk⟩ := rw_facts i hi
  obtain ⟨n02, n04, n05, n06, n07, n0t, n03, c0⟩ := dk 0 (by decide)
  obtain ⟨n12, n14, n15, n16, n17, n1t, n13, c1⟩ := dk 1 (by decide)
  obtain ⟨n22, n24, n25, n26, n27, n2t, n23, c2⟩ := dk 2 (by decide)
  obtain ⟨n32, n34, n35, n36, n37, n3t, n33, c3⟩ := dk 3 (by decide)
  obtain ⟨n42, n44, n45, n46, n47, n4t, n43, c4⟩ := dk 4 (by decide)
  simp only [Nat.add_zero] at n02 n04 n05 n06 n07 n0t n03 c0
  have n0a := (rw_ne i).2.1
  have n1a := (rw_ne (i + 1)).2.1
  have n2a := (rw_ne (i + 2)).2.1
  have n3a := (rw_ne (i + 3)).2.1
  have n4a := (rw_ne (i + 4)).2.1
  have hc := h.ctx
  have hd : ACC + 8 * (i + 4) + 8 ≤ 2048 := by simp only [ACC]; omega
  unfold Impl.Weierstrass.RISCV64.Gen4.round
  simp only [List.append_assoc, List.singleton_append]
  refine ld_ok hc hd (by simp only [ACC]; omega) fun s1 u1 => ?_
  have hT4 : (s1.gpr (rw (i + 4))).toNat = T s0.mem b (i + 4) := by
    rw [u1.gpr, ← h.mem]; rfl
  refine WP.block_append (WP.mono (qword_m hm i) fun s2 ⟨q1, q2, k2⟩ => ?_)
  refine WP.block_append (WP.mono (mac_m (m := m) i 1) fun s3 ⟨e3, k3⟩ => ?_)
  refine WP.block_append (WP.mono (mac_m (m := m) i 2) fun s4 ⟨e4, k4⟩ => ?_)
  refine WP.block_append (WP.mono (mac_m (m := m) i 3) fun s5 ⟨e5, k5⟩ => ?_)
  refine WP.mono (top_ok (d := rw (i + 4)) (by simp [n42, n44, n47])) fun s6 ⟨e6, k6⟩ => ?_
  -- The quotient word, kept.
  have q3 : s3.gpr (rw i) = s2.gpr (rw i) := kp k3 (by simp [d01, n0a, n04, n05, n06, n07])
  have q4 : s4.gpr (rw i) = s2.gpr (rw i) := by rw [kp k4 (by simp [d02, n0a, n04, n05, n06, n07]), q3]
  rw [q3] at e4
  rw [q4] at e5
  -- What each step read.
  have g1 : ∀ r, r ≠ rw (i + 4) → s1.gpr r = s.gpr r := u1.other
  rw [g1 _ d04] at q2
  have w1_2 : s2.gpr (rw (i + 1)) = s.gpr (rw (i + 1)) := by
    rw [kp k2 (by simp [Ne.symm d01, n1t, n1a, n14]), g1 _ d14]
  rw [w1_2] at e3
  have w2_3 : s3.gpr (rw (i + 2)) = s.gpr (rw (i + 2)) := by
    rw [kp k3 (by simp [Ne.symm d12, n2a, n24, n25, n26, n27]), kp k2 (by simp [Ne.symm d02, n2t, n2a, n24]),
      g1 _ d24]
  rw [w2_3] at e4
  have w3_4 : s4.gpr (rw (i + 3)) = s.gpr (rw (i + 3)) := by
    rw [kp k4 (by simp [Ne.symm d23, n3a, n34, n35, n36, n37]),
      kp k3 (by simp [Ne.symm d13, n3a, n34, n35, n36, n37]), kp k2 (by simp [Ne.symm d03, n3t, n3a, n34]),
      g1 _ d34]
  rw [w3_4] at e5
  have w4_5 : s5.gpr (rw (i + 4)) = s1.gpr (rw (i + 4)) := by
    rw [kp k5 (by simp [Ne.symm d34, n4a, n44, n45, n46, n47]),
      kp k4 (by simp [Ne.symm d24, n4a, n44, n45, n46, n47]),
      kp k3 (by simp [Ne.symm d14, n4a, n44, n45, n46, n47]), kp k2 (by simp [Ne.symm d04, n4t, n4a, n44])]
  have a2_5 : s5.gpr .a2 = s.gpr .a2 := by
    rw [kp k5 (by simp [Ne.symm n32]), kp k4 (by simp [Ne.symm n22]), kp k3 (by simp [Ne.symm n12]),
      kp k2 (by simp [Ne.symm n02]), g1 _ (Ne.symm n42)]
  obtain ⟨e6, cy⟩ := e6 (by rw [a2_5]; exact h.cy)
  rw [w4_5, hT4, a2_5] at e6
  -- The new registers, read from the last state.
  have o1 : s6.gpr (rw (i + 1)) = s3.gpr (rw (i + 1)) := by
    rw [kp k6 (by simp [d14, n12, n17]), kp k5 (by simp [d13, n1a, n14, n15, n16, n17]),
      kp k4 (by simp [d12, n1a, n14, n15, n16, n17])]
  have o2 : s6.gpr (rw (i + 2)) = s4.gpr (rw (i + 2)) := by
    rw [kp k6 (by simp [d24, n22, n27]), kp k5 (by simp [d23, n2a, n24, n25, n26, n27])]
  have o3 : s6.gpr (rw (i + 3)) = s5.gpr (rw (i + 3)) := kp k6 (by simp [d34, n32, n37])
  -- The frame.
  have sub : ∀ r ∈ clob64, r ∈ clobM := by decide
  have cons : ∀ {r : Reg} {l : List Reg}, r ∈ clob64 → (∀ x ∈ l, x ∈ clobM) → ∀ x ∈ r :: l, x ∈ clobM :=
    fun hr hl x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact sub _ hr
      · exact hl x hx
  have hrest : Rest clobM s s6 :=
    (u1.rest (sub _ c4)).trans <| ((Keeps.rest k2).mono (cons c0 (by decide))).trans <|
      ((Keeps.rest k3).mono (cons c1 (by decide))).trans <| ((Keeps.rest k4).mono (cons c2 (by decide))).trans <|
      ((Keeps.rest k5).mono (cons c3 (by decide))).trans ((Keeps.rest k6).mono (cons c4 (by decide)))
  have hmem : s6.mem = s0.mem := by
    rw [k6.2.1, k5.2.1, k4.2.1, k3.2.1, k2.2.1, u1.mem, h.mem]
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := idx i
  have hup : upW s0.mem b (i + 4) (4 - i) = T s0.mem b (i + 4) + 2 ^ 64 * upW s0.mem b (i + 5) (3 - i) := by
    rw [i6 hi]; rfl
  have hM := mul4 (s2.gpr (rw i)).toNat (wd m 0) (wd m 1) (wd m 2) (wd m 3)
  rw [← words4 hm.lt] at hM
  have key : 2 ^ 64 * wv s0.mem b (i + 1) s6 = wv s0.mem b i s + (s2.gpr (rw i)).toNat * m := by
    simp only [wv, i1, i2, i3, i4, i5 hi, hup, o1, o2, o3]
    exact round_arith hM q2 e3 e4 e5 e6
  obtain ⟨Q, hQ, hv⟩ := h.val
  obtain ⟨v1, v2⟩ := round_val hQ (BitVec.isLt _) hv key
  refine ⟨hc.of_rest hrest (by decide), h.rest.trans hrest, hmem, cy,
    ⟨Q + (s2.gpr (rw i)).toNat * 2 ^ (64 * i), by rw [pow64_succ]; exact v1, by rw [pow64_succ]; exact v2⟩⟩

/-- The rounds, by induction. -/
theorem rounds_ok (hm : Ok m) {b : Addr} {s0 : State} : ∀ n ≤ 4, ∀ s, RedInv m b s0 0 s →
    WP isa (.block ((List.range n).flatMap (Impl.Weierstrass.RISCV64.Gen4.round m))) s (RedInv m b s0 n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (rounds_ok hm n (by omega) s h) fun s1 h1 => round_ok hm (by omega) h1)

/-- The initial loads, as P-256's. -/
theorem loads_ok {b : Addr} {s : State} (hc : Ctx b s) :
    WP isa (.block ((List.range 4).map (fun j => .load .d (rw j) .a3 (ACC + 8 * j)) ++ ([.li .a2 0] : List Instr))) s
      (RedInv m b s 0) :=
  WP.mono (P256Field.loads_ok hc) fun _ h =>
    ⟨h.ctx, h.rest.mono (by decide), h.mem, h.cy, ⟨0, by decide, by
      obtain ⟨Q, hQ, hv⟩ := h.val
      have : Q = 0 := by simpa using hQ
      subst this
      simpa using hv⟩⟩

/-- `reduce`: `X + 2²⁵⁶ c` with `(X + 2²⁵⁶ c) 2²⁵⁶ = T + Q m` for some `Q < 2²⁵⁶`. -/
theorem reduce_ok (hm : Ok m) {b : Addr} {s : State} (hc : Ctx b s) :
    WP isa (.block (Impl.Weierstrass.RISCV64.Gen4.reduce m)) s fun s' =>
      Ctx b s' ∧ Rest clobM s s' ∧ s'.mem = s.mem ∧ (s'.gpr XC).toNat ≤ 1 ∧
      ∃ Q, Q < 2 ^ 256 ∧
        ((s'.gpr X0).toNat + 2 ^ 64 * (s'.gpr X1).toNat + 2 ^ 128 * (s'.gpr X2).toNat +
          2 ^ 192 * (s'.gpr X3).toNat + 2 ^ 256 * (s'.gpr XC).toNat) * 2 ^ 256 = prodV s.mem b + Q * m := by
  unfold Impl.Weierstrass.RISCV64.Gen4.reduce
  refine WP.block_append (WP.mono (loads_ok hc) fun s1 h1 => WP.mono (rounds_ok hm 4 (Nat.le_refl _) s1 h1)
    fun s2 h2 => ?_)
  obtain ⟨Q, hQ, hv⟩ := h2.val
  refine ⟨h2.ctx, h2.rest, h2.mem, h2.cy, Q, by simpa using hQ, ?_⟩
  simpa [wv, upW, X0, X1, X2, X3, XC, rw, RW] using hv

/-! ## The final subtraction -/

theorem sum_arith {x0 x1 x2 x3 y0 y1 y2 y3 c0 c1 c2 c3 C0 C1 C2 C3 C : Nat}
    (hC : C = C0 + 2 ^ 64 * C1 + 2 ^ 128 * C2 + 2 ^ 192 * C3)
    (e0 : y0 + 2 ^ 64 * c0 = x0 + C0) (e1 : y1 + 2 ^ 64 * c1 = x1 + C1 + c0)
    (e2 : y2 + 2 ^ 64 * c2 = x2 + C2 + c1) (e3 : y3 + 2 ^ 64 * c3 = x3 + C3 + c2) :
    y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 + 2 ^ 256 * c3 =
      x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 + C := by
  omega

/-- `x + (2²⁵⁶ - m)` into `t6`, `a4`–`a6`, its carry into `a7`. -/
theorem sumC_ok (hm : Ok m) {s : State} :
    WP isa (.block (sumC m)) s fun s' =>
      v4 s' .t6 .a4 .a5 .a6 + 2 ^ 256 * (s'.gpr .a7).toNat = v4 s X0 X1 X2 X3 + (2 ^ 256 - m) ∧
      (s'.gpr .a7).toNat ≤ 1 ∧ Keeps clobC s s' := by
  unfold sumC
  simp only [List.append_assoc]
  refine wp_li64 (by decide) _ fun s1 e1 k1 => wp_add fun s2 u2 => wp_sltu fun s3 u3 => ?_
  refine wp_li64 (by decide) _ fun s4 e4 k4 => ?_
  refine WP.block_append (WP.mono (adc_ok (d := .a4) (x := X1) (y := .t0) (c := .a7) (u := .a0))
    fun s5 ⟨f5, k5⟩ => ?_)
  refine wp_li64 (by decide) _ fun s6 e6 k6 => ?_
  refine WP.block_append (WP.mono (adc_ok (d := .a5) (x := X2) (y := .t0) (c := .a7) (u := .a0))
    fun s7 ⟨f7, k7⟩ => ?_)
  refine wp_li64 (by decide) _ fun s8 e8 k8 => ?_
  refine WP.mono (adc_ok (d := .a6) (x := X3) (y := .t0) (c := .a7) (u := .a0)) fun s9 ⟨f9, k9⟩ => ?_
  -- Word 0.
  have x0_1 : s1.gpr X0 = s.gpr X0 := kp k1 (by decide)
  have hs3 : s3.gpr .a7 = if s2.gpr .t6 < s1.gpr .t0 then 1 else 0 := by rw [u3.gpr, u2.other .t0 (by decide)]
  have c0 := carry (s1.gpr X0) (s1.gpr .t0)
  rw [← u2.gpr, ← hs3, x0_1, e1, wordOf_toNat] at c0
  have t6_3 : s3.gpr .t6 = s2.gpr .t6 := u3.other _ (by decide)
  rw [← t6_3] at c0
  -- Word 1.
  have a7_4 : s4.gpr .a7 = s3.gpr .a7 := kp k4 (by decide)
  have f5' := f5 (by rw [a7_4, u3.gpr]; exact sltu_le _)
  have x1_4 : s4.gpr X1 = s.gpr X1 := by
    rw [kp k4 (by decide), u3.other X1 (by decide), u2.other X1 (by decide), kp k1 (by decide)]
  rw [e4, x1_4, a7_4, wordOf_toNat] at f5'
  -- Word 2.
  have a7_6 : s6.gpr .a7 = s5.gpr .a7 := kp k6 (by decide)
  have b5 : (s5.gpr .a7).toNat ≤ 1 := by
    have := (s5.gpr .a4).isLt; have := (s.gpr X1).isLt; have := wd_lt (2 ^ 256 - m) 1
    have := (s3.gpr .a7).isLt; have : (s3.gpr .a7).toNat ≤ 1 := by rw [u3.gpr]; exact sltu_le _
    omega
  have f7' := f7 (by rw [a7_6]; exact b5)
  have x2_6 : s6.gpr X2 = s.gpr X2 := by
    rw [kp k6 (by decide), kp k5 (by decide), kp k4 (by decide), u3.other X2 (by decide),
      u2.other X2 (by decide), kp k1 (by decide)]
  rw [e6, x2_6, a7_6, wordOf_toNat] at f7'
  -- Word 3.
  have a7_8 : s8.gpr .a7 = s7.gpr .a7 := kp k8 (by decide)
  have b7 : (s7.gpr .a7).toNat ≤ 1 := by
    have := (s7.gpr .a5).isLt; have := (s.gpr X2).isLt; have := wd_lt (2 ^ 256 - m) 2
    omega
  have f9' := f9 (by rw [a7_8]; exact b7)
  have x3_8 : s8.gpr X3 = s.gpr X3 := by
    rw [kp k8 (by decide), kp k7 (by decide), kp k6 (by decide), kp k5 (by decide), kp k4 (by decide),
      u3.other X3 (by decide), u2.other X3 (by decide), kp k1 (by decide)]
  rw [e8, x3_8, a7_8, wordOf_toNat] at f9'
  -- The registers at the end.
  have o0 : s9.gpr .t6 = s3.gpr .t6 := by
    rw [kp k9 (by decide), kp k8 (by decide), kp k7 (by decide), kp k6 (by decide), kp k5 (by decide),
      kp k4 (by decide)]
  have o1 : s9.gpr .a4 = s5.gpr .a4 := by
    rw [kp k9 (by decide), kp k8 (by decide), kp k7 (by decide), kp k6 (by decide)]
  have o2 : s9.gpr .a5 = s7.gpr .a5 := by rw [kp k9 (by decide), kp k8 (by decide)]
  have hlt : 2 ^ 256 - m < 2 ^ 256 := by have := hm.pos; omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [v4, o0, o1, o2]
    exact sum_arith (words4 hlt) c0 f5' f7' f9'
  · have := (s9.gpr .a6).isLt; have := (s.gpr X3).isLt; have := wd_lt (2 ^ 256 - m) 3; omega
  · exact (((((((((k1.trans (upd_keeps u2)).trans (upd_keeps u3)).trans k4).trans k5).trans k6).trans k7).trans
      k8).trans k9)).mono

/-! ## The operations -/

/-- `m`'s word `j` under the mask. -/
theorem kword_ok (j : Nat) : KOk (kword m j) (wd m j) := by
  have h := kW (wordOf m j)
  rw [wordOf_toNat] at h
  exact h

/-- Montgomery's product modulo `m`. -/
abbrev mulRes (m A B r : Nat) : Prop := r < m ∧ r * 2 ^ 256 % m = A * B % m

theorem mulCore_core (hm : Ok m) :
    CoreOk (Impl.Weierstrass.RISCV64.Gen4.mulCore m) (fun _ B => B < m) (mulRes m) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB =>
    WP.mono (mulWith_ok hm.pos (Nat.le_of_lt hm.lt) (reduce_ok hm) (fun _ => sumC_ok hm) hw h4 h5 h2 ha8 hb8
      ho8 ha hb ho hdb hB) fun _ ⟨v1, v2, f, g, rd, wr, sp⟩ => ⟨⟨v1, v2⟩, f, g, rd, wr, sp⟩

theorem addCore_core (hm : Ok m) :
    CoreOk (.block (Impl.Weierstrass.RISCV64.Gen4.addCore m)) (fun A B => A + B < 2 * m)
      (fun A B r => r = (A + B) % m) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho _ hAB =>
    WP.mono (addWith_ok (sum := sumC m) (Nat.le_of_lt hm.lt) (fun _ => sumC_ok hm) hw h4 h5 h2 ha8 hb8 ho8 ha
      hb ho hAB) fun _ ⟨v, f, g, rd, wr, sp⟩ => ⟨v, f.mono (by simp), g, rd, wr, sp⟩

theorem subCore_core (hm : Ok m) :
    CoreOk (.block (Impl.Weierstrass.RISCV64.Gen4.subCore m)) (fun A B => A < m ∧ B < m)
      (fun A B r => r = (A + m - B) % m) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho _ hAB =>
    WP.mono (subWith_ok (words4 hm.lt) (wd_lt _ _) (wd_lt _ _) (wd_lt _ _) (wd_lt _ _) (kword_ok 0)
      (kword_ok 1) (kword_ok 2) (kword_ok 3) hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hAB.1 hAB.2)
      fun _ ⟨v, f, g, rd, wr, sp⟩ => ⟨v, f.mono (by simp), g, rd, wr, sp⟩

/-! ## The contracts -/


open VG.Impl.Weierstrass.RISCV64.P256Field (fn ptrs SA SB SO)
open VG.Proof.Weierstrass.RISCV64.P256Field (numAt_d4 keeps_of_frame fn_ct read_zero satWs CoreOk fn_ok d4
  rvPub_agree)
open VG.Impl.Weierstrass.RISCV64.Gen4 (mulCore addCore subCore mulFn addFn subFn)
open VG.Impl.Weierstrass.Mont (numAt Keeps Modulus Fits)
open VG.Proof.Weierstrass.RISCV64 (offArg rvPre arg res rvPub mulRV addRV subRV)
open VG.Proof.Ed25519.RISCV64 (mulAgreeLo)

/-- What the taint analysis proves of an operation `core` (`fn_ct`): `fn core`
is constant time. -/
abbrev CtOk (core : Prog isa) : Prop :=
  RelCT isa (VG.RISCV64.Taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]))
    (.seq (.block ptrs) (.ite (.zero .t0) core
      (.seq (.block (([.addi .t1 .t2 0] : List Instr) ++ VG.Impl.Ed25519.RISCV64.unpackField .t4 SA 0 ++
          VG.Impl.Ed25519.RISCV64.unpackField .t5 SB 0 ++
          ([.addi .t4 .a3 SA, .addi .t5 .a3 SB, .addi .t2 .a3 SO] : List Instr))) <|
        .seq core (.block (VG.Impl.Ed25519.RISCV64.packField .t1 SO 0))))) fun _ _ => True

variable {S : Modulus}

/-- `fn core` meets a contract by register, from `fn_ok`. -/
theorem fn_rv (hk : S.k = 4) {core : Prog isa} {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop}
    (hcore : CoreOk core pre res) {s : State} (hs : rvPre S s) (hp : pre (arg S s .a2) (arg S s .a3)) :
    ∃ t s', Exec isa (fn core) s t s' ∧ abiPreserved s s' ∧
      res (arg S s .a2) (arg S s .a3) (numAt s'.mem (s.gpr .a0) (offArg s .a1) 4) ∧
      Keeps 4 (s.gpr .a0) (offArg s .a1) s.mem s'.mem := by
  obtain ⟨-, hwr, hfit, ⟨fo, fa, fb⟩, hal⟩ := hs
  simp only [Fits, hk, VG.Proof.Weierstrass.RISCV64.rvOwn_le (show 4 ≤ 6 by decide), Impl.Weierstrass.Mont.ownAt,
    Impl.Weierstrass.Mont.ownBytes] at fo fa fb
  simp only [arg, hk, numAt_d4] at hp ⊢
  obtain ⟨t, s', he, v, f, g, -, -, sp⟩ := fn_ok hcore rfl hal (by rw [hwr]; simp) hfit fo fa fb hp
  refine ⟨t, s', he, ⟨fun r hr => g r (by revert hr; revert r; decide), sp, g _ (by decide)⟩, v,
    keeps_of_frame fo f⟩

theorem mul_rv (hk : S.k = 4) (hm : Ok S.m) (s : State) (hs : (mulRV S).pre s) :
    ∃ t s', Exec isa (mulFn S.m) s t s' ∧ abiPreserved s s' ∧ (mulRV S).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fn_rv hk (@mulCore_core S.m hm) hs.1 (by exact hs.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v1,
    by rw [res, Impl.Weierstrass.Mont.Modulus.R, hk]; exact v2, by rw [hk]; exact k⟩

theorem add_rv (hk : S.k = 4) (hm : Ok S.m) (s : State) (hs : (addRV S).pre s) :
    ∃ t s', Exec isa (addFn S.m) s t s' ∧ abiPreserved s s' ∧ (addRV S).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv hk (@addCore_core S.m hm) hs.1 (by exact hs.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

theorem sub_rv (hk : S.k = 4) (hm : Ok S.m) (s : State) (hs : (subRV S).pre s) :
    ∃ t s', Exec isa (subFn S.m) s t s' ∧ abiPreserved s s' ∧ (subRV S).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv hk (@subCore_core S.m hm) hs.1 (by exact hs.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

theorem mulA_rv (hk : S.k = 4) (hm : Ok S.m) (s : State)
    (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV S)).pre s) :
    ∃ t s', Exec isa (Impl.Weierstrass.RISCV64.Gen4.mulFnA S.m) s t s' ∧ abiPreserved s s' ∧ (mulRV S).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := P256Field.fnA_rv hk (@mulCore_core S.m hm) hs.1.1 hs.2 (by exact hs.1.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v1,
    by rw [res, Impl.Weierstrass.Mont.Modulus.R, hk]; exact v2, by rw [hk]; exact k⟩

theorem addA_rv (hk : S.k = 4) (hm : Ok S.m) (s : State)
    (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV S)).pre s) :
    ∃ t s', Exec isa (Impl.Weierstrass.RISCV64.Gen4.addFnA S.m) s t s' ∧ abiPreserved s s' ∧ (addRV S).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := P256Field.fnA_rv hk (@addCore_core S.m hm) hs.1.1 hs.2 (by exact hs.1.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

theorem subA_rv (hk : S.k = 4) (hm : Ok S.m) (s : State)
    (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV S)).pre s) :
    ∃ t s', Exec isa (Impl.Weierstrass.RISCV64.Gen4.subFnA S.m) s t s' ∧ abiPreserved s s' ∧ (subRV S).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := P256Field.fnA_rv hk (@subCore_core S.m hm) hs.1.1 hs.2 (by exact hs.1.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

/-! ## The shared contracts -/

theorem rvPub_agree' : ∀ s₁ s₂ : State, rvPre S s₁ → rvPre S s₂ → rvPub s₁ s₂ → mulAgreeLo s₁ s₂ :=
  fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, h0, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption⟩

theorem sat_pre (hk : S.k = 4) : rvPre S satWs ∧ arg S satWs .a2 = 0 ∧ arg S satWs .a3 = 0 := by
  refine ⟨⟨rfl, rfl, by decide, ⟨?_, ?_, ?_⟩, by decide⟩, read_zero _ _, read_zero _ _⟩ <;>
    simp [Fits, hk, VG.Proof.Weierstrass.RISCV64.rvOwn, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes,
      satWs, offArg]

theorem mul_verified (hk : S.k = 4) (hm : Ok S.m) (hct : CtOk (mulCore S.m)) :
    Verified RISCV64.target (mulFn S.m) (S.mulContract RISCV64.abi) := by
  obtain ⟨c, w, m, k, d⟩ := S
  cases hk
  exact Verified.of_correct (mul_rv rfl hm) (fn_ct (Pre := (mulRV ⟨c, w, m, 4, d⟩).pre)
    (fun s₁ s₂ h₁ h₂ hp => rvPub_agree' s₁ s₂ h₁.1 h₂.1 hp) hct)
    { pre := by sig_implies_pre [Impl.Weierstrass.Mont.Modulus.mulContract, Impl.Weierstrass.Mont.sig, arg, mulRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      post := by sig_implies_post [Impl.Weierstrass.Mont.Modulus.mulContract, Impl.Weierstrass.Mont.sig, arg,
        mulRV, rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      pub := by sig_implies_pub [Impl.Weierstrass.Mont.Modulus.mulContract, Impl.Weierstrass.Mont.sig, arg, mulRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      sat := ⟨satWs, by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.Mont.sig, RISCV64.abi, RISCV64.argRegs, satWs]
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre (S := ⟨c, w, m, 4, d⟩) rfl
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; exact hm.pos⟩ }

theorem add_verified (hk : S.k = 4) (hm : Ok S.m) (hct : CtOk (.block (addCore S.m))) :
    Verified RISCV64.target (addFn S.m) (S.addContract RISCV64.abi) := by
  obtain ⟨c, w, m, k, d⟩ := S
  cases hk
  exact Verified.of_correct (add_rv rfl hm) (fn_ct (Pre := (addRV ⟨c, w, m, 4, d⟩).pre)
    (fun s₁ s₂ h₁ h₂ hp => rvPub_agree' s₁ s₂ h₁.1 h₂.1 hp) hct)
    { pre := by sig_implies_pre [Impl.Weierstrass.Mont.Modulus.addContract, Impl.Weierstrass.Mont.sig, arg, addRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      post := by sig_implies_post [Impl.Weierstrass.Mont.Modulus.addContract, Impl.Weierstrass.Mont.sig, arg,
        addRV, rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      pub := by sig_implies_pub [Impl.Weierstrass.Mont.Modulus.addContract, Impl.Weierstrass.Mont.sig, arg, addRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      sat := ⟨satWs, by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.Mont.sig, RISCV64.abi, RISCV64.argRegs, satWs]
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre (S := ⟨c, w, m, 4, d⟩) rfl
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; have := hm.pos; dsimp only at this ⊢; omega⟩ }

theorem sub_verified (hk : S.k = 4) (hm : Ok S.m) (hct : CtOk (.block (subCore S.m))) :
    Verified RISCV64.target (subFn S.m) (S.subContract RISCV64.abi) := by
  obtain ⟨c, w, m, k, d⟩ := S
  cases hk
  exact Verified.of_correct (sub_rv rfl hm) (fn_ct (Pre := (subRV ⟨c, w, m, 4, d⟩).pre)
    (fun s₁ s₂ h₁ h₂ hp => rvPub_agree' s₁ s₂ h₁.1 h₂.1 hp) hct)
    { pre := by sig_implies_pre [Impl.Weierstrass.Mont.Modulus.subContract, Impl.Weierstrass.Mont.sig, arg, subRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      post := by sig_implies_post [Impl.Weierstrass.Mont.Modulus.subContract, Impl.Weierstrass.Mont.sig, arg,
        subRV, rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      pub := by sig_implies_pub [Impl.Weierstrass.Mont.Modulus.subContract, Impl.Weierstrass.Mont.sig, arg, subRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      sat := ⟨satWs, by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.Mont.sig, RISCV64.abi, RISCV64.argRegs, satWs]
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre (S := ⟨c, w, m, 4, d⟩) rfl
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; exact ⟨hm.pos, hm.pos⟩⟩ }

end VG.Proof.Weierstrass.RISCV64.Gen4
