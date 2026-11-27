module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen5
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Rows
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen5.Fn
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.FieldRV
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Fn
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Order.Fn
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Arithmetic modulo a five-word modulus on RISC-V

The operations of `Impl/Weierstrass/RISCV64/Gen5.lean` meet `CoreOk`
(`mulCore_core`, `fast_core`, `addCore_core`, `subCore_core`) for every
modulus `m` with `Ok m` (odd, below `2³²⁰`, its quotient constant right), by
the lemmas of `Proof/Weierstrass/RISCV64/Gen5/Fn.lean` (`mulWith_ok`,
`csubWith_ok`, `subWith_ok`), from the reduction (`reduce_ok`), the words of `2³²⁰ - m` (`sumK_ok`) and `m`'s words under a
mask (P-384's order's `kmW`), as the six-word functions' do (Gen6's, in
`Proof/Ecdsa/RISCV64/BrainpoolP384r1/MulFn.lean`).

The reduction keeps five words in registers (`RedInv`): round `i` takes the
quotient word and the carry out of `w + q m₀` (`qword_ok`, Gen4's
`mont_carry`), adds each `q mⱼ` with its carries (`mac_ok`), loads the next
word of the product and adds the carries into it (Gen4's `top_ok`), and the
sums add up. The product's twelve words have their top two zero, so the
number the rounds leave is the product's.

The functions then meet the contracts by register (`mulRV`, `addRV`,
`subRV`) for a modulus `S` of five words with `Ok S.m`: `mul_rv`, `add_rv`,
`sub_rv`, and for offsets as the calls set them, `mulA_rv`, `addA_rv`,
`subA_rv`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.Gen5

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide
open VG.Impl.Weierstrass.RISCV64.Gen5 (ACC gw GW qword mac sumKs subKs)
open VG.Impl.Weierstrass.RISCV64.P384Field (X XC)
open VG.Impl.Weierstrass.RISCV64.Gen4 (wordOf negInv top)
open VG.Proof.Weierstrass.RISCV64.Gen4 (wd wordOf_toNat wd_lt mont_carry prod_le round_val top_ok)
open VG.Proof.Weierstrass.RISCV64.P256Order (wp_li64 wp_mulhu ofNat_lt add_toNat kp pow64_succ)
open VG.Proof.Weierstrass.RISCV64.P256Field (sltu_toNat upd_keeps add1_ok)
open VG.Proof.X25519.RISCV64 (Ctx Rest wp_mul)
open VG.Proof.X448.RISCV64.R64 (dw ld_ok clob64 Keeps.rest colsV)
open VG.Impl.Words.RISCV64 (li64 mulWide)

/-! ## Arithmetic -/

theorem words5 {x : Nat} (h : x < 2 ^ 320) :
    x = wd x 0 + 2 ^ 64 * wd x 1 + 2 ^ 128 * wd x 2 + 2 ^ 192 * wd x 3 + 2 ^ 256 * wd x 4 := by
  simp only [wd, show 64 * 0 = 0 from rfl, show 64 * 1 = 64 from rfl, show 64 * 2 = 128 from rfl,
    show 64 * 3 = 192 from rfl, show 64 * 4 = 256 from rfl, Nat.pow_zero, Nat.div_one]
  omega_using [h]

theorem colsV5 (f : Nat → Nat) :
    colsV f 5 = f 0 + 2 ^ 64 * f 1 + 2 ^ 128 * f 2 + 2 ^ 192 * f 3 + 2 ^ 256 * f 4 := by
  simp only [colsV]
  omega_using []

/-- What the code needs of a modulus: odd, below `2³²⁰` (stated as `(2⁶⁴)⁵`,
which `decide` evaluates), and `negInv m` its quotient constant,
`-m⁻¹ mod 2⁶⁴`. -/
structure Ok (m : Nat) : Prop where
  pos : 0 < m
  lt' : m < (2 ^ 64) ^ 5
  inv : (wd m 0 * (negInv m % 2 ^ 64) + 1) % 2 ^ 64 = 0

theorem Ok.lt {m : Nat} (h : Ok m) : m < 2 ^ 320 := by
  have := h.lt'
  simp only [← Nat.pow_mul, Nat.reduceMul] at this
  exact this

theorem mul5 (q a b c d e : Nat) :
    q * (a + 2 ^ 64 * b + 2 ^ 128 * c + 2 ^ 192 * d + 2 ^ 256 * e) =
      q * a + 2 ^ 64 * (q * b) + 2 ^ 128 * (q * c) + 2 ^ 192 * (q * d) + 2 ^ 256 * (q * e) := by
  simp only [Nat.mul_add, Nat.mul_left_comm q]

/-! ## The registers -/

theorem gw_ne (j : Nat) : gw j ≠ .t0 ∧ gw j ≠ .a2 ∧ gw j ≠ .a3 ∧ gw j ≠ .a4 ∧ gw j ≠ .a5 ∧
    gw j ≠ .a6 ∧ gw j ≠ .a7 ∧ gw j ∈ clobM := by
  have : j % 5 < 5 := Nat.mod_lt _ (by decide)
  obtain h | h | h | h | h : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4 := by omega_using []
  all_goals simp only [gw, GW, h]; decide

theorem gw_five (i : Nat) : gw (i + 5) = gw i := by simp only [gw, Nat.add_mod_right]

/-- The five registers of a round are distinct. -/
theorem gw_facts : ∀ i < 5,
    gw i ≠ gw (i + 1) ∧ gw i ≠ gw (i + 2) ∧ gw i ≠ gw (i + 3) ∧ gw i ≠ gw (i + 4) ∧
    gw (i + 1) ≠ gw (i + 2) ∧ gw (i + 1) ≠ gw (i + 3) ∧ gw (i + 1) ≠ gw (i + 4) ∧
    gw (i + 2) ≠ gw (i + 3) ∧ gw (i + 2) ≠ gw (i + 4) ∧ gw (i + 3) ≠ gw (i + 4) := by
  decide

/-! ## Steps -/

/-- The quotient word `q = w m'` of `w` in `r`, in place, and in `a4` the
carry word of `w + q m₀`. -/
theorem qword_ok {r : Reg} {ni m0 : BitVec 64} (hinv : (m0.toNat * ni.toNat + 1) % 2 ^ 64 = 0)
    (hr : r ∉ [Reg.t0, .a5, .a4]) {s : State} :
    WP isa (.block (li64 .t0 .a5 ni ++ ([.mul r r .t0] : List Instr) ++ li64 .a4 .a5 m0 ++
        ([.mulhu .a4 r .a4] : List Instr) ++ ([.li .a5 0, .sltu .a5 .a5 r, .add .a4 .a4 .a5] : List Instr))) s
      fun s' =>
      (s'.gpr r).toNat = (s.gpr r).toNat * ni.toNat % 2 ^ 64 ∧
      (s.gpr r).toNat + (s'.gpr r).toNat * m0.toNat = 2 ^ 64 * (s'.gpr .a4).toNat ∧
      Keeps [r, .t0, .a5, .a4] s s' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨r0, ra, r4⟩ := hr
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_li64 (by decide) ni fun s1 e1 k1 => wp_mul fun s2 u2 => ?_
  refine wp_li64 (by decide) m0 fun s3 e3 k3 => wp_mulhu fun s4 u4 => ?_
  refine wp_li (imm := 0) (by decide) fun s5 u5 => wp_sltu fun s6 u6 => wp_add fun s7 u7 => WP.block_nil ?_
  obtain hq2 : s2.gpr r = s.gpr r * ni := by rw [u2.gpr, e1, k1.1 _ (by simp [r0, ra])]
  obtain q3 : s3.gpr r = s2.gpr r := k3.1 _ (by simp [r4, ra])
  obtain q7 : s7.gpr r = s2.gpr r := by
    rw [u7.other _ r4, u6.other _ ra, u5.other _ ra, u4.other _ r4, q3]
  obtain hqn : (s2.gpr r).toNat = (s.gpr r).toNat * ni.toNat % 2 ^ 64 := by rw [hq2, BitVec.toNat_mul]
  obtain hA4 : s4.gpr .a4 = BitVec.ofNat 64 ((s2.gpr r).toNat * m0.toNat / 2 ^ 64) := by
    rw [u4.gpr, q3, e3]
  obtain hB : (s6.gpr .a5).toNat = if 0 < (s2.gpr r).toNat then 1 else 0 := by
    rw [u6.gpr, sltu_toNat, u5.gpr, u5.other _ ra, u4.other _ r4, q3]; rfl
  obtain a4_6 : s6.gpr .a4 = s4.gpr .a4 := by rw [u6.other _ (by decide), u5.other _ (by decide)]
  obtain pl := prod_le (s2.gpr r) m0
  obtain bA4 : (s2.gpr r).toNat * m0.toNat / 2 ^ 64 < 2 ^ 64 - 1 := Nat.div_lt_of_lt_mul (by omega_using [pl])
  obtain eA4 : (s4.gpr .a4).toNat = (s2.gpr r).toNat * m0.toNat / 2 ^ 64 := by
    rw [hA4]; exact ofNat_lt (by omega_using [pl])
  obtain bB : (s6.gpr .a5).toNat ≤ 1 := by rw [hB]; split <;> decide
  obtain e7 : (s7.gpr .a4).toNat = (s4.gpr .a4).toNat + (s6.gpr .a5).toNat := by
    rw [u7.gpr, a4_6]; exact add_toNat (by rw [a4_6] at *; omega_using [pl, eA4, bB])
  obtain mc := mont_carry hinv (s.gpr r).isLt
  rw [← hqn] at mc
  refine ⟨by rw [q7, hqn], ?_, ?_⟩
  · rw [q7, e7, eA4, hB]; exact mc
  · exact ((((((k1.trans (upd_keeps u2)).trans k3).trans (upd_keeps u4)).trans (upd_keeps u5)).trans
      (upd_keeps u6)).trans (upd_keeps u7)).mono (by simp)

/-- `d += q w + c` for `q` in `q` and the carry word `c` in `a4`, in and out. -/
theorem mac_ok {q d : Reg} (w : BitVec 64) (hq : q ∉ [Reg.a4, .a5, .a6, .a7])
    (hd : d ∉ [Reg.a4, .a5, .a6, .a7]) {s : State} :
    WP isa (.block (li64 .a6 .a7 w ++ mulWide .a5 .a6 q .a6 ++
        ([.add .a5 .a5 .a4, .sltu .a7 .a5 .a4, .add .a6 .a6 .a7, .add d d .a5, .sltu .a7 d .a5, .add .a4 .a6 .a7] :
          List Instr)))
      s fun s' =>
      (s'.gpr d).toNat + 2 ^ 64 * (s'.gpr .a4).toNat =
        (s.gpr d).toNat + (s.gpr q).toNat * w.toNat + (s.gpr .a4).toNat ∧
      Keeps [d, .a4, .a5, .a6, .a7] s s' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq hd
  obtain ⟨q4, q5, q6, q7⟩ := hq
  obtain ⟨d4, d5, d6, d7⟩ := hd
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
  obtain hq1 : s1.gpr q = s.gpr q := k1.1 _ (by simp [q6, q7])
  rw [hq1, e1] at m2
  obtain a4_2 : s2.gpr .a4 = s.gpr .a4 := by rw [k2.1 _ (by decide), k1.1 _ (by decide)]
  rw [a4_2] at e3
  obtain a6_3 : s3.gpr .a6 = s2.gpr .a6 := k3.1 _ (by decide)
  obtain d4' : s4.gpr d = s.gpr d := by
    rw [u4.other _ d6, k3.1 _ (by simp [d5, d7]), k2.1 _ (by simp [d5, d6]), k1.1 _ (by simp [d6, d7])]
  obtain a5_4 : s4.gpr .a5 = s3.gpr .a5 := u4.other _ (by decide)
  rw [d4', a5_4] at e5
  obtain a6_5 : s5.gpr .a6 = s4.gpr .a6 := k5.1 _ (by simp [Ne.symm d6])
  obtain pl := prod_le (s.gpr q) w
  have := (s.gpr .a4).isLt; have := (s.gpr d).isLt; have := (s5.gpr d).isLt; have := (s3.gpr .a5).isLt
  have := (s2.gpr .a5).isLt
  obtain e4 : (s4.gpr .a6).toNat = (s2.gpr .a6).toNat + (s3.gpr .a7).toNat := by
    rw [u4.gpr, a6_3]; exact add_toNat (by omega_using [m2, e3, pl])
  obtain e6 : (s6.gpr .a4).toNat = (s4.gpr .a6).toNat + (s5.gpr .a7).toNat := by
    rw [u6.gpr, a6_5]; exact add_toNat (by omega_using [m2, e3, e5, pl, e4])
  refine ⟨?_, ?_⟩
  · rw [u6.other _ d4, e6]; omega_using [m2, e3, e5, e4]
  · exact (((((k1.trans k2).trans k3).trans (upd_keeps u4)).trans k5).trans (upd_keeps u6)).mono (by simp)

variable {m : Nat}

theorem qword_m (hm : Ok m) (i : Nat) {s : State} :
    WP isa (.block (qword m i)) s fun s' =>
      (s'.gpr (gw i)).toNat = (s.gpr (gw i)).toNat * (negInv m % 2 ^ 64) % 2 ^ 64 ∧
      (s.gpr (gw i)).toNat + (s'.gpr (gw i)).toNat * wd m 0 = 2 ^ 64 * (s'.gpr .a4).toNat ∧
      Keeps [gw i, .t0, .a5, .a4] s s' := by
  obtain ⟨n0, -, -, n4, n5, -, -, -⟩ := gw_ne i
  obtain h := qword_ok (r := gw i) (ni := BitVec.ofNat 64 (negInv m)) (m0 := wordOf m 0) (s := s)
    (by rw [wordOf_toNat, BitVec.toNat_ofNat]; exact hm.inv) (by simp [n0, n5, n4])
  rw [wordOf_toNat, BitVec.toNat_ofNat] at h
  exact h

theorem mac_m (i j : Nat) {s : State} :
    WP isa (.block (mac m i j)) s fun s' =>
      (s'.gpr (gw (i + j))).toNat + 2 ^ 64 * (s'.gpr .a4).toNat =
        (s.gpr (gw (i + j))).toNat + (s.gpr (gw i)).toNat * wd m j + (s.gpr .a4).toNat ∧
      Keeps [gw (i + j), .a4, .a5, .a6, .a7] s s' := by
  obtain ⟨-, -, -, n4, n5, n6, n7, -⟩ := gw_ne i
  obtain ⟨-, -, -, m4, m5, m6, m7, -⟩ := gw_ne (i + j)
  obtain h := mac_ok (q := gw i) (d := gw (i + j)) (wordOf m j) (s := s) (by simp [n4, n5, n6, n7])
    (by simp [m4, m5, m6, m7])
  rw [wordOf_toNat] at h
  exact h

/-! ## The reduction -/

/-- The number before round `i`: the five registers from `gw i`, then the
carry `a2` and the words of the product not yet loaded. -/
def wv (mm : Mem) (b : Addr) (i : Nat) (s : State) : Nat :=
  (s.gpr (gw i)).toNat + 2 ^ 64 * (s.gpr (gw (i + 1))).toNat + 2 ^ 128 * (s.gpr (gw (i + 2))).toNat +
    2 ^ 192 * (s.gpr (gw (i + 3))).toNat + 2 ^ 256 * (s.gpr (gw (i + 4))).toNat +
    2 ^ 320 * ((s.gpr .a2).toNat + upW mm b (i + 5) (7 - i))

/-- After `i` rounds, from `s0`. -/
structure RedInv (m : Nat) (b : Addr) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clobM s0 s
  mem : s.mem = s0.mem
  cy : (s.gpr .a2).toNat ≤ 1
  val : ∃ Q, Q < 2 ^ (64 * i) ∧ wv s0.mem b i s * 2 ^ (64 * i) = prodV s0.mem b + Q * m

theorem cons_clobM {r : Reg} {l : List Reg} (hr : r ∈ clobM) (hl : ∀ x ∈ l, x ∈ clobM := by decide) :
    ∀ x ∈ r :: l, x ∈ clobM := fun x hx => by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hr
  · exact hl x hx

/-- Round `i`. -/
theorem round_ok (hm : Ok m) {b : Addr} {s0 : State} {i : Nat} (hi : i < 5) {s : State}
    (h : RedInv m b s0 i s) :
    WP isa (.block (Impl.Weierstrass.RISCV64.Gen5.round m i)) s (RedInv m b s0 (i + 1)) := by
  obtain ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34⟩ := gw_facts i hi
  obtain ⟨n0t, n02, n03, n04, n05, n06, n07, c0⟩ := gw_ne i
  obtain ⟨n1t, n12, n13, n14, n15, n16, n17, c1⟩ := gw_ne (i + 1)
  obtain ⟨n2t, n22, n23, n24, n25, n26, n27, c2⟩ := gw_ne (i + 2)
  obtain ⟨n3t, n32, n33, n34, n35, n36, n37, c3⟩ := gw_ne (i + 3)
  obtain ⟨n4t, n42, n43, n44, n45, n46, n47, c4⟩ := gw_ne (i + 4)
  obtain hd : ACC + 8 * (i + 5) + 8 ≤ 2048 := by simp only [ACC]; omega_using [hi]
  unfold Impl.Weierstrass.RISCV64.Gen5.round
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (qword_m hm i) fun s1 ⟨q1, q2, k1⟩ => ?_)
  refine WP.block_append (WP.mono (mac_m (m := m) i 1) fun s2 ⟨e2, k2⟩ => ?_)
  refine WP.block_append (WP.mono (mac_m (m := m) i 2) fun s3 ⟨e3, k3⟩ => ?_)
  refine WP.block_append (WP.mono (mac_m (m := m) i 3) fun s4 ⟨e4, k4⟩ => ?_)
  refine WP.block_append (WP.mono (mac_m (m := m) i 4) fun s5 ⟨e5, k5⟩ => ?_)
  -- The frame so far, for the load.
  obtain r5 : Rest clobM s s5 :=
    ((Keeps.rest k1).mono (cons_clobM c0)).trans <| ((Keeps.rest k2).mono (cons_clobM c1)).trans <|
      ((Keeps.rest k3).mono (cons_clobM c2)).trans <| ((Keeps.rest k4).mono (cons_clobM c3)).trans
      ((Keeps.rest k5).mono (cons_clobM c4))
  obtain hmem5 : s5.mem = s0.mem := by
    rw [k5.2.1, k4.2.1, k3.2.1, k2.2.1, k1.2.1, h.mem]
  obtain hc5 : Ctx b s5 := h.ctx.of_rest r5 (by decide)
  refine WP.block_append (ld_ok (is := []) hc5 hd (by simp only [ACC]; omega_using []) fun s6 u6 => WP.block_nil ?_)
  refine WP.mono (top_ok (d := gw i) (by simp [n02, n04, n07])) fun s7 ⟨e7, k7⟩ => ?_
  -- The quotient word, kept.
  obtain q2' : s2.gpr (gw i) = s1.gpr (gw i) := kp k2 (by simp [d01, n04, n05, n06, n07])
  obtain q3' : s3.gpr (gw i) = s1.gpr (gw i) := by rw [kp k3 (by simp [d02, n04, n05, n06, n07]), q2']
  obtain q4' : s4.gpr (gw i) = s1.gpr (gw i) := by rw [kp k4 (by simp [d03, n04, n05, n06, n07]), q3']
  rw [q2'] at e3
  rw [q3'] at e4
  rw [q4'] at e5
  -- What each step read.
  obtain w1 : s1.gpr (gw (i + 1)) = s.gpr (gw (i + 1)) := kp k1 (by simp [Ne.symm d01, n1t, n15, n14])
  rw [w1] at e2
  obtain w2 : s2.gpr (gw (i + 2)) = s.gpr (gw (i + 2)) := by
    rw [kp k2 (by simp [Ne.symm d12, n24, n25, n26, n27]), kp k1 (by simp [Ne.symm d02, n2t, n25, n24])]
  rw [w2] at e3
  obtain w3 : s3.gpr (gw (i + 3)) = s.gpr (gw (i + 3)) := by
    rw [kp k3 (by simp [Ne.symm d23, n34, n35, n36, n37]), kp k2 (by simp [Ne.symm d13, n34, n35, n36, n37]),
      kp k1 (by simp [Ne.symm d03, n3t, n35, n34])]
  rw [w3] at e4
  obtain w4 : s4.gpr (gw (i + 4)) = s.gpr (gw (i + 4)) := by
    rw [kp k4 (by simp [Ne.symm d34, n44, n45, n46, n47]), kp k3 (by simp [Ne.symm d24, n44, n45, n46, n47]),
      kp k2 (by simp [Ne.symm d14, n44, n45, n46, n47]), kp k1 (by simp [Ne.symm d04, n4t, n45, n44])]
  rw [w4] at e5
  -- The load and the carries into the top word.
  obtain hT5 : (s6.gpr (gw i)).toNat = T s0.mem b (i + 5) := by
    rw [u6.gpr, hmem5]; rfl
  obtain a4_6 : s6.gpr .a4 = s5.gpr .a4 := u6.other _ (Ne.symm n04)
  obtain a2_6 : s6.gpr .a2 = s.gpr .a2 := by
    rw [u6.other _ (Ne.symm n02), kp k5 (by simp [Ne.symm n42]),
      kp k4 (by simp [Ne.symm n32]), kp k3 (by simp [Ne.symm n22]), kp k2 (by simp [Ne.symm n12]),
      kp k1 (by simp [Ne.symm n02])]
  obtain ⟨e7, cy⟩ := e7 (by rw [a2_6]; exact h.cy)
  rw [hT5, a4_6, a2_6] at e7
  -- The new registers, read from the last state.
  obtain o1 : s7.gpr (gw (i + 1)) = s2.gpr (gw (i + 1)) := by
    rw [kp k7 (by simp [Ne.symm d01, n12, n17]), u6.other _ (Ne.symm d01),
      kp k5 (by simp [d14, n14, n15, n16, n17]), kp k4 (by simp [d13, n14, n15, n16, n17]),
      kp k3 (by simp [d12, n14, n15, n16, n17])]
  obtain o2 : s7.gpr (gw (i + 2)) = s3.gpr (gw (i + 2)) := by
    rw [kp k7 (by simp [Ne.symm d02, n22, n27]), u6.other _ (Ne.symm d02),
      kp k5 (by simp [d24, n24, n25, n26, n27]), kp k4 (by simp [d23, n24, n25, n26, n27])]
  obtain o3 : s7.gpr (gw (i + 3)) = s4.gpr (gw (i + 3)) := by
    rw [kp k7 (by simp [Ne.symm d03, n32, n37]), u6.other _ (Ne.symm d03),
      kp k5 (by simp [d34, n34, n35, n36, n37])]
  obtain o4 : s7.gpr (gw (i + 4)) = s5.gpr (gw (i + 4)) := by
    rw [kp k7 (by simp [Ne.symm d04, n42, n47]), u6.other _ (Ne.symm d04)]
  -- The frame.
  obtain hrest : Rest clobM s s7 :=
    r5.trans ((u6.rest c0).trans ((Keeps.rest k7).mono (cons_clobM c0)))
  obtain hmem : s7.mem = s0.mem := by rw [k7.2.1, u6.mem, hmem5]
  obtain hup : upW s0.mem b (i + 5) (7 - i) = T s0.mem b (i + 5) + 2 ^ 64 * upW s0.mem b (i + 6) (6 - i) := by
    rw [show 7 - i = (6 - i) + 1 by omega_using [hi]]; rfl
  obtain hM := mul5 (s1.gpr (gw i)).toNat (wd m 0) (wd m 1) (wd m 2) (wd m 3) (wd m 4)
  rw [← words5 hm.lt] at hM
  obtain key : 2 ^ 64 * wv s0.mem b (i + 1) s7 = wv s0.mem b i s + (s1.gpr (gw i)).toNat * m := by
    obtain g5 : gw (i + 1 + 4) = gw i := by rw [show i + 1 + 4 = i + 5 by omega_using [], gw_five]
    simp only [wv, show i + 1 + 1 = i + 2 by omega_using [], show i + 1 + 2 = i + 3 by omega_using [],
      show i + 1 + 3 = i + 4 by omega_using [], g5,
      show i + 1 + 5 = i + 6 by omega_using [], show 7 - (i + 1) = 6 - i by omega_using [], hup, o1, o2, o3, o4]
    rw [hM]
    omega_using [q2, e2, e3, e4, e5, e7]
  obtain ⟨Q, hQ, hv⟩ := h.val
  obtain ⟨v1, v2⟩ := round_val hQ (BitVec.isLt _) hv key
  refine ⟨h.ctx.of_rest hrest (by decide), h.rest.trans hrest, hmem, cy,
    ⟨Q + (s1.gpr (gw i)).toNat * 2 ^ (64 * i), by rw [pow64_succ]; exact v1, by rw [pow64_succ]; exact v2⟩⟩

/-- The rounds, by induction. -/
theorem rounds_ok (hm : Ok m) {b : Addr} {s0 : State} : ∀ n ≤ 5, ∀ s, RedInv m b s0 0 s →
    WP isa (.block ((List.range n).flatMap (Impl.Weierstrass.RISCV64.Gen5.round m))) s (RedInv m b s0 n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (rounds_ok hm n (by omega_using [hn]) s h) fun s1 h1 => round_ok hm (by omega_using [hn]) h1)

/-- The initial loads. -/
theorem loads_ok {b : Addr} {s : State} (hc : Ctx b s) :
    WP isa (.block ((List.range 5).map (fun j => .load .d (gw j) .a3 (ACC + 8 * j)) ++ ([.li .a2 0] : List Instr)))
      s (RedInv m b s 0) := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  refine ld_ok hc (by unfold ACC; omega_using []) (by unfold ACC; omega_using []) fun s1 u1 => ?_
  obtain hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := clobM) (by decide)) (by decide)
  refine ld_ok hc1 (by unfold ACC; omega_using []) (by unfold ACC; omega_using []) fun s2 u2 => ?_
  obtain hc2 : Ctx b s2 := hc1.of_rest (u2.rest (ws := clobM) (by decide)) (by decide)
  refine ld_ok hc2 (by unfold ACC; omega_using []) (by unfold ACC; omega_using []) fun s3 u3 => ?_
  obtain hc3 : Ctx b s3 := hc2.of_rest (u3.rest (ws := clobM) (by decide)) (by decide)
  refine ld_ok hc3 (by unfold ACC; omega_using []) (by unfold ACC; omega_using []) fun s4 u4 => ?_
  obtain hc4 : Ctx b s4 := hc3.of_rest (u4.rest (ws := clobM) (by decide)) (by decide)
  refine ld_ok hc4 (by unfold ACC; omega_using []) (by unfold ACC; omega_using []) fun s5 u5 => ?_
  obtain hc5 : Ctx b s5 := hc4.of_rest (u5.rest (ws := clobM) (by decide)) (by decide)
  refine wp_li (by decide) fun s7 u7 => WP.block_nil ?_
  obtain hr : Rest clobM s s7 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans
    (u7.rest (by decide))))))
  obtain hm : s7.mem = s.mem := by rw [u7.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain w0 : (s7.gpr (gw 0)).toNat = T s.mem b 0 := by
    rw [u7.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; rfl
  obtain w1 : (s7.gpr (gw 1)).toNat = T s.mem b 1 := by
    rw [u7.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr, u1.mem]; rfl
  obtain w2 : (s7.gpr (gw 2)).toNat = T s.mem b 2 := by
    rw [u7.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.gpr, u2.mem, u1.mem]; rfl
  obtain w3 : (s7.gpr (gw 3)).toNat = T s.mem b 3 := by
    rw [u7.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.mem, u2.mem,
      u1.mem]; rfl
  obtain w4 : (s7.gpr (gw 4)).toNat = T s.mem b 4 := by
    rw [u7.other _ (by decide), u5.gpr, u4.mem, u3.mem, u2.mem, u1.mem]; rfl
  obtain c7 : (s7.gpr .a2).toNat = 0 := by rw [u7.gpr]; rfl
  refine ⟨hc5.of_rest (u7.rest (ws := clobM) (by decide)) (by decide), hr, hm, by omega_using [c7], 0, by decide, ?_⟩
  simp only [wv, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_mul, Nat.add_zero, w0, w1, w2,
    w3, w4, c7]
  simp only [prodV, upW, Nat.reduceAdd, Nat.reduceSub]
  omega_using []

/-- The number after the rounds: `X + 2³²⁰ c`, the product's top two words
being zero. -/
theorem wv_five {mm : Mem} {b : Addr} {s : State} (hz : upW mm b 10 2 = 0) :
    wv mm b 5 s = xv s + 2 ^ 320 * (s.gpr XC).toNat := by
  simp only [wv, xv, colsV5, X, Impl.Weierstrass.RISCV64.P384Field.XR, XC, gw, GW, Nat.reduceAdd,
    Nat.reduceMod, Nat.reduceSub, List.getD_cons_zero, List.getD_cons_succ, hz, Nat.add_zero]

/-- `reduce`: `X + 2³²⁰ c` with `(X + 2³²⁰ c) 2³²⁰ = T + Q m` for some `Q < 2³²⁰`. -/
theorem reduce_ok (hm : Ok m) {b : Addr} {s : State} (hc : Ctx b s) (hz : upW s.mem b 10 2 = 0) :
    WP isa (.block (Impl.Weierstrass.RISCV64.Gen5.reduce m)) s fun s' =>
      Ctx b s' ∧ Rest clobM s s' ∧ Frame [VG.Proof.Weierstrass.RISCV64.P384Field.AR ACC b] s.mem s'.mem ∧
      (s'.gpr XC).toNat ≤ 1 ∧
      ∃ Q, Q < 2 ^ 320 ∧ (xv s' + 2 ^ 320 * (s'.gpr XC).toNat) * 2 ^ 320 = prodV s.mem b + Q * m := by
  unfold Impl.Weierstrass.RISCV64.Gen5.reduce
  refine WP.block_append (WP.mono (loads_ok (m := m) hc) fun s1 h1 => ?_)
  refine WP.mono (rounds_ok hm 5 (Nat.le_refl _) s1 h1) fun s2 h2 => ?_
  obtain ⟨Q, hQ, hv⟩ := h2.val
  refine ⟨h2.ctx, h2.rest, by rw [h2.mem]; exact Frame.refl _ _, h2.cy, Q, by simpa only [Nat.reduceMul] using hQ, ?_⟩
  rw [wv_five hz] at hv
  simpa only [Nat.reduceMul] using hv

/-! ## The sum's and the difference's words -/

theorem sumKs_getD {j : Nat} (hj : j < 5) :
    (sumKs m).getD j [] = li64 .t0 .a6 (wordOf (2 ^ 320 - m) j) := by
  obtain rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega_using [hj]
  all_goals rfl

/-- The words of `2³²⁰ - m`, as a definition of its own, which unification
treats as a constant rather than evaluating `2³²⁰`. -/
def cw (m j : Nat) : Nat := wd (2 ^ 320 - m) j

theorem cw_lt (m j : Nat) : cw m j < 2 ^ 64 := by
  unfold cw
  exact wd_lt _ _

/-- The words of `2³²⁰ - m` into `t0`. -/
theorem sumK_ok : ∀ j < 5, KOk ((sumKs m).getD j []) j (cw m) := by
  intro j hj s _
  rw [sumKs_getD hj, ← List.append_nil (li64 .t0 .a6 _)]
  exact wp_li64 (by decide) _ fun s1 e1 k1 => WP.block_nil ⟨by rw [e1, wordOf_toNat, cw], k1⟩

theorem sumK_val (hm : Ok m) : colsV (cw m) 5 + m = 2 ^ 320 := by
  have := hm.pos
  have := hm.lt
  rw [colsV5]
  simp only [cw]
  rw [← words5 (show 2 ^ 320 - m < 2 ^ 320 by omega_arith)]
  omega_using [this]

theorem subKs_getD {j : Nat} (hj : j < 5) :
    (subKs m).getD j [] = li64 .a6 .a0 (wordOf m j) ++ ([.logic .and .a6 .a6 .t0] : List Instr) := by
  obtain rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega_using [hj]
  all_goals rfl

/-- `m`'s words under the mask. -/
theorem subK_ok : ∀ j < 5, KMOk ((subKs m).getD j []) j (wd m) := by
  intro j hj s hmask
  rw [subKs_getD hj]
  obtain h := VG.Proof.Weierstrass.RISCV64.P384Order.kmW (wordOf m j) hmask
  rw [wordOf_toNat] at h
  exact h

theorem subK_val (hm : Ok m) : colsV (wd m) 5 = m := by
  rw [colsV5, ← words5 hm.lt]

/-! ## The operations -/

open VG.Proof.X448.RISCV64.R64 (al8)

/-- Montgomery's product modulo `m`. -/
abbrev mulRes (m A B r : Nat) : Prop := r < m ∧ r * 2 ^ 320 % m = A * B % m

theorem mulCore_core (hm : Ok m) :
    CoreOk (Impl.Weierstrass.RISCV64.Gen5.mulCore m) (fun _ B => B < m) (mulRes m) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB =>
    WP.mono (mulWith_ok (red := Impl.Weierstrass.RISCV64.Gen5.reduce m) (ks := sumKs m)
      (N := cw m) hm.pos (cw_lt m) sumK_ok (sumK_val hm) (fun hc hz => reduce_ok hm hc hz) hw h4 h5 h2 ha8 hb8 ho8
      ha hb ho hdb hB) fun _ ⟨v1, v2, f, g, rd, wr, sp⟩ => ⟨⟨v1, v2⟩, f, g, rd, wr, sp⟩

theorem lay_ok : Rows.LOk Impl.Weierstrass.RISCV64.Gen5.lay :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem fast_core (hm : Ok m) :
    CoreOkA (Impl.Weierstrass.RISCV64.Rows.fast Impl.Weierstrass.RISCV64.Gen5.lay m Impl.Weierstrass.RISCV64.Gen5.order)
      (fun _ B => B < m) (mulRes m) := fun {W s a bb o} hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hB => by
  obtain own : Rows.own Impl.Weierstrass.RISCV64.Gen5.lay (W + BitVec.ofNat 64 2048) = ⟨W + BitVec.ofNat 64 3776, 168⟩ :=
    congrArg (Region.mk · 168) (off_add _ _ _)
  obtain dis : ∀ x, x + 40 ≤ 3776 → ∀ i < 5, Region.Disjoint ⟨W + BitVec.ofNat 64 x + BitVec.ofNat 64 (8 * i), 8⟩
      (Rows.own Impl.Weierstrass.RISCV64.Gen5.lay (W + BitVec.ofNat 64 2048)) := fun x hx i hi => by
    rw [own, off_add]
    exact Offset.disjoint W (.inl (by omega_using [hx, hi])) (by omega_using [hx, hi]) (by decide)
  obtain disO : Region.Disjoint ⟨W + BitVec.ofNat 64 o, 40⟩
      (Rows.own Impl.Weierstrass.RISCV64.Gen5.lay (W + BitVec.ofNat 64 2048)) := by
    rw [own]
    exact Offset.disjoint W (.inl (by omega_using [ho])) (by omega_using [ho]) (by decide)
  refine WP.mono (Rows.fastWith_ok lay_ok (m := m) _ (Rows.tail_ok lay_ok (by show m < (2 ^ 64) ^ 5; exact hm.lt')
    (by have h := hm.inv; rw [← wordOf_toNat] at h; exact h)) hw.ctx h4 h5 h2 (al8 hw.al ha8) (al8 hw.al hb8) (al8 hw.al ho8)
    (hw.inR (by omega_using [ha])) (hw.inR (by omega_using [hb])) (hw.inW (by omega_using [ho])) (dis a ha) (dis bb hb) disO hB)
    fun s' ⟨v1, v2, f, g, rd, wr, sp⟩ => ⟨⟨v1, ?_⟩, ?_, fun r hr => ?_, rd, wr, sp⟩
  · have v2 : d5 s'.mem (W + BitVec.ofNat 64 o) * (2 ^ 64) ^ 5 % m = _ := v2
    simp only [← Nat.pow_mul, Nat.reduceMul] at v2
    exact v2
  · rw [own] at f
    refine f.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
  · exact g r (by revert hr; cases r <;> decide)

theorem addCore_core (hm : Ok m) :
    CoreOk (.block (Impl.Weierstrass.RISCV64.Gen5.addCore m)) (fun A B => A + B < 2 * m)
      (fun A B r => r = (A + B) % m) := by
  intro W s a bb o hw h4 h5 h2 ha8 hb8 ho8 ha hb ho _ hab
  unfold Impl.Weierstrass.RISCV64.Gen5.addCore
  refine WP.block_append (WP.mono (addSum_ok hw h4 h5 ha8 hb8 ha hb) fun s1 ⟨v1, c1, r1, m1⟩ => ?_)
  obtain hw1 : WsAt W s1 := hw.of_rest r1 (by decide)
  refine WP.mono (csubWith_ok (N := cw m) (cw_lt m) sumK_ok (sumK_val hm) (O := W + BitVec.ofNat 64 o)
    (by rw [r1.gpr _ (by decide), h2]) (al8 hw.al ho8) (hw1.inW ho) c1 (by rw [v1]; exact hab))
    fun s2 ⟨v2, f2, g2, rd2, wr2, sp2⟩ => ?_
  refine ⟨by rw [v2, v1], by rw [← m1]; exact f2.mono (by simp), fun r hr => ?_, by rw [rd2, r1.rd],
    by rw [wr2, r1.wr], by rw [sp2, r1.sp]⟩
  obtain hC : r ∉ clobC := fun h => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h | h | h | h <;> simp [h])
  rw [g2 r hC, r1.gpr r hr]

theorem subCore_core (hm : Ok m) :
    CoreOk (.block (Impl.Weierstrass.RISCV64.Gen5.subCore m)) (fun A B => A < m ∧ B < m)
      (fun A B r => r = (A + m - B) % m) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho _ hAB =>
    WP.mono (subWith_ok (ks := subKs m) (PW := wd m) (wd_lt m) subK_ok (subK_val hm) hw h4 h5 h2 ha8 hb8 ho8 ha hb
      ho hAB.1 hAB.2) fun _ ⟨v, f, g, rd, wr, sp⟩ => ⟨v, f.mono (by simp), g, rd, wr, sp⟩

/-! ## The contracts -/

open VG.Impl.Weierstrass.RISCV64.Gen5 (fn fnA SA SB SO unpack pack mulCore addCore subCore mulFn addFn subFn)
open VG.Impl.Weierstrass.Mont (numAt Keeps Modulus Fits)
open VG.Proof.Weierstrass.RISCV64 (offArg rvPre arg res rvPub mulRV addRV subRV)

theorem numAt_d5 (mm : Mem) (W : Addr) (o : BitVec 32) : numAt mm W o 5 = d5 mm (W + BitVec.ofNat 64 o.toNat) := by
  have h := VG.Proof.Mont.read_eq_wordsVal mm (W + BitVec.ofNat 64 o.toNat) 5 0
  simp only [VG.Proof.Mont.off, BitVec.add_zero] at h
  rw [numAt, h]
  simp only [VG.Proof.Mont.wordsVal, VG.Proof.Mont.word, VG.Proof.Mont.off, d5, colsV,
    VG.Proof.X448.RISCV64.R64.dw, Nat.reduceAdd, Nat.mul_zero, Nat.mul_one, Nat.reduceMul]
  omega_using []

/-- A byte of the working space outside a range of it. -/
theorem byte_out {W : Addr} {i e k : Nat} (hi : i + 1 ≤ 8192) (he : e + k ≤ 8192) (h : i < e ∨ e + k ≤ i) :
    ¬ (⟨W + BitVec.ofNat 64 e, k⟩ : Region).Contains (W + BitVec.ofNat 64 i) 1 := fun hc =>
  Offset.disjoint W (d := i) (n := 1) (e := e) (k := k) (by omega_using [h]) (by omega_using [hi]) (by omega_using [he]) _
    (Region.contains_self _ _) hc

/-- The regions the functions write keep every byte the contracts do. -/
theorem keeps_of_frame {W : Addr} {o : BitVec 32} (ho : o.toNat + 40 ≤ 3776) {mm mm' : Mem}
    (hf : Frame (fnW W o.toNat) mm mm') : Keeps 5 W o mm mm' := by
  intro i hi hown hoi
  simp only [Impl.Weierstrass.Mont.wsBytes, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes] at hi hown
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact byte_out (by omega_using [hi]) (by omega_using []) (by omega_using [hown])
  · exact byte_out (by omega_using [hi]) (by omega_using [ho]) hoi

variable {S : Modulus}

/-- `fn core` meets a contract by register, from `fn_ok`. -/
theorem fn_rv (hk : S.k = 5) {core : Prog isa} {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop}
    (hcore : CoreOk core pre res) {s : State} (hs : rvPre S s) (hp : pre (arg S s .a2) (arg S s .a3)) :
    ∃ t s', Exec isa (fn core) s t s' ∧ abiPreserved s s' ∧
      res (arg S s .a2) (arg S s .a3) (numAt s'.mem (s.gpr .a0) (offArg s .a1) 5) ∧
      Keeps 5 (s.gpr .a0) (offArg s .a1) s.mem s'.mem := by
  obtain ⟨-, hwr, hfit, ⟨fo, fa, fb⟩, hal⟩ := hs
  simp only [Fits, hk, VG.Proof.Weierstrass.RISCV64.rvOwn_le (show 5 ≤ 6 by decide), Impl.Weierstrass.Mont.ownAt,
    Impl.Weierstrass.Mont.ownBytes] at fo fa fb
  simp only [arg, hk, numAt_d5] at hp ⊢
  obtain ⟨t, s', he, v, f, g, -, -, sp⟩ := fn_ok hcore rfl hal (by rw [hwr]; simp) hfit fo fa fb hp
  refine ⟨t, s', he, ⟨fun r hr => g r (by revert hr; revert r; decide), sp, g _ (by decide)⟩, v,
    keeps_of_frame fo f⟩

/-- `fnA core` meets a contract by register for offsets as the calls set
them, from `fnA_ok`. -/
theorem fnA_rv (hk : S.k = 5) {core : Prog isa} {pre : Nat → Nat → Prop}
    {res : Nat → Nat → Nat → Prop} (hcore : CoreOkA core pre res) {s : State} (hs : rvPre S s)
    (hoff : VG.Proof.Weierstrass.RISCV64.OffsOk s) (hp : pre (arg S s .a2) (arg S s .a3)) :
    ∃ t s', Exec isa (fnA core) s t s' ∧ abiPreserved s s' ∧
      res (arg S s .a2) (arg S s .a3) (numAt s'.mem (s.gpr .a0) (offArg s .a1) 5) ∧
      Keeps 5 (s.gpr .a0) (offArg s .a1) s.mem s'.mem := by
  obtain ⟨-, hwr, hfit, ⟨fo, fa, fb⟩, hal⟩ := hs
  simp only [Fits, hk, VG.Proof.Weierstrass.RISCV64.rvOwn_le (show 5 ≤ 6 by decide), Impl.Weierstrass.Mont.ownAt,
    Impl.Weierstrass.Mont.ownBytes] at fo fa fb
  simp only [arg, hk, numAt_d5] at hp ⊢
  obtain ⟨t, s', he, v, f, g, -, -, sp⟩ := fnA_ok hcore rfl hal (by rw [hwr]; simp) hfit fo fa fb
    (hoff _ (by simp)) (hoff _ (by simp)) (hoff _ (by simp)) hp
  refine ⟨t, s', he, ⟨fun r hr => g r (by revert hr; revert r; decide), sp, g _ (by decide)⟩, v,
    keeps_of_frame fo f⟩

theorem mul_rv (hk : S.k = 5) (hm : Ok S.m) (s : State) (hs : (mulRV S).pre s) :
    ∃ t s', Exec isa (mulFn S.m) s t s' ∧ abiPreserved s s' ∧ (mulRV S).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fn_rv hk (@mulCore_core S.m hm) hs.1 (by exact hs.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v1,
    by simp only [res, Impl.Weierstrass.Mont.Modulus.R, hk, Nat.reduceMul]; exact v2, by rw [hk]; exact k⟩

theorem add_rv (hk : S.k = 5) (hm : Ok S.m) (s : State) (hs : (addRV S).pre s) :
    ∃ t s', Exec isa (addFn S.m) s t s' ∧ abiPreserved s s' ∧ (addRV S).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv hk (@addCore_core S.m hm) hs.1 (by exact hs.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

theorem sub_rv (hk : S.k = 5) (hm : Ok S.m) (s : State) (hs : (subRV S).pre s) :
    ∃ t s', Exec isa (subFn S.m) s t s' ∧ abiPreserved s s' ∧ (subRV S).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv hk (@subCore_core S.m hm) hs.1 (by exact hs.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

theorem mulA_rv (hk : S.k = 5) (hm : Ok S.m) (s : State)
    (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV S)).pre s) :
    ∃ t s', Exec isa (Impl.Weierstrass.RISCV64.Gen5.mulFnA S.m) s t s' ∧ abiPreserved s s' ∧ (mulRV S).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fnA_rv hk (@fast_core S.m hm) hs.1.1 hs.2 (by exact hs.1.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v1,
    by simp only [res, Impl.Weierstrass.Mont.Modulus.R, hk, Nat.reduceMul]; exact v2, by rw [hk]; exact k⟩

theorem addA_rv (hk : S.k = 5) (hm : Ok S.m) (s : State)
    (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV S)).pre s) :
    ∃ t s', Exec isa (Impl.Weierstrass.RISCV64.Gen5.addFnA S.m) s t s' ∧ abiPreserved s s' ∧ (addRV S).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fnA_rv hk (@CoreOk.toA _ _ _ (@addCore_core S.m hm)) hs.1.1 hs.2 (by exact hs.1.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

theorem subA_rv (hk : S.k = 5) (hm : Ok S.m) (s : State)
    (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV S)).pre s) :
    ∃ t s', Exec isa (Impl.Weierstrass.RISCV64.Gen5.subFnA S.m) s t s' ∧ abiPreserved s s' ∧ (subRV S).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fnA_rv hk (@CoreOk.toA _ _ _ (@subCore_core S.m hm)) hs.1.1 hs.2 (by exact hs.1.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

end VG.Proof.Weierstrass.RISCV64.Gen5
