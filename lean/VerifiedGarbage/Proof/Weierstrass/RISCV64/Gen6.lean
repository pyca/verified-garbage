module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen6
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Fn
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Verified
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.FieldRV
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Fn
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Order.Fn
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Arithmetic modulo a six-word modulus on RISC-V

The operations of `Impl/Weierstrass/RISCV64/Gen6.lean` meet `CoreOk`
(`mulCore_core`, `addCore_core`, `subCore_core`) for every modulus `m` with
`Ok m` (odd, below `2³⁸⁴`, its quotient constant right), by the lemmas of
P-384's field (`mulWith_ok`, `csubWith_ok`, `subWith_ok`), from the reduction
(`reduce_ok`), the words of `2³⁸⁴ - m` (`sumK_ok`) and `m`'s words under a
mask (P-384's order's `kmW`).

The reduction keeps six words in registers (`RedInv`): round `i` takes the
quotient word and the carry out of `w + q m₀` (`qword_ok`, Gen4's
`mont_carry`), adds each `q mⱼ` with its carries (`mac_ok`), loads the next
word of the product and adds the carries into it (Gen4's `top_ok`), and the
sums add up (`round_arith`).

The functions then meet the shared contracts of
`Proof/Weierstrass/MontContract.lean` for a modulus `S` of six words with
`Ok S.m` as P-384's do (`Proof/Weierstrass/RISCV64/P384Field/Verified.lean`,
whose lemmas this uses), given that the taint analysis finds each operation
constant time (`CtOk`), which a modulus's own module proves of its code
(`by taint_decide`): `mul_verified`, `add_verified`, `sub_verified`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.Gen6

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide
open VG.Impl.Weierstrass.RISCV64.P384Field (ACC X XC)
open VG.Impl.Weierstrass.RISCV64.Gen6 (gw GW qword mac sumKs subKs)
open VG.Impl.Weierstrass.RISCV64.Gen4 (wordOf negInv top)
open VG.Proof.Weierstrass.RISCV64.Gen4 (wd wordOf_toNat wd_lt mont_carry prod_le round_val top_ok)
open VG.Proof.Weierstrass.RISCV64.P384Field (T upW prodV xv clobM KOk KMOk)
open VG.Proof.Weierstrass.RISCV64.P256Order (wp_li64 wp_mulhu ofNat_lt add_toNat kp pow64_succ)
open VG.Proof.Weierstrass.RISCV64.P256Field (sltu_toNat upd_keeps add1_ok)
open VG.Proof.X25519.RISCV64 (Ctx Rest wp_mul)
open VG.Proof.X448.RISCV64.R64 (dw ld_ok clob64 Keeps.rest colsV)
open VG.Impl.Words.RISCV64 (li64 mulWide)

/-! ## Arithmetic -/

theorem words6 {x : Nat} (h : x < 2 ^ 384) :
    x = wd x 0 + 2 ^ 64 * wd x 1 + 2 ^ 128 * wd x 2 + 2 ^ 192 * wd x 3 + 2 ^ 256 * wd x 4 +
      2 ^ 320 * wd x 5 := by
  simp only [wd, show 64 * 0 = 0 from rfl, show 64 * 1 = 64 from rfl, show 64 * 2 = 128 from rfl,
    show 64 * 3 = 192 from rfl, show 64 * 4 = 256 from rfl, show 64 * 5 = 320 from rfl, Nat.pow_zero,
    Nat.div_one]
  omega

theorem colsV6 (f : Nat → Nat) :
    colsV f 6 = f 0 + 2 ^ 64 * f 1 + 2 ^ 128 * f 2 + 2 ^ 192 * f 3 + 2 ^ 256 * f 4 + 2 ^ 320 * f 5 := by
  simp only [colsV]
  omega

/-- What the code needs of a modulus: odd, below `2³⁸⁴` (stated as `(2⁶⁴)⁶`,
which `decide` evaluates), and `negInv m` its quotient constant,
`-m⁻¹ mod 2⁶⁴`. -/
structure Ok (m : Nat) : Prop where
  pos : 0 < m
  lt' : m < (2 ^ 64) ^ 6
  inv : (wd m 0 * (negInv m % 2 ^ 64) + 1) % 2 ^ 64 = 0

theorem Ok.lt {m : Nat} (h : Ok m) : m < 2 ^ 384 := by
  have := h.lt'
  simp only [← Nat.pow_mul, Nat.reduceMul] at this
  exact this

theorem mul6 (q a b c d e f : Nat) :
    q * (a + 2 ^ 64 * b + 2 ^ 128 * c + 2 ^ 192 * d + 2 ^ 256 * e + 2 ^ 320 * f) =
      q * a + 2 ^ 64 * (q * b) + 2 ^ 128 * (q * c) + 2 ^ 192 * (q * d) + 2 ^ 256 * (q * e) +
        2 ^ 320 * (q * f) := by
  simp only [Nat.mul_add, Nat.mul_left_comm q]

/-- The numbers of a round. -/
theorem round_arith {M q w0 w1 w2 w3 w4 w5 w6 cy U c0 c1 c2 c3 c4 c5 w1' w2' w3' w4' w5' w6' cy'
    P0 P1 P2 P3 P4 P5 : Nat}
    (hP : q * M = P0 + 2 ^ 64 * P1 + 2 ^ 128 * P2 + 2 ^ 192 * P3 + 2 ^ 256 * P4 + 2 ^ 320 * P5)
    (F0 : w0 + P0 = 2 ^ 64 * c0) (F1 : w1' + 2 ^ 64 * c1 = w1 + P1 + c0)
    (F2 : w2' + 2 ^ 64 * c2 = w2 + P2 + c1) (F3 : w3' + 2 ^ 64 * c3 = w3 + P3 + c2)
    (F4 : w4' + 2 ^ 64 * c4 = w4 + P4 + c3) (F5 : w5' + 2 ^ 64 * c5 = w5 + P5 + c4)
    (F6 : w6' + 2 ^ 64 * cy' = w6 + c5 + cy) :
    2 ^ 64 * (w1' + 2 ^ 64 * w2' + 2 ^ 128 * w3' + 2 ^ 192 * w4' + 2 ^ 256 * w5' + 2 ^ 320 * w6' +
        2 ^ 384 * (cy' + U)) =
      w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3 + 2 ^ 256 * w4 + 2 ^ 320 * w5 +
        2 ^ 384 * (cy + (w6 + 2 ^ 64 * U)) + q * M := by
  rw [hP]
  omega

/-! ## The registers -/

theorem gw_ne (j : Nat) : gw j ≠ .t0 ∧ gw j ≠ .a2 ∧ gw j ≠ .a3 ∧ gw j ≠ .a4 ∧ gw j ≠ .a5 ∧
    gw j ≠ .a6 ∧ gw j ≠ .a7 ∧ gw j ∈ clobM := by
  have : j % 6 < 6 := Nat.mod_lt _ (by decide)
  obtain h | h | h | h | h | h :
      j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 2 ∨ j % 6 = 3 ∨ j % 6 = 4 ∨ j % 6 = 5 := by omega
  all_goals simp only [gw, GW, h]; decide

theorem gw_six (i : Nat) : gw (i + 6) = gw i := by simp only [gw, Nat.add_mod_right]

/-- The six registers of a round are distinct. -/
theorem gw_facts : ∀ i < 6,
    gw i ≠ gw (i + 1) ∧ gw i ≠ gw (i + 2) ∧ gw i ≠ gw (i + 3) ∧ gw i ≠ gw (i + 4) ∧ gw i ≠ gw (i + 5) ∧
    gw (i + 1) ≠ gw (i + 2) ∧ gw (i + 1) ≠ gw (i + 3) ∧ gw (i + 1) ≠ gw (i + 4) ∧ gw (i + 1) ≠ gw (i + 5) ∧
    gw (i + 2) ≠ gw (i + 3) ∧ gw (i + 2) ≠ gw (i + 4) ∧ gw (i + 2) ≠ gw (i + 5) ∧
    gw (i + 3) ≠ gw (i + 4) ∧ gw (i + 3) ≠ gw (i + 5) ∧ gw (i + 4) ≠ gw (i + 5) := by
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
  have hq2 : s2.gpr r = s.gpr r * ni := by rw [u2.gpr, e1, k1.1 _ (by simp [r0, ra])]
  have q3 : s3.gpr r = s2.gpr r := k3.1 _ (by simp [r4, ra])
  have q7 : s7.gpr r = s2.gpr r := by
    rw [u7.other _ r4, u6.other _ ra, u5.other _ ra, u4.other _ r4, q3]
  have hqn : (s2.gpr r).toNat = (s.gpr r).toNat * ni.toNat % 2 ^ 64 := by rw [hq2, BitVec.toNat_mul]
  have hA4 : s4.gpr .a4 = BitVec.ofNat 64 ((s2.gpr r).toNat * m0.toNat / 2 ^ 64) := by
    rw [u4.gpr, q3, e3]
  have hB : (s6.gpr .a5).toNat = if 0 < (s2.gpr r).toNat then 1 else 0 := by
    rw [u6.gpr, sltu_toNat, u5.gpr, u5.other _ ra, u4.other _ r4, q3]; rfl
  have a4_6 : s6.gpr .a4 = s4.gpr .a4 := by rw [u6.other _ (by decide), u5.other _ (by decide)]
  have pl := prod_le (s2.gpr r) m0
  have bA4 : (s2.gpr r).toNat * m0.toNat / 2 ^ 64 < 2 ^ 64 - 1 := Nat.div_lt_of_lt_mul (by omega)
  have eA4 : (s4.gpr .a4).toNat = (s2.gpr r).toNat * m0.toNat / 2 ^ 64 := by
    rw [hA4]; exact ofNat_lt (by omega)
  have bB : (s6.gpr .a5).toNat ≤ 1 := by rw [hB]; split <;> decide
  have e7 : (s7.gpr .a4).toNat = (s4.gpr .a4).toNat + (s6.gpr .a5).toNat := by
    rw [u7.gpr, a4_6]; exact add_toNat (by rw [a4_6] at *; omega)
  have mc := mont_carry hinv (s.gpr r).isLt
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
  have hq1 : s1.gpr q = s.gpr q := k1.1 _ (by simp [q6, q7])
  rw [hq1, e1] at m2
  have a4_2 : s2.gpr .a4 = s.gpr .a4 := by rw [k2.1 _ (by decide), k1.1 _ (by decide)]
  rw [a4_2] at e3
  have a6_3 : s3.gpr .a6 = s2.gpr .a6 := k3.1 _ (by decide)
  have d4' : s4.gpr d = s.gpr d := by
    rw [u4.other _ d6, k3.1 _ (by simp [d5, d7]), k2.1 _ (by simp [d5, d6]), k1.1 _ (by simp [d6, d7])]
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

variable {m : Nat}

theorem qword_m (hm : Ok m) (i : Nat) {s : State} :
    WP isa (.block (qword m i)) s fun s' =>
      (s'.gpr (gw i)).toNat = (s.gpr (gw i)).toNat * (negInv m % 2 ^ 64) % 2 ^ 64 ∧
      (s.gpr (gw i)).toNat + (s'.gpr (gw i)).toNat * wd m 0 = 2 ^ 64 * (s'.gpr .a4).toNat ∧
      Keeps [gw i, .t0, .a5, .a4] s s' := by
  obtain ⟨n0, -, -, n4, n5, -, -, -⟩ := gw_ne i
  have h := qword_ok (r := gw i) (ni := BitVec.ofNat 64 (negInv m)) (m0 := wordOf m 0) (s := s)
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
  have h := mac_ok (q := gw i) (d := gw (i + j)) (wordOf m j) (s := s) (by simp [n4, n5, n6, n7])
    (by simp [m4, m5, m6, m7])
  rw [wordOf_toNat] at h
  exact h

/-! ## The reduction -/

/-- The number before round `i`: the six registers from `gw i`, then the
carry `a2` and the words of the product not yet loaded. -/
def wv (mm : Mem) (b : Addr) (i : Nat) (s : State) : Nat :=
  (s.gpr (gw i)).toNat + 2 ^ 64 * (s.gpr (gw (i + 1))).toNat + 2 ^ 128 * (s.gpr (gw (i + 2))).toNat +
    2 ^ 192 * (s.gpr (gw (i + 3))).toNat + 2 ^ 256 * (s.gpr (gw (i + 4))).toNat +
    2 ^ 320 * (s.gpr (gw (i + 5))).toNat + 2 ^ 384 * ((s.gpr .a2).toNat + upW mm b (i + 6) (6 - i))

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
theorem round_ok (hm : Ok m) {b : Addr} {s0 : State} {i : Nat} (hi : i < 6) {s : State}
    (h : RedInv m b s0 i s) :
    WP isa (.block (Impl.Weierstrass.RISCV64.Gen6.round m i)) s (RedInv m b s0 (i + 1)) := by
  obtain ⟨d01, d02, d03, d04, d05, d12, d13, d14, d15, d23, d24, d25, d34, d35, d45⟩ := gw_facts i hi
  obtain ⟨n0t, n02, n03, n04, n05, n06, n07, c0⟩ := gw_ne i
  obtain ⟨n1t, n12, n13, n14, n15, n16, n17, c1⟩ := gw_ne (i + 1)
  obtain ⟨n2t, n22, n23, n24, n25, n26, n27, c2⟩ := gw_ne (i + 2)
  obtain ⟨n3t, n32, n33, n34, n35, n36, n37, c3⟩ := gw_ne (i + 3)
  obtain ⟨n4t, n42, n43, n44, n45, n46, n47, c4⟩ := gw_ne (i + 4)
  obtain ⟨n5t, n52, n53, n54, n55, n56, n57, c5⟩ := gw_ne (i + 5)
  have hd : ACC + 8 * (i + 6) + 8 ≤ 2048 := by simp only [ACC]; omega
  unfold Impl.Weierstrass.RISCV64.Gen6.round
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (qword_m hm i) fun s1 ⟨q1, q2, k1⟩ => ?_)
  refine WP.block_append (WP.mono (mac_m (m := m) i 1) fun s2 ⟨e2, k2⟩ => ?_)
  refine WP.block_append (WP.mono (mac_m (m := m) i 2) fun s3 ⟨e3, k3⟩ => ?_)
  refine WP.block_append (WP.mono (mac_m (m := m) i 3) fun s4 ⟨e4, k4⟩ => ?_)
  refine WP.block_append (WP.mono (mac_m (m := m) i 4) fun s5 ⟨e5, k5⟩ => ?_)
  refine WP.block_append (WP.mono (mac_m (m := m) i 5) fun s6 ⟨e6, k6⟩ => ?_)
  -- The frame so far, for the load.
  have r6 : Rest clobM s s6 :=
    ((Keeps.rest k1).mono (cons_clobM c0)).trans <| ((Keeps.rest k2).mono (cons_clobM c1)).trans <|
      ((Keeps.rest k3).mono (cons_clobM c2)).trans <| ((Keeps.rest k4).mono (cons_clobM c3)).trans <|
      ((Keeps.rest k5).mono (cons_clobM c4)).trans ((Keeps.rest k6).mono (cons_clobM c5))
  have hmem6 : s6.mem = s0.mem := by
    rw [k6.2.1, k5.2.1, k4.2.1, k3.2.1, k2.2.1, k1.2.1, h.mem]
  have hc6 : Ctx b s6 := h.ctx.of_rest r6 (by decide)
  refine WP.block_append (ld_ok (is := []) hc6 hd (by simp only [ACC]; omega) fun s7 u7 => WP.block_nil ?_)
  refine WP.mono (top_ok (d := gw i) (by simp [n02, n04, n07])) fun s8 ⟨e8, k8⟩ => ?_
  -- The quotient word, kept.
  have q2' : s2.gpr (gw i) = s1.gpr (gw i) := kp k2 (by simp [d01, n04, n05, n06, n07])
  have q3' : s3.gpr (gw i) = s1.gpr (gw i) := by rw [kp k3 (by simp [d02, n04, n05, n06, n07]), q2']
  have q4' : s4.gpr (gw i) = s1.gpr (gw i) := by rw [kp k4 (by simp [d03, n04, n05, n06, n07]), q3']
  have q5' : s5.gpr (gw i) = s1.gpr (gw i) := by rw [kp k5 (by simp [d04, n04, n05, n06, n07]), q4']
  rw [q2'] at e3
  rw [q3'] at e4
  rw [q4'] at e5
  rw [q5'] at e6
  -- What each step read.
  have w1 : s1.gpr (gw (i + 1)) = s.gpr (gw (i + 1)) := kp k1 (by simp [Ne.symm d01, n1t, n15, n14])
  rw [w1] at e2
  have w2 : s2.gpr (gw (i + 2)) = s.gpr (gw (i + 2)) := by
    rw [kp k2 (by simp [Ne.symm d12, n24, n25, n26, n27]), kp k1 (by simp [Ne.symm d02, n2t, n25, n24])]
  rw [w2] at e3
  have w3 : s3.gpr (gw (i + 3)) = s.gpr (gw (i + 3)) := by
    rw [kp k3 (by simp [Ne.symm d23, n34, n35, n36, n37]), kp k2 (by simp [Ne.symm d13, n34, n35, n36, n37]),
      kp k1 (by simp [Ne.symm d03, n3t, n35, n34])]
  rw [w3] at e4
  have w4 : s4.gpr (gw (i + 4)) = s.gpr (gw (i + 4)) := by
    rw [kp k4 (by simp [Ne.symm d34, n44, n45, n46, n47]), kp k3 (by simp [Ne.symm d24, n44, n45, n46, n47]),
      kp k2 (by simp [Ne.symm d14, n44, n45, n46, n47]), kp k1 (by simp [Ne.symm d04, n4t, n45, n44])]
  rw [w4] at e5
  have w5 : s5.gpr (gw (i + 5)) = s.gpr (gw (i + 5)) := by
    rw [kp k5 (by simp [Ne.symm d45, n54, n55, n56, n57]), kp k4 (by simp [Ne.symm d35, n54, n55, n56, n57]),
      kp k3 (by simp [Ne.symm d25, n54, n55, n56, n57]), kp k2 (by simp [Ne.symm d15, n54, n55, n56, n57]),
      kp k1 (by simp [Ne.symm d05, n5t, n55, n54])]
  rw [w5] at e6
  -- The load and the carries into the top word.
  have hT6 : (s7.gpr (gw i)).toNat = T s0.mem b (i + 6) := by
    rw [u7.gpr, hmem6]; rfl
  have a4_7 : s7.gpr .a4 = s6.gpr .a4 := u7.other _ (Ne.symm n04)
  have a2_7 : s7.gpr .a2 = s.gpr .a2 := by
    rw [u7.other _ (Ne.symm n02), kp k6 (by simp [Ne.symm n52]), kp k5 (by simp [Ne.symm n42]),
      kp k4 (by simp [Ne.symm n32]), kp k3 (by simp [Ne.symm n22]), kp k2 (by simp [Ne.symm n12]),
      kp k1 (by simp [Ne.symm n02])]
  obtain ⟨e8, cy⟩ := e8 (by rw [a2_7]; exact h.cy)
  rw [hT6, a4_7, a2_7] at e8
  -- The new registers, read from the last state.
  have o1 : s8.gpr (gw (i + 1)) = s2.gpr (gw (i + 1)) := by
    rw [kp k8 (by simp [Ne.symm d01, n12, n17]), u7.other _ (Ne.symm d01),
      kp k6 (by simp [d15, n14, n15, n16, n17]), kp k5 (by simp [d14, n14, n15, n16, n17]),
      kp k4 (by simp [d13, n14, n15, n16, n17]), kp k3 (by simp [d12, n14, n15, n16, n17])]
  have o2 : s8.gpr (gw (i + 2)) = s3.gpr (gw (i + 2)) := by
    rw [kp k8 (by simp [Ne.symm d02, n22, n27]), u7.other _ (Ne.symm d02),
      kp k6 (by simp [d25, n24, n25, n26, n27]), kp k5 (by simp [d24, n24, n25, n26, n27]),
      kp k4 (by simp [d23, n24, n25, n26, n27])]
  have o3 : s8.gpr (gw (i + 3)) = s4.gpr (gw (i + 3)) := by
    rw [kp k8 (by simp [Ne.symm d03, n32, n37]), u7.other _ (Ne.symm d03),
      kp k6 (by simp [d35, n34, n35, n36, n37]), kp k5 (by simp [d34, n34, n35, n36, n37])]
  have o4 : s8.gpr (gw (i + 4)) = s5.gpr (gw (i + 4)) := by
    rw [kp k8 (by simp [Ne.symm d04, n42, n47]), u7.other _ (Ne.symm d04),
      kp k6 (by simp [d45, n44, n45, n46, n47])]
  have o5 : s8.gpr (gw (i + 5)) = s6.gpr (gw (i + 5)) := by
    rw [kp k8 (by simp [Ne.symm d05, n52, n57]), u7.other _ (Ne.symm d05)]
  -- The frame.
  have hrest : Rest clobM s s8 :=
    r6.trans ((u7.rest c0).trans ((Keeps.rest k8).mono (cons_clobM c0)))
  have hmem : s8.mem = s0.mem := by rw [k8.2.1, u7.mem, hmem6]
  have hup : upW s0.mem b (i + 6) (6 - i) = T s0.mem b (i + 6) + 2 ^ 64 * upW s0.mem b (i + 7) (5 - i) := by
    rw [show 6 - i = (5 - i) + 1 by omega]; rfl
  have hM := mul6 (s1.gpr (gw i)).toNat (wd m 0) (wd m 1) (wd m 2) (wd m 3) (wd m 4) (wd m 5)
  rw [← words6 hm.lt] at hM
  have key : 2 ^ 64 * wv s0.mem b (i + 1) s8 = wv s0.mem b i s + (s1.gpr (gw i)).toNat * m := by
    have g6 : gw (i + 1 + 5) = gw i := by rw [show i + 1 + 5 = i + 6 by omega, gw_six]
    simp only [wv, show i + 1 + 1 = i + 2 by omega, show i + 1 + 2 = i + 3 by omega,
      show i + 1 + 3 = i + 4 by omega, show i + 1 + 4 = i + 5 by omega, g6,
      show i + 1 + 6 = i + 7 by omega, show 6 - (i + 1) = 5 - i by omega, hup, o1, o2, o3, o4, o5]
    rw [hM]
    omega
  obtain ⟨Q, hQ, hv⟩ := h.val
  obtain ⟨v1, v2⟩ := round_val hQ (BitVec.isLt _) hv key
  refine ⟨h.ctx.of_rest hrest (by decide), h.rest.trans hrest, hmem, cy,
    ⟨Q + (s1.gpr (gw i)).toNat * 2 ^ (64 * i), by rw [pow64_succ]; exact v1, by rw [pow64_succ]; exact v2⟩⟩

/-- The rounds, by induction. -/
theorem rounds_ok (hm : Ok m) {b : Addr} {s0 : State} : ∀ n ≤ 6, ∀ s, RedInv m b s0 0 s →
    WP isa (.block ((List.range n).flatMap (Impl.Weierstrass.RISCV64.Gen6.round m))) s (RedInv m b s0 n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (rounds_ok hm n (by omega) s h) fun s1 h1 => round_ok hm (by omega) h1)

/-- The initial loads. -/
theorem loads_ok {b : Addr} {s : State} (hc : Ctx b s) :
    WP isa (.block ((List.range 6).map (fun j => .load .d (gw j) .a3 (ACC + 8 * j)) ++ ([.li .a2 0] : List Instr)))
      s (RedInv m b s 0) := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  refine ld_ok hc (by unfold ACC; omega) (by unfold ACC; omega) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := clobM) (by decide)) (by decide)
  refine ld_ok hc1 (by unfold ACC; omega) (by unfold ACC; omega) fun s2 u2 => ?_
  have hc2 : Ctx b s2 := hc1.of_rest (u2.rest (ws := clobM) (by decide)) (by decide)
  refine ld_ok hc2 (by unfold ACC; omega) (by unfold ACC; omega) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := hc2.of_rest (u3.rest (ws := clobM) (by decide)) (by decide)
  refine ld_ok hc3 (by unfold ACC; omega) (by unfold ACC; omega) fun s4 u4 => ?_
  have hc4 : Ctx b s4 := hc3.of_rest (u4.rest (ws := clobM) (by decide)) (by decide)
  refine ld_ok hc4 (by unfold ACC; omega) (by unfold ACC; omega) fun s5 u5 => ?_
  have hc5 : Ctx b s5 := hc4.of_rest (u5.rest (ws := clobM) (by decide)) (by decide)
  refine ld_ok hc5 (by unfold ACC; omega) (by unfold ACC; omega) fun s6 u6 => ?_
  have hc6 : Ctx b s6 := hc5.of_rest (u6.rest (ws := clobM) (by decide)) (by decide)
  refine wp_li (by decide) fun s7 u7 => WP.block_nil ?_
  have hr : Rest clobM s s7 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans
    ((u6.rest (by decide)).trans (u7.rest (by decide)))))))
  have hm : s7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have w0 : (s7.gpr (gw 0)).toNat = T s.mem b 0 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; rfl
  have w1 : (s7.gpr (gw 1)).toNat = T s.mem b 1 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr, u1.mem]; rfl
  have w2 : (s7.gpr (gw 2)).toNat = T s.mem b 2 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.gpr, u2.mem, u1.mem]; rfl
  have w3 : (s7.gpr (gw 3)).toNat = T s.mem b 3 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.mem, u2.mem,
      u1.mem]; rfl
  have w4 : (s7.gpr (gw 4)).toNat = T s.mem b 4 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.gpr, u4.mem, u3.mem, u2.mem, u1.mem]; rfl
  have w5 : (s7.gpr (gw 5)).toNat = T s.mem b 5 := by
    rw [u7.other _ (by decide), u6.gpr, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]; rfl
  have c7 : (s7.gpr .a2).toNat = 0 := by rw [u7.gpr]; rfl
  refine ⟨hc6.of_rest (u7.rest (ws := clobM) (by decide)) (by decide), hr, hm, by omega, 0, by decide, ?_⟩
  simp only [wv, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_mul, Nat.add_zero, w0, w1, w2,
    w3, w4, w5, c7]
  simp only [prodV, upW, Nat.reduceAdd, Nat.reduceSub]
  omega

/-- `reduce`: `X + 2³⁸⁴ c` with `(X + 2³⁸⁴ c) 2³⁸⁴ = T + Q m` for some `Q < 2³⁸⁴`. -/
theorem reduce_ok (hm : Ok m) {b : Addr} {s : State} (hc : Ctx b s) :
    WP isa (.block (Impl.Weierstrass.RISCV64.Gen6.reduce m)) s fun s' =>
      Ctx b s' ∧ Rest clobM s s' ∧ Frame [VG.Proof.Weierstrass.RISCV64.P384Field.AR ACC b] s.mem s'.mem ∧
      (s'.gpr XC).toNat ≤ 1 ∧
      ∃ Q, Q < 2 ^ 384 ∧ (xv s' + 2 ^ 384 * (s'.gpr XC).toNat) * 2 ^ 384 = prodV s.mem b + Q * m := by
  unfold Impl.Weierstrass.RISCV64.Gen6.reduce
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (loads_ok (m := m) hc) fun s1 h1 => ?_)
  refine WP.block_append (WP.mono (rounds_ok hm 6 (Nat.le_refl _) s1 h1) fun s2 h2 => ?_)
  refine wp_addi (imm := 0) (by decide) fun s3 u3 => WP.block_nil ?_
  have hr : Rest clobM s s3 := h2.rest.trans (u3.rest (by decide))
  obtain ⟨Q, hQ, hv⟩ := h2.val
  have x5 : s3.gpr .a4 = s2.gpr .a0 := by rw [u3.gpr]; simp
  have g : ∀ r, r ≠ .a4 → s3.gpr r = s2.gpr r := u3.other
  refine ⟨h2.ctx.of_rest (u3.rest (ws := clobM) (by decide)) (by decide), hr,
    by rw [u3.mem, h2.mem]; exact Frame.refl _ _, by rw [g _ (by decide)]; exact h2.cy, Q, by simpa only [Nat.reduceMul] using hQ, ?_⟩
  rw [← hv]
  simp only [xv, colsV6, wv, X, Impl.Weierstrass.RISCV64.P384Field.XR, XC, gw, GW, upW, x5, Nat.reduceAdd,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceMul, List.getD_cons_zero,
    List.getD_cons_succ, g _ (show Reg.t5 ≠ .a4 by decide), g _ (show Reg.t6 ≠ .a4 by decide),
    g _ (show Reg.t3 ≠ .a4 by decide), g _ (show Reg.t4 ≠ .a4 by decide), g _ (show Reg.a1 ≠ .a4 by decide),
    g _ (show Reg.a2 ≠ .a4 by decide)]
  omega

/-! ## The sum's and the difference's words -/

theorem sumKs_getD {j : Nat} (hj : j < 6) :
    (sumKs m).getD j [] = li64 .t0 .a6 (wordOf (2 ^ 384 - m) j) := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  all_goals rfl

/-- The words of `2³⁸⁴ - m`, as a definition of its own, which unification
treats as a constant rather than evaluating `2³⁸⁴`. -/
def cw (m j : Nat) : Nat := wd (2 ^ 384 - m) j

theorem cw_lt (m j : Nat) : cw m j < 2 ^ 64 := by
  unfold cw
  exact wd_lt _ _

/-- The words of `2³⁸⁴ - m` into `t0`. -/
theorem sumK_ok : ∀ j < 6, KOk ((sumKs m).getD j []) j (cw m) := by
  intro j hj s _
  rw [sumKs_getD hj, ← List.append_nil (li64 .t0 .a6 _)]
  exact wp_li64 (by decide) _ fun s1 e1 k1 => WP.block_nil ⟨by rw [e1, wordOf_toNat, cw], k1⟩

theorem sumK_val (hm : Ok m) : colsV (cw m) 6 + m = 2 ^ 384 := by
  have := hm.pos
  have := hm.lt
  rw [colsV6]
  simp only [cw]
  rw [← words6 (show 2 ^ 384 - m < 2 ^ 384 by omega)]
  omega

theorem subKs_getD {j : Nat} (hj : j < 6) :
    (subKs m).getD j [] = li64 .a6 .a0 (wordOf m j) ++ ([.logic .and .a6 .a6 .t0] : List Instr) := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  all_goals rfl

/-- `m`'s words under the mask. -/
theorem subK_ok : ∀ j < 6, KMOk ((subKs m).getD j []) j (wd m) := by
  intro j hj s hmask
  rw [subKs_getD hj]
  have h := VG.Proof.Weierstrass.RISCV64.P384Order.kmW (wordOf m j) hmask
  rw [wordOf_toNat] at h
  exact h

theorem subK_val (hm : Ok m) : colsV (wd m) 6 = m := by
  rw [colsV6, ← words6 hm.lt]

/-! ## The operations -/

open VG.Proof.Weierstrass.RISCV64.P384Field (CoreOk mulWith_ok csubWith_ok addSum_ok subWith_ok WsAt clobC)
open VG.Proof.X448.RISCV64.R64 (al8)

/-- Montgomery's product modulo `m`. -/
abbrev mulRes (m A B r : Nat) : Prop := r < m ∧ r * 2 ^ 384 % m = A * B % m

theorem mulCore_core (hm : Ok m) :
    CoreOk (Impl.Weierstrass.RISCV64.Gen6.mulCore m) (fun _ B => B < m) (mulRes m) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB =>
    WP.mono (mulWith_ok (red := Impl.Weierstrass.RISCV64.Gen6.reduce m) (ks := sumKs m)
      (N := cw m) hm.pos (cw_lt m) sumK_ok (sumK_val hm) (fun hc => reduce_ok hm hc) hw h4 h5 h2 ha8 hb8 ho8 ha hb ho
      hdb hB) fun _ ⟨v1, v2, f, g, rd, wr, sp⟩ => ⟨⟨v1, v2⟩, f, g, rd, wr, sp⟩

theorem addCore_core (hm : Ok m) :
    CoreOk (.block (Impl.Weierstrass.RISCV64.Gen6.addCore m)) (fun A B => A + B < 2 * m)
      (fun A B r => r = (A + B) % m) := by
  intro W s a bb o hw h4 h5 h2 ha8 hb8 ho8 ha hb ho _ hab
  unfold Impl.Weierstrass.RISCV64.Gen6.addCore
  refine WP.block_append (WP.mono (addSum_ok hw h4 h5 ha8 hb8 ha hb) fun s1 ⟨v1, c1, r1, m1⟩ => ?_)
  have hw1 : WsAt W s1 := hw.of_rest r1 (by decide)
  refine WP.mono (csubWith_ok (N := cw m) (cw_lt m) sumK_ok (sumK_val hm) (O := W + BitVec.ofNat 64 o)
    (by rw [r1.gpr _ (by decide), h2]) (al8 hw.al ho8) (hw1.inW ho) c1 (by rw [v1]; exact hab))
    fun s2 ⟨v2, f2, g2, rd2, wr2, sp2⟩ => ?_
  refine ⟨by rw [v2, v1], by rw [← m1]; exact f2.mono (by simp), fun r hr => ?_, by rw [rd2, r1.rd],
    by rw [wr2, r1.wr], by rw [sp2, r1.sp]⟩
  have hC : r ∉ clobC := fun h => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h | h | h | h <;> simp [h])
  rw [g2 r hC, r1.gpr r hr]

theorem subCore_core (hm : Ok m) :
    CoreOk (.block (Impl.Weierstrass.RISCV64.Gen6.subCore m)) (fun A B => A < m ∧ B < m)
      (fun A B r => r = (A + m - B) % m) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho _ hAB =>
    WP.mono (subWith_ok (ks := subKs m) (PW := wd m) (wd_lt m) subK_ok (subK_val hm) hw h4 h5 h2 ha8 hb8 ho8 ha hb
      ho hAB.1 hAB.2) fun _ ⟨v, f, g, rd, wr, sp⟩ => ⟨v, f.mono (by simp), g, rd, wr, sp⟩

/-! ## The contracts -/

open VG.Impl.Weierstrass.RISCV64.P384Field (fn ptrs SA SB SO unpack pack)
open VG.Proof.Weierstrass.RISCV64.P384Field (numAt_d6 keeps_of_frame fn_ct read_zero satWs fn_ok d6)
open VG.Impl.Weierstrass.RISCV64.Gen6 (mulCore addCore subCore mulFn addFn subFn)
open VG.Impl.Weierstrass.Mont (numAt Keeps Modulus Fits)
open VG.Proof.Weierstrass.RISCV64 (offArg rvPre arg res rvPub mulRV addRV subRV)
open VG.Proof.Ed25519.RISCV64 (mulAgreeLo)

/-- What the taint analysis proves of an operation `core` (`fn_ct`): `fn core`
is constant time. -/
abbrev CtOk (core : Prog isa) : Prop :=
  RelCT isa (VG.RISCV64.Taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]))
    (.seq (.block ptrs) (.ite (.zero .t0) core
      (.seq (.block (([.addi .t1 .t2 0] : List Instr) ++ unpack .t4 SA 0 ++ unpack .t5 SB 0 ++
          ([.addi .t4 .a3 SA, .addi .t5 .a3 SB, .addi .t2 .a3 SO] : List Instr))) <|
        .seq core (.block (pack .t1 SO 0))))) fun _ _ => True

variable {S : Modulus}

/-- `fn core` meets a contract by register, from `fn_ok`. -/
theorem fn_rv (hk : S.k = 6) {core : Prog isa} {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop}
    (hcore : CoreOk core pre res) {s : State} (hs : rvPre S s) (hp : pre (arg S s .a2) (arg S s .a3)) :
    ∃ t s', Exec isa (fn core) s t s' ∧ abiPreserved s s' ∧
      res (arg S s .a2) (arg S s .a3) (numAt s'.mem (s.gpr .a0) (offArg s .a1) 6) ∧
      Keeps 6 (s.gpr .a0) (offArg s .a1) s.mem s'.mem := by
  obtain ⟨-, hwr, hfit, ⟨fo, fa, fb⟩, hal⟩ := hs
  simp only [Fits, hk, VG.Proof.Weierstrass.RISCV64.rvOwn_le (show 6 ≤ 6 by decide), Impl.Weierstrass.Mont.ownAt,
    Impl.Weierstrass.Mont.ownBytes] at fo fa fb
  simp only [arg, hk, numAt_d6] at hp ⊢
  obtain ⟨t, s', he, v, f, g, -, -, sp⟩ := fn_ok hcore rfl hal (by rw [hwr]; simp) hfit fo fa fb hp
  refine ⟨t, s', he, ⟨fun r hr => g r (by revert hr; revert r; decide), sp, g _ (by decide)⟩, v,
    keeps_of_frame fo f⟩

theorem mul_rv (hk : S.k = 6) (hm : Ok S.m) (s : State) (hs : (mulRV S).pre s) :
    ∃ t s', Exec isa (mulFn S.m) s t s' ∧ abiPreserved s s' ∧ (mulRV S).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fn_rv hk (@mulCore_core S.m hm) hs.1 (by exact hs.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v1,
    by simp only [res, Impl.Weierstrass.Mont.Modulus.R, hk, Nat.reduceMul]; exact v2, by rw [hk]; exact k⟩

theorem add_rv (hk : S.k = 6) (hm : Ok S.m) (s : State) (hs : (addRV S).pre s) :
    ∃ t s', Exec isa (addFn S.m) s t s' ∧ abiPreserved s s' ∧ (addRV S).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv hk (@addCore_core S.m hm) hs.1 (by exact hs.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

theorem sub_rv (hk : S.k = 6) (hm : Ok S.m) (s : State) (hs : (subRV S).pre s) :
    ∃ t s', Exec isa (subFn S.m) s t s' ∧ abiPreserved s s' ∧ (subRV S).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv hk (@subCore_core S.m hm) hs.1 (by exact hs.2)
  exact ⟨t, s', he, a, by rw [res, hk]; exact v, by rw [hk]; exact k⟩

/-! ## The shared contracts -/

theorem rvPub_agree' : ∀ s₁ s₂ : State, rvPre S s₁ → rvPre S s₂ → rvPub s₁ s₂ → mulAgreeLo s₁ s₂ :=
  fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, h0, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption⟩

theorem sat_pre (hk : S.k = 6) : rvPre S satWs ∧ arg S satWs .a2 = 0 ∧ arg S satWs .a3 = 0 := by
  refine ⟨⟨rfl, rfl, by decide, ⟨?_, ?_, ?_⟩, by decide⟩, read_zero _ _, read_zero _ _⟩ <;>
    simp [Fits, hk, VG.Proof.Weierstrass.RISCV64.rvOwn, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes,
      satWs, offArg]

theorem mul_verified (hk : S.k = 6) (hm : Ok S.m) (hct : CtOk (mulCore S.m)) :
    Verified RISCV64.target (mulFn S.m) (S.mulContract RISCV64.abi) := by
  obtain ⟨c, w, m, k, d⟩ := S
  cases hk
  exact Verified.of_correct (mul_rv rfl hm) (fn_ct (Pre := (mulRV ⟨c, w, m, 6, d⟩).pre)
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
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre (S := ⟨c, w, m, 6, d⟩) rfl
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; exact hm.pos⟩ }

theorem add_verified (hk : S.k = 6) (hm : Ok S.m) (hct : CtOk (.block (addCore S.m))) :
    Verified RISCV64.target (addFn S.m) (S.addContract RISCV64.abi) := by
  obtain ⟨c, w, m, k, d⟩ := S
  cases hk
  exact Verified.of_correct (add_rv rfl hm) (fn_ct (Pre := (addRV ⟨c, w, m, 6, d⟩).pre)
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
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre (S := ⟨c, w, m, 6, d⟩) rfl
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; have := hm.pos; dsimp only at this ⊢; omega⟩ }

theorem sub_verified (hk : S.k = 6) (hm : Ok S.m) (hct : CtOk (.block (subCore S.m))) :
    Verified RISCV64.target (subFn S.m) (S.subContract RISCV64.abi) := by
  obtain ⟨c, w, m, k, d⟩ := S
  cases hk
  exact Verified.of_correct (sub_rv rfl hm) (fn_ct (Pre := (subRV ⟨c, w, m, 6, d⟩).pre)
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
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre (S := ⟨c, w, m, 6, d⟩) rfl
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; exact ⟨hm.pos, hm.pos⟩⟩ }

end VG.Proof.Weierstrass.RISCV64.Gen6
