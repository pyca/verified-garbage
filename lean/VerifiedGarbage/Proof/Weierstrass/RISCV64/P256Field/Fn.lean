module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.X448.RISCV64.R64.Product
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X25519.RISCV64.R64.Mul
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed
import VerifiedGarbage.Proof.Ed25519.RISCV64.MulFn
public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT

/-!
# P-256's field on RISC-V: the functions

`fn core` (`Impl/Weierstrass/RISCV64/P256Field.lean`) from a state with the
working space at `W` in `a0` and the offsets' low words in `a1`–`a3`
(`fn_ok`): the entry (`entry_ok`) zero-extends the offsets and leaves the
pointers and, in `t0`, the low three bits of their `or`, zero only if the
offsets are multiples of 8 (`aligned_of`); then the operation on the
pointers, or on the byte-wise copies (`slowIn_ok`, `slowOut_ok`). Each
operation meets `CoreOk` (`mulCore_ok`, `addCore_ok`, `subCore_ok`).
-/

@[expose] public section

/-!
## P-256's field on RISC-V: the product

`mulCore` (`Impl/Weierstrass/RISCV64/P256Field.lean`) on pointers `t4`, `t5`
and `t2` (`mulCore_ok`): the operands copied to `MA` and `MB`
(`copyIn_ok`), their product (or the square of the first, if the pointers
are equal) at `ACC` by X25519's columns (`product_ok`, `square_ok`), whose
number is `prodV` (`accW_prodV`), reduced (`reduce_ok`) and stored at `[t2]`
(`csub_ok`): Montgomery's product modulo `p`.
-/

/-!
## P-256's field on RISC-V: Montgomery's reduction

`reduce` (`Impl/Weierstrass/RISCV64/P256Field.lean`) reduces the eight words
`T` at `ACC`: after round `i`, the registers `rw i`–`rw (i + 3)`, the carry
`a2` and the words of `T` from `i + 4` on, as a number `wv i` (`RedInv`), are
`(T + Q p) / 2^(64 i)` for some `Q < 2^(64 i)` (`round_ok`: a round adds
`q p` for the low word `q`, which `p ≡ -1 (mod 2⁶⁴)` makes the next quotient
word), so the four rounds leave `X` with `X 2²⁵⁶ = T + Q p` (`reduce_ok`).
-/

namespace VG.Proof.Weierstrass.RISCV64.P256Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Proof.X25519.RISCV64 (Ctx Rest)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok clob64 Keeps.rest)

/-- Word `j` of the product at `ACC`. -/
abbrev T (m : Mem) (b : Addr) (j : Nat) : Nat := dw m b (ACC + 8 * j)

/-- The `n` words of the product from word `j`. -/
def upW (m : Mem) (b : Addr) (j : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => T m b j + 2 ^ 64 * upW m b (j + 1) n

/-- The product's eight words. -/
abbrev prodV (m : Mem) (b : Addr) : Nat := upW m b 0 8

/-- The number after round `i - 1`: the registers, the carry and the words of
the product not yet loaded. -/
def wv (m : Mem) (b : Addr) (i : Nat) (s : State) : Nat :=
  (s.gpr (rw i)).toNat + 2 ^ 64 * (s.gpr (rw (i + 1))).toNat + 2 ^ 128 * (s.gpr (rw (i + 2))).toNat +
    2 ^ 192 * (s.gpr (rw (i + 3))).toNat + 2 ^ 256 * ((s.gpr .a2).toNat + upW m b (i + 4) (4 - i))

/-- After `i` rounds, from `s0`. -/
structure RedInv (b : Addr) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob64 s0 s
  mem : s.mem = s0.mem
  cy : (s.gpr .a2).toNat ≤ 1
  val : ∃ Q, Q < 2 ^ (64 * i) ∧ wv s0.mem b i s * 2 ^ (64 * i) = prodV s0.mem b + Q * P

/-- The registers of a round. -/
theorem rw_facts : ∀ i < 4,
    rw i ≠ rw (i + 1) ∧ rw i ≠ rw (i + 2) ∧ rw i ≠ rw (i + 3) ∧ rw i ≠ rw (i + 4) ∧
    rw (i + 1) ≠ rw (i + 2) ∧ rw (i + 1) ≠ rw (i + 3) ∧ rw (i + 1) ≠ rw (i + 4) ∧
    rw (i + 2) ≠ rw (i + 3) ∧ rw (i + 2) ≠ rw (i + 4) ∧ rw (i + 3) ≠ rw (i + 4) ∧
    (∀ k < 5, rw (i + k) ≠ .a2 ∧ rw (i + k) ≠ .a4 ∧ rw (i + k) ≠ .a5 ∧ rw (i + k) ≠ .a6 ∧
      rw (i + k) ≠ .a7 ∧ rw (i + k) ≠ .t0 ∧ rw (i + k) ≠ .a3 ∧ rw (i + k) ∈ clob64) := by
  intro i hi
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals decide

theorem rw_add5 (i : Nat) : rw (i + 5) = rw i := by
  simp only [rw, Nat.add_mod_right]

theorem mem2 {r : Reg} (h : r ∈ clob64) : ∀ x ∈ [r, .t0], x ∈ clob64 := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact h
  · decide

theorem mem3 {r r₁ r₂ : Reg} (h : r ∈ clob64) (h₁ : r₁ ∈ clob64 := by decide) (h₂ : r₂ ∈ clob64 := by decide) :
    ∀ x ∈ [r, r₁, r₂], x ∈ clob64 := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact h
  · exact h₁
  · exact h₂

/-- Round `i`. -/
theorem round_ok {b : Addr} {s0 : State} {i : Nat} (hi : i < 4) {s : State} (h : RedInv b s0 i s) :
    WP isa (.block (round i)) s (RedInv b s0 (i + 1)) := by
  obtain ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34, dk⟩ := rw_facts i hi
  obtain ⟨n02, n04, n05, n06, n07, n0t, n03, c0⟩ := dk 0 (by decide)
  obtain ⟨n12, n14, n15, n16, n17, n1t, n13, c1⟩ := dk 1 (by decide)
  obtain ⟨n22, n24, n25, n26, n27, n2t, n23, c2⟩ := dk 2 (by decide)
  obtain ⟨n32, n34, n35, n36, n37, n3t, n33, c3⟩ := dk 3 (by decide)
  obtain ⟨n42, n44, n45, n46, n47, n4t, n43, c4⟩ := dk 4 (by decide)
  simp only [Nat.add_zero] at n02 n04 n05 n06 n07 n0t n03 c0
  have hc := h.ctx
  have hd : ACC + 8 * (i + 4) + 8 ≤ 2048 := by simp only [ACC]; omega
  unfold round
  refine ld_ok hc hd (by simp only [ACC]; omega) fun s1 u1 => ?_
  have hT4 : (s1.gpr (rw (i + 4))).toNat = T s0.mem b (i + 4) := by
    rw [u1.gpr, ← h.mem]; rfl
  show WP isa (.block (quot i ++ _)) s1 _
  refine WP.block_append (WP.mono (quot_ok (r := rw i) n04 n05 n06 n07) fun s2 ⟨q1, q2, q5, q7, k2⟩ => ?_)
  refine WP.block_append (WP.mono (add1_ok (d := rw (i + 1)) (y := .a4) (c := .t0) n14 n1t)
    fun s3 ⟨e3, k3⟩ => ?_)
  refine WP.block_append (WP.mono (add3s_ok (d := rw (i + 2)) (y := .a5) (c := .t0) n25 n2t)
    fun s4 ⟨e4, k4⟩ => ?_)
  refine WP.block_append (WP.mono (adc_ok (d := rw (i + 3)) (x := rw (i + 3)) (y := .a6) (c := .t0) (u := .a4)
    n36 n3t (Ne.symm n34) (by decide)) fun s5 ⟨e5, k5⟩ => ?_)
  refine WP.mono (addTop_ok (d := rw (i + 4)) (h := .a7) (c := .t0) (k := .a2) n47 n42 (by decide))
    fun s6 ⟨e6, k6⟩ => ?_
  have g1 : ∀ r, r ≠ rw (i + 4) → s1.gpr r = s.gpr r := u1.other
  -- Registers read by each step, through the steps before it.
  have r0 : s2.gpr (rw i) = s.gpr (rw i) := by rw [k2.1 _ (by simp [n04, n05, n06, n07, n0t]), g1 _ d04]
  have r0' : s1.gpr (rw i) = s.gpr (rw i) := g1 _ d04
  have r1 : s2.gpr (rw (i + 1)) = s.gpr (rw (i + 1)) := by
    rw [k2.1 _ (by simp [n14, n15, n16, n17, n1t]), g1 _ d14]
  have r2 : s3.gpr (rw (i + 2)) = s.gpr (rw (i + 2)) := by
    rw [k3.1 _ (by simp [Ne.symm d12, n2t]), k2.1 _ (by simp [n24, n25, n26, n27, n2t]), g1 _ d24]
  have r3 : s4.gpr (rw (i + 3)) = s.gpr (rw (i + 3)) := by
    rw [k4.1 _ (by simp [Ne.symm d23, n35, n3t]), k3.1 _ (by simp [Ne.symm d13, n3t]),
      k2.1 _ (by simp [n34, n35, n36, n37, n3t]), g1 _ d34]
  have r4 : s5.gpr (rw (i + 4)) = s1.gpr (rw (i + 4)) := by
    rw [k5.1 _ (by simp [Ne.symm d34, n44, n4t]), k4.1 _ (by simp [Ne.symm d24, n45, n4t]),
      k3.1 _ (by simp [Ne.symm d14, n4t]), k2.1 _ (by simp [n44, n45, n46, n47, n4t])]
  have ra2 : s5.gpr .a2 = s.gpr .a2 := by
    rw [k5.1 _ (by simp [Ne.symm n32]), k4.1 _ (by simp [Ne.symm n22]), k3.1 _ (by simp [Ne.symm n12]),
      k2.1 _ (by decide), g1 _ (Ne.symm n42)]
  have a5' : s3.gpr .a5 = s2.gpr .a5 := k3.1 _ (by simp [Ne.symm n15])
  have a6' : s4.gpr .a6 = s2.gpr .a6 := by
    rw [k4.1 _ (by simp [Ne.symm n26]), k3.1 _ (by simp [Ne.symm n16])]
  have a7' : s5.gpr .a7 = s2.gpr .a7 := by
    rw [k5.1 _ (by simp [Ne.symm n37]), k4.1 _ (by simp [Ne.symm n27]), k3.1 _ (by simp [Ne.symm n17])]
  -- The new registers, read from the last state.
  have o1 : s6.gpr (rw (i + 1)) = s3.gpr (rw (i + 1)) := by
    rw [k6.1 _ (by simp [d14, n17, n12]), k5.1 _ (by simp [d13, n14, n1t]), k4.1 _ (by simp [d12, n15, n1t])]
  have o2 : s6.gpr (rw (i + 2)) = s4.gpr (rw (i + 2)) := by
    rw [k6.1 _ (by simp [d24, n27, n22]), k5.1 _ (by simp [d23, n24, n2t])]
  have o3 : s6.gpr (rw (i + 3)) = s5.gpr (rw (i + 3)) := by
    rw [k6.1 _ (by simp [d34, n37, n32])]
  rw [r0'] at q1 q2
  rw [r1] at e3
  rw [a5', r2] at e4
  rw [r3, a6'] at e5
  rw [r4, hT4, a7', ra2] at e6
  have hcy := h.cy
  have bA4 := (s2.gpr .a4).isLt
  have bw1 := (s.gpr (rw (i + 1))).isLt
  have bw2 := (s.gpr (rw (i + 2))).isLt
  have bw3 := (s.gpr (rw (i + 3))).isLt
  have bT := dw_lt s0.mem b (ACC + 8 * (i + 4))
  have b1 := (s3.gpr (rw (i + 1))).isLt
  have b2 := (s4.gpr (rw (i + 2))).isLt
  have b3 := (s5.gpr (rw (i + 3))).isLt
  have b4 := (s6.gpr (rw (i + 4))).isLt
  have bA6 := (s2.gpr .a6).isLt
  have hk1 : (s3.gpr .t0).toNat ≤ 1 := by omega
  have e4' := e4 (by omega)
  have hk2 : (s4.gpr .t0).toNat ≤ 1 := by omega
  have e5' := e5 hk2
  have hk3 : (s5.gpr .t0).toNat ≤ 1 := by omega
  have e6' := e6 (by omega)
  have hrest : Rest clob64 s s6 :=
    (u1.rest c4).trans ((Keeps.rest k2).mono (by decide) |>.trans ((Keeps.rest k3).mono (mem2 c1) |>.trans
      ((Keeps.rest k4).mono (mem3 c2) |>.trans ((Keeps.rest k5).mono (mem3 c3) |>.trans
      ((Keeps.rest k6).mono (mem3 c4))))))
  have hm : s6.mem = s0.mem := by rw [k6.2.1, k5.2.1, k4.2.1, k3.2.1, k2.2.1, u1.mem, h.mem]
  have hup : upW s0.mem b (i + 4) (4 - i) = T s0.mem b (i + 4) + 2 ^ 64 * upW s0.mem b (i + 5) (3 - i) := by
    rw [show 4 - i = (3 - i) + 1 by omega]; rfl
  obtain ⟨Q, hQ, hv⟩ := h.val
  have key : 2 ^ 64 * wv s0.mem b (i + 1) s6 = wv s0.mem b i s + (s.gpr (rw i)).toNat * P := by
    simp only [wv, show i + 1 + 1 = i + 2 by omega, show i + 1 + 2 = i + 3 by omega,
      show i + 1 + 3 = i + 4 by omega, show i + 1 + 4 = i + 5 by omega, show 4 - (i + 1) = 3 - i by omega,
      hup, o1, o2, o3]
    simp only [P]
    omega
  refine ⟨hc.of_rest hrest (by decide), h.rest.trans hrest, hm, by omega,
    ⟨Q + (s.gpr (rw i)).toNat * 2 ^ (64 * i), ?_, ?_⟩⟩
  · have hq := (s.gpr (rw i)).isLt
    rw [show 64 * (i + 1) = 64 * i + 64 by omega, Nat.pow_add]
    generalize 2 ^ (64 * i) = E at *
    generalize (s.gpr (rw i)).toNat = q at *
    have : (q + 1) * E ≤ 2 ^ 64 * E := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    rw [Nat.mul_comm E]
    omega
  · rw [show 64 * (i + 1) = 64 * i + 64 by omega, Nat.pow_add]
    generalize 2 ^ (64 * i) = E at *
    generalize wv s0.mem b (i + 1) s6 = W' at *
    generalize wv s0.mem b i s = W at *
    generalize (s.gpr (rw i)).toNat = q at *
    generalize prodV s0.mem b = Pr at *
    have : W' * (E * 2 ^ 64) = (2 ^ 64 * W') * E := by
      rw [Nat.mul_comm E, ← Nat.mul_assoc, Nat.mul_comm W']
    rw [this, key, Nat.add_mul, hv]
    grind

/-- The rounds, by induction. -/
theorem rounds_ok {b : Addr} {s0 : State} : ∀ n ≤ 4, ∀ s, RedInv b s0 0 s →
    WP isa (.block ((List.range n).flatMap round)) s (RedInv b s0 n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (rounds_ok n (by omega) s h) fun s1 h1 => round_ok (by omega) h1)

/-- The initial loads. -/
theorem loads_ok {b : Addr} {s : State} (hc : Ctx b s) :
    WP isa (.block ((List.range 4).map (fun j => .load .d (rw j) .a3 (ACC + 8 * j)) ++ ([.li .a2 0] : List Instr))) s
      (RedInv b s 0) := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  refine ld_ok hc (by unfold ACC; omega) (by unfold ACC; omega) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := clob64) (by decide)) (by decide)
  refine ld_ok hc1 (by unfold ACC; omega) (by unfold ACC; omega) fun s2 u2 => ?_
  have hc2 : Ctx b s2 := hc1.of_rest (u2.rest (ws := clob64) (by decide)) (by decide)
  refine ld_ok hc2 (by unfold ACC; omega) (by unfold ACC; omega) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := hc2.of_rest (u3.rest (ws := clob64) (by decide)) (by decide)
  refine ld_ok hc3 (by unfold ACC; omega) (by unfold ACC; omega) fun s4 u4 => ?_
  have hc4 : Ctx b s4 := hc3.of_rest (u4.rest (ws := clob64) (by decide)) (by decide)
  refine wp_li (by decide) fun s5 u5 => WP.block_nil ?_
  have hr : Rest clob64 s s5 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  have hm : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have w0 : (s5.gpr (rw 0)).toNat = T s.mem b 0 := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.gpr]; rfl
  have w1 : (s5.gpr (rw 1)).toNat = T s.mem b 1 := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.mem]; rfl
  have w2 : (s5.gpr (rw 2)).toNat = T s.mem b 2 := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.mem, u1.mem]; rfl
  have w3 : (s5.gpr (rw 3)).toNat = T s.mem b 3 := by
    rw [u5.other _ (by decide), u4.gpr, u3.mem, u2.mem, u1.mem]; rfl
  have wc : (s5.gpr .a2).toNat = 0 := by rw [u5.gpr]; rfl
  refine ⟨hc4.of_rest (u5.rest (ws := clob64) (by decide)) (by decide), hr, hm, by rw [wc]; omega,
    ⟨0, by decide, ?_⟩⟩
  simp only [wv, Nat.zero_add, w0, w1, w2, w3, wc, Nat.mul_zero, Nat.pow_zero, Nat.mul_one,
    Nat.sub_zero, prodV, upW, Nat.reduceAdd]
  omega

/-- `reduce`: `X + 2²⁵⁶ c` (`X0`–`X3` and `XC`), with `(X + 2²⁵⁶ c) 2²⁵⁶ = T + Q p` for some
`Q < 2²⁵⁶`, below `2p` if the product is below `2²⁵⁶ p`. -/
theorem reduce_ok {b : Addr} {s : State} (hc : Ctx b s) :
    WP isa (.block reduce) s fun s' =>
      Ctx b s' ∧ Rest clob64 s s' ∧ s'.mem = s.mem ∧ (s'.gpr XC).toNat ≤ 1 ∧
      ∃ Q, Q < 2 ^ 256 ∧
        ((s'.gpr X0).toNat + 2 ^ 64 * (s'.gpr X1).toNat + 2 ^ 128 * (s'.gpr X2).toNat +
          2 ^ 192 * (s'.gpr X3).toNat + 2 ^ 256 * (s'.gpr XC).toNat) * 2 ^ 256 = prodV s.mem b + Q * P := by
  unfold reduce
  refine WP.block_append (WP.mono (loads_ok hc) fun s1 h1 => WP.mono (rounds_ok 4 (Nat.le_refl _) s1 h1)
    fun s2 h2 => ?_)
  obtain ⟨Q, hQ, hv⟩ := h2.val
  refine ⟨h2.ctx, h2.rest, h2.mem, h2.cy, Q, by simpa using hQ, ?_⟩
  simpa [wv, upW, X0, X1, X2, X3, XC, rw, RW] using hv

end VG.Proof.Weierstrass.RISCV64.P256Field

/-!
## P-256's field on RISC-V: the final subtraction

`csub` (`Impl/Weierstrass/RISCV64/P256Field.lean`) stores `x mod p` at
`[t2]` for the number `x = X0 + … + 2¹⁹² X3 + 2²⁵⁶ XC` below `2p`
(`csub_ok`): `x + (2²⁵⁶ - p)` with carries (`sumN_ok`), whose carry out of 256
bits or `XC` is `x ≥ p`, then its low words or `x`'s by that mask
(`sel_ok`).
-/

namespace VG.Proof.Weierstrass.RISCV64.P256Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt dw_write_self dw_write_other al8)

/-- The registers `csub` writes. -/
abbrev clobC : List Reg := [.t0, .t6, .a0, .a4, .a5, .a6, .a7]

/-- The number of the words `x₀`–`x₃` of registers. -/
abbrev v4 (s : State) (r₀ r₁ r₂ r₃ : Reg) : Nat :=
  (s.gpr r₀).toNat + 2 ^ 64 * (s.gpr r₁).toNat + 2 ^ 128 * (s.gpr r₂).toNat + 2 ^ 192 * (s.gpr r₃).toNat

/-- The four doublewords at `O`. -/
abbrev d4 (m : Mem) (O : Addr) : Nat := dw m O 0 + 2 ^ 64 * dw m O 8 + 2 ^ 128 * dw m O 16 + 2 ^ 192 * dw m O 24

set_option linter.unusedSimpArgs false in
/-- `x + (2²⁵⁶ - p)` into `t6`, `a4`–`a6`, its carry into `a7`. -/
theorem sumN_ok {s : State} :
    WP isa (.block sumP) s fun s' =>
      v4 s' .t6 .a4 .a5 .a6 + 2 ^ 256 * (s'.gpr .a7).toNat = v4 s X0 X1 X2 X3 + (2 ^ 256 - P) ∧
      (s'.gpr .a7).toNat ≤ 1 ∧ Keeps clobC s s' := by
  simp only [sumP, List.append_assoc, List.cons_append, List.nil_append, csubWord]
  refine wp_addi (imm := 1) (by decide) fun sa ua => wp_sltu fun sb ub => wp_lim1 fun sc uc =>
    wp_sll (by decide) fun sd ud => ?_
  refine WP.block_append (WP.mono (adc_ok (d := .a4) (x := X1) (y := .t0) (c := .a7) (u := .a0))
    fun s1 ⟨e1, k1⟩ => ?_)
  refine wp_lim1 fun se ue => ?_
  refine WP.block_append (WP.mono (adc_ok (d := .a5) (x := X2) (y := .t0) (c := .a7) (u := .a0))
    fun s2 ⟨e2, k2⟩ => ?_)
  refine wp_lim1 fun sf uf => wp_srl (by decide) fun sg ug => wp_subi (imm := 1) (by decide) fun sh uh => ?_
  refine WP.mono (adc_ok (d := .a6) (x := X3) (y := .t0) (c := .a7) (u := .a0)) fun s3 ⟨e3, k3⟩ => ?_
  -- The carry out of `x₀ + 1`.
  have c0 : (sb.gpr .t6).toNat + 2 ^ 64 * (sb.gpr .a7).toNat = (s.gpr X0).toNat + 1 := by
    rw [ub.other _ (by decide), ub.gpr, ua.gpr, ua.other _ (by decide)]
    have := carry (BitVec.ofNat 64 1) (s.gpr X0)
    rw [BitVec.add_comm (BitVec.ofNat 64 1)] at this
    simp only [BitVec.toNat_ofNat] at this ⊢
    omega
  have hn1 : (sd.gpr .t0).toNat = 2 ^ 64 - 2 ^ 32 := by rw [ud.gpr, uc.gpr]; decide
  have hn2 : (se.gpr .t0).toNat = 2 ^ 64 - 1 := by rw [ue.gpr]; decide
  have hn3 : (sh.gpr .t0).toNat = 2 ^ 32 - 2 := by rw [uh.gpr, ug.gpr, uf.gpr]; decide
  have a7d : (sd.gpr .a7) = sb.gpr .a7 := by rw [ud.other _ (by decide), uc.other _ (by decide)]
  have x1d : sd.gpr X1 = s.gpr X1 := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide)]
  have hc0 : (sb.gpr .a7).toNat ≤ 1 := by
    rw [ub.gpr]; exact sltu_le _
  have e1' := e1 (by rw [a7d]; exact hc0)
  rw [a7d, x1d, hn1] at e1'
  have b1 := (s1.gpr .a4).isLt
  have hc1 : (se.gpr .a7).toNat ≤ 1 := by rw [ue.other _ (by decide)]; omega
  have e2' := e2 hc1
  rw [hn2, ue.other _ (by decide), k1.1 _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
    ub.other _ (by decide), ua.other _ (by decide), ue.other .a7 (by decide)] at e2'
  have b2 := (s2.gpr .a5).isLt
  have hc2 : (sh.gpr .a7).toNat ≤ 1 := by
    rw [uh.other _ (by decide), ug.other _ (by decide), uf.other _ (by decide)]; omega
  have e3' := e3 hc2
  rw [hn3, uh.other X3 (by decide), ug.other X3 (by decide), uf.other X3 (by decide), k2.1 X3 (by decide),
    ue.other X3 (by decide), k1.1 X3 (by decide), ud.other X3 (by decide), uc.other X3 (by decide),
    ub.other X3 (by decide), ua.other X3 (by decide), uh.other .a7 (by decide), ug.other .a7 (by decide),
    uf.other .a7 (by decide)] at e3'
  have b3 := (s3.gpr .a6).isLt
  -- The registers at the end.
  have f6 : s3.gpr .t6 = sb.gpr .t6 := by
    rw [k3.1 _ (by decide), uh.other _ (by decide), ug.other _ (by decide), uf.other _ (by decide),
      k2.1 _ (by decide), ue.other _ (by decide), k1.1 _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide)]
  have f4 : s3.gpr .a4 = s1.gpr .a4 := by
    rw [k3.1 _ (by decide), uh.other _ (by decide), ug.other _ (by decide), uf.other _ (by decide),
      k2.1 _ (by decide), ue.other _ (by decide)]
  have f5 : s3.gpr .a5 = s2.gpr .a5 := by
    rw [k3.1 _ (by decide), uh.other _ (by decide), ug.other _ (by decide), uf.other _ (by decide)]
  have x2 : (se.gpr X2) = s.gpr X2 := by
    rw [ue.other _ (by decide), k1.1 _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide)]
  refine ⟨?_, by omega, ?_⟩
  · simp only [v4, f6, f4, f5, P]
    have := (s.gpr X0).isLt
    omega
  · exact ((((((((((upd_keeps ua).trans (upd_keeps ub)).trans (upd_keeps uc)).trans (upd_keeps ud)).trans
      k1).trans (upd_keeps ue)).trans k2).trans (upd_keeps uf)).trans (upd_keeps ug)).trans
      (upd_keeps uh) |>.trans k3).mono (by decide)

/-- A mask, zero or all ones. -/
def IsMask (m : BitVec 64) : Prop := m = 0 ∨ m = BitVec.allOnes 64

/-- `x ⊕ ((e ⊕ x) ∧ m)`: `e` under the mask all ones, `x` under zero. -/
theorem sel_mask {x e m : BitVec 64} (hm : IsMask m) :
    (e ^^^ x) &&& m ^^^ x = if m = BitVec.allOnes 64 then e else x := by
  rcases hm with rfl | rfl
  · have : (0 : BitVec 64) ≠ BitVec.allOnes 64 := by decide
    simp only [this, ↓reduceIte]
    ext i hi
    simp
  · simp only [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, ↓reduceIte]

/-- The region of `o`'s four doublewords. -/
theorem out_contains (O : Addr) {j : Nat} (hj : j < 4) :
    (⟨O, 32⟩ : Region).Contains (O + BitVec.ofNat 64 (8 * j)) 8 := by
  have := Offset.contains O (d := 8 * j) (n := 8) (e := 0) (k := 32) (by omega) (by omega) (by omega)
  simpa using this

set_option linter.unusedSimpArgs false in
/-- `selWord x e j`: `[O + 8j] =` `e` under the mask `t0` all ones, else `x`. -/
theorem selWord_ok {s : State} {O : Addr} {x e : Reg} {j : Nat} (hj : j < 4) (ht2 : s.gpr .t2 = O)
    (hal : O.toNat % 8 = 0) (hw : InRegions s.wr (O + BitVec.ofNat 64 (8 * j)) 8) (hm : IsMask (s.gpr .t0))
    (hex : e ≠ x := by decide) (he0 : e ≠ .t0 := by decide) (he2 : e ≠ .t2 := by decide) :
    WP isa (.block (selWord x e j)) s fun s' =>
      s'.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j))
        (if s.gpr .t0 = BitVec.allOnes 64 then s.gpr e else s.gpr x) ∧
      (∀ r, r ≠ e → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold selWord
  refine wp_xor fun s1 u1 => VG.Proof.X25519.RISCV64.wp_and fun s2 u2 => wp_xor fun s3 u3 => ?_
  have h3 : s3.gpr e = if s.gpr .t0 = BitVec.allOnes 64 then s.gpr e else s.gpr x := by
    rw [u3.gpr, u2.gpr, u1.gpr, u2.other _ hex.symm, u1.other _ hex.symm, u1.other _ he0.symm]
    exact sel_mask hm
  have g3 : ∀ r, r ≠ e → s3.gpr r = s.gpr r := fun r hr => by rw [u3.other _ hr, u2.other _ hr, u1.other _ hr]
  refine wp_sd (by omega) (by rw [g3 _ (Ne.symm he2), ht2]) (al8 hal (by omega))
    (by rw [u3.wr, u2.wr, u1.wr]; exact hw) fun s4 u4 => WP.block_nil ?_
  refine ⟨by rw [u4.mem, h3, u3.mem, u2.mem, u1.mem], fun r hr => by rw [u4.gpr, g3 _ hr], ?_, ?_, ?_⟩
  · rw [u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u4.wr, u3.wr, u2.wr, u1.wr]
  · rw [u4.sp, u3.sp, u2.sp, u1.sp]

/-- The mask of `a ∨ c`, for bits `a` and `c`. -/
theorem mask_of_bits {a c : BitVec 64} (ha : a.toNat ≤ 1) (hc : c.toNat ≤ 1) :
    IsMask (0 - (a ||| c)) ∧ (0 - (a ||| c) = BitVec.allOnes 64 ↔ a.toNat = 1 ∨ c.toNat = 1) := by
  have ha' : a = 0 ∨ a = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with h | h
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  have hc' : c = 0 ∨ c = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  rcases ha' with rfl | rfl <;> rcases hc' with rfl | rfl <;> (unfold IsMask; decide)

/-- `sum ++ csubTail`: `x mod m` at `[t2]`, for `x = X0 + … + 2¹⁹² X3 + 2²⁵⁶ XC`
below `2m`, after a `sum` that leaves `x + (2²⁵⁶ - m)` in `t6`, `a4`–`a6` and its
carry in `a7`. -/
theorem csubWith_ok {sum : List Instr} {M : Nat} (hM : M ≤ 2 ^ 256) {s : State}
    (hsum : WP isa (.block sum) s fun s' =>
      v4 s' .t6 .a4 .a5 .a6 + 2 ^ 256 * (s'.gpr .a7).toNat = v4 s X0 X1 X2 X3 + (2 ^ 256 - M) ∧
      (s'.gpr .a7).toNat ≤ 1 ∧ Keeps clobC s s')
    {O : Addr} (ht2 : s.gpr .t2 = O) (hal : O.toNat % 8 = 0)
    (hw : ∀ j < 4, InRegions s.wr (O + BitVec.ofNat 64 (8 * j)) 8) (hc : (s.gpr XC).toNat ≤ 1)
    (hx : v4 s X0 X1 X2 X3 + 2 ^ 256 * (s.gpr XC).toNat < 2 * M) :
    WP isa (.block (sum ++ csubTail)) s fun s' =>
      d4 s'.mem O = (v4 s X0 X1 X2 X3 + 2 ^ 256 * (s.gpr XC).toNat) % M ∧
      Frame [⟨O, 32⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobC → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e : sum ++ csubTail = sum ++
      ([.logic .or .a7 .a7 XC, .li .t0 0, .sub .t0 .t0 .a7] ++
      (selWord X0 .t6 0 ++ (selWord X1 .a4 1 ++ (selWord X2 .a5 2 ++ selWord X3 .a6 3)))) := by
    simp only [csubTail, List.append_assoc]
  rw [e]
  refine WP.block_append (WP.mono hsum fun s1 ⟨v1, c1, k1⟩ => ?_)
  refine wp_or fun s2 u2 => wp_li (imm := 0) (by decide) fun s3 u3 => wp_sub fun s4 u4 => ?_
  have hm : IsMask (s4.gpr .t0) ∧ (s4.gpr .t0 = BitVec.allOnes 64 ↔
      (s1.gpr .a7).toNat = 1 ∨ (s.gpr XC).toNat = 1) := by
    rw [u4.gpr, u3.gpr, u3.other _ (by decide), u2.gpr, k1.1 XC (by decide)]
    exact mask_of_bits c1 hc
  have g4 : ∀ r, r ≠ .t0 → r ≠ .a7 → s4.gpr r = s1.gpr r := fun r h0 h7 => by
    rw [u4.other _ h0, u3.other _ h0, u2.other _ h7]
  have m4 : s4.mem = s1.mem := by rw [u4.mem, u3.mem, u2.mem]
  have w4 : s4.wr = s.wr := by rw [u4.wr, u3.wr, u2.wr, k1.2.2.2.1]
  have p4 : s4.gpr .t2 = O := by rw [g4 _ (by decide) (by decide), k1.1 _ (by decide), ht2]
  show WP isa (.block (selWord X0 .t6 0 ++ _)) s4 _
  refine WP.block_append (WP.mono (selWord_ok (x := X0) (e := .t6) (j := 0) (by decide) p4 hal
    (by rw [w4]; exact hw 0 (by decide)) hm.1) fun s5 ⟨m5, g5, r5, w5, sp5⟩ => ?_)
  have t5 : s5.gpr .t0 = s4.gpr .t0 := g5 _ (by decide)
  refine WP.block_append (WP.mono (selWord_ok (x := X1) (e := .a4) (j := 1) (by decide)
    (by rw [g5 _ (by decide), p4]) hal (by rw [w5, w4]; exact hw 1 (by decide)) (by rw [t5]; exact hm.1))
    fun s6 ⟨m6, g6, r6, w6, sp6⟩ => ?_)
  have t6 : s6.gpr .t0 = s4.gpr .t0 := by rw [g6 _ (by decide), t5]
  refine WP.block_append (WP.mono (selWord_ok (x := X2) (e := .a5) (j := 2) (by decide)
    (by rw [g6 _ (by decide), g5 _ (by decide), p4]) hal (by rw [w6, w5, w4]; exact hw 2 (by decide))
    (by rw [t6]; exact hm.1)) fun s7 ⟨m7, g7, r7, w7, sp7⟩ => ?_)
  have t7 : s7.gpr .t0 = s4.gpr .t0 := by rw [g7 _ (by decide), t6]
  refine WP.mono (selWord_ok (x := X3) (e := .a6) (j := 3) (by decide)
    (by rw [g7 _ (by decide), g6 _ (by decide), g5 _ (by decide), p4]) hal
    (by rw [w7, w6, w5, w4]; exact hw 3 (by decide)) (by rw [t7]; exact hm.1))
    fun s8 ⟨m8, g8, r8, w8, sp8⟩ => ?_
  -- The registers, from `s1` and `s`.
  have rt4 : ∀ r, r ∉ clobC → s4.gpr r = s.gpr r := fun r hr => by
    rw [g4 _ (fun h => hr (by simp [h])) (fun h => hr (by simp [h])), k1.1 r hr]
  have rt5 : ∀ r, r ∉ clobC → s5.gpr r = s.gpr r := fun r hr => by
    rw [g5 _ (fun h => hr (by simp [h])), rt4 r hr]
  have rt6 : ∀ r, r ∉ clobC → s6.gpr r = s.gpr r := fun r hr => by
    rw [g6 _ (fun h => hr (by simp [h])), rt5 r hr]
  have rt7 : ∀ r, r ∉ clobC → s7.gpr r = s.gpr r := fun r hr => by
    rw [g7 _ (fun h => hr (by simp [h])), rt6 r hr]
  have rt8 : ∀ r, r ∉ clobC → s8.gpr r = s.gpr r := fun r hr => by
    rw [g8 _ (fun h => hr (by simp [h])), rt7 r hr]
  have d0 : s4.gpr .t6 = s1.gpr .t6 := g4 _ (by decide) (by decide)
  have d1 : s5.gpr .a4 = s1.gpr .a4 := by rw [g5 _ (by decide), g4 _ (by decide) (by decide)]
  have d2 : s6.gpr .a5 = s1.gpr .a5 := by
    rw [g6 _ (by decide), g5 _ (by decide), g4 _ (by decide) (by decide)]
  have d3 : s7.gpr .a6 = s1.gpr .a6 := by
    rw [g7 _ (by decide), g6 _ (by decide), g5 _ (by decide), g4 _ (by decide) (by decide)]
  rw [t5] at m6
  rw [t6] at m7
  rw [t7] at m8
  rw [d0, rt4 X0 (by decide)] at m5
  rw [d1, rt5 X1 (by decide)] at m6
  rw [d2, rt6 X2 (by decide)] at m7
  rw [d3, rt7 X3 (by decide)] at m8
  rw [m7, m6, m5, m4] at m8
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at m8
  have hm1 : s1.mem = s.mem := k1.2.1
  refine ⟨?_, ?_, rt8, ?_, ?_, ?_⟩
  · rw [m8, d4, dw_write_other _ _ _ (by omega) (by omega) (by omega),
      dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_other _ _ _ (by omega) (by omega) (by omega),
      show O + BitVec.ofNat 64 0 = O + BitVec.ofNat 64 0 from rfl, dw_write_self,
      dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_other _ _ _ (by omega) (by omega) (by omega),
      dw_write_self, dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_self, dw_write_self]
    have hge := hm.2
    simp only [v4] at v1 hx ⊢
    have := (s.gpr X0).isLt; have := (s.gpr X1).isLt; have := (s.gpr X2).isLt; have := (s.gpr X3).isLt
    have := (s1.gpr .t6).isLt; have := (s1.gpr .a4).isLt; have := (s1.gpr .a5).isLt; have := (s1.gpr .a6).isLt
    by_cases h : s4.gpr .t0 = BitVec.allOnes 64
    · simp only [h, ↓reduceIte]
      have hg := hge.mp h
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [h, ↓reduceIte]
      have hg : ¬ ((s1.gpr .a7).toNat = 1 ∨ (s.gpr XC).toNat = 1) := fun h' => h (hge.mpr h')
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [m8, ← hm1]
    have c0 := out_contains O (j := 0) (by decide)
    have c1 := out_contains O (j := 1) (by decide)
    have c2 := out_contains O (j := 2) (by decide)
    have c3 := out_contains O (j := 3) (by decide)
    simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at c0 c1 c2 c3
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW
      (List.mem_singleton_self _) _ c1).writeW (List.mem_singleton_self _) _ c2).writeW
      (List.mem_singleton_self _) _ c3
  · rw [r8, r7, r6, r5, u4.rd, u3.rd, u2.rd, k1.2.2.1]
  · rw [w8, w7, w6, w5, w4]
  · rw [sp8, sp7, sp6, sp5, u4.sp, u3.sp, u2.sp, k1.2.2.2.2]


/-- `csub`: `x mod p` at `[t2]`, for `x = X0 + … + 2¹⁹² X3 + 2²⁵⁶ XC` below `2p`. -/
theorem csub_ok {s : State} {O : Addr} (ht2 : s.gpr .t2 = O) (hal : O.toNat % 8 = 0)
    (hw : ∀ j < 4, InRegions s.wr (O + BitVec.ofNat 64 (8 * j)) 8) (hc : (s.gpr XC).toNat ≤ 1)
    (hx : v4 s X0 X1 X2 X3 + 2 ^ 256 * (s.gpr XC).toNat < 2 * P) :
    WP isa (.block csub) s fun s' =>
      d4 s'.mem O = (v4 s X0 X1 X2 X3 + 2 ^ 256 * (s.gpr XC).toNat) % P ∧
      Frame [⟨O, 32⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobC → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  csubWith_ok (by unfold P; omega) sumN_ok ht2 hal hw hc hx

end VG.Proof.Weierstrass.RISCV64.P256Field

namespace VG.Proof.Weierstrass.RISCV64.P256Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Proof.X25519.RISCV64 (Ctx Rest V)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok clob64 dw_write_self dw_write_other al8 dw_frame)

/-- The registers the operations write. -/
abbrev clobM : List Reg := [.t0, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a4, .a5, .a6, .a7]

/-- The own area the product writes: the copies and the product's words. -/
abbrev areaM (b : Addr) : Region := ⟨b + BitVec.ofNat 64 MA, 128⟩

/-- The words of the operand at `p` are the four doublewords at it. -/
theorem copyIn_ok {b A : Addr} {s : State} (hc : Ctx b s) {p : Reg} (hp : s.gpr p = A)
    (hp3 : p ≠ .t3 := by decide) (hp6 : p ≠ .t6 := by decide) (hp1 : p ≠ .a1 := by decide)
    (hal : A.toNat % 8 = 0) (hr : ∀ j < 4, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * j)) 8)
    {o : Nat} (ho : o + 32 ≤ 2048) (ho8 : o % 8 = 0) :
    WP isa (.block (copyIn p o)) s fun s' =>
      Ctx b s' ∧ Rest [.t3, .t6, .a1, .a4] s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      d4 s'.mem (b + BitVec.ofNat 64 o) = d4 s.mem A := by
  unfold copyIn
  have h0 := hr 0 (by decide)
  have h1 := hr 1 (by decide)
  have h2 := hr 2 (by decide)
  have h3 := hr 3 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at h0 h1 h2 h3
  refine wp_ld (off := 0) (a := A + BitVec.ofNat 64 0) (by decide) (by rw [hp]) (al8 hal (by decide)) h0
    fun s1 u1 => ?_
  refine wp_ld (off := 8) (a := A + BitVec.ofNat 64 8) (by decide) (by rw [u1.other _ hp3, hp])
    (al8 hal (by decide)) (by rw [u1.rd, u1.wr]; exact h1) fun s2 u2 => ?_
  refine wp_ld (off := 16) (a := A + BitVec.ofNat 64 16) (by decide) (by rw [u2.other _ hp6, u1.other _ hp3, hp])
    (al8 hal (by decide)) (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact h2) fun s3 u3 => ?_
  refine wp_ld (off := 24) (a := A + BitVec.ofNat 64 24) (by decide)
    (by rw [u3.other _ hp1, u2.other _ hp6, u1.other _ hp3, hp])
    (al8 hal (by decide)) (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact h3) fun s4 u4 => ?_
  have r4 : Rest [.t3, .t6, .a1, .a4] s s4 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide))))
  have hc4 : Ctx b s4 := hc.of_rest r4 (by decide)
  have m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have v0 : s4.gpr .t3 = s.mem.readW (A + BitVec.ofNat 64 0) 64 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
  have v1 : s4.gpr .t6 = s.mem.readW (A + BitVec.ofNat 64 8) 64 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.mem]
  have v2 : s4.gpr .a1 = s.mem.readW (A + BitVec.ofNat 64 16) 64 := by
    rw [u4.other _ (by decide), u3.gpr, u2.mem, u1.mem]
  have v3 : s4.gpr .a4 = s.mem.readW (A + BitVec.ofNat 64 24) 64 := by
    rw [u4.gpr, u3.mem, u2.mem, u1.mem]
  refine sd_ok hc4 (d := o) (by omega) ho8 fun s5 u5 => ?_
  have hc5 : Ctx b s5 := hc4.of_rest (u5.rest []) (by decide)
  refine sd_ok hc5 (d := o + 8) (by omega) (by omega) fun s6 u6 => ?_
  have hc6 : Ctx b s6 := hc5.of_rest (u6.rest []) (by decide)
  refine sd_ok hc6 (d := o + 16) (by omega) (by omega) fun s7 u7 => ?_
  have hc7 : Ctx b s7 := hc6.of_rest (u7.rest []) (by decide)
  refine sd_ok hc7 (d := o + 24) (by omega) (by omega) fun s8 u8 => WP.block_nil ?_
  have g8 : s8.gpr = s4.gpr := by rw [u8.gpr, u7.gpr, u6.gpr, u5.gpr]
  have hm : s8.mem = (((s.mem.writeW (b + BitVec.ofNat 64 o) (s4.gpr .t3)).writeW
      (b + BitVec.ofNat 64 (o + 8)) (s4.gpr .t6)).writeW (b + BitVec.ofNat 64 (o + 16)) (s4.gpr .a1)).writeW
      (b + BitVec.ofNat 64 (o + 24)) (s4.gpr .a4) := by
    rw [u8.mem, u7.mem, u6.mem, u5.mem, m4, u7.gpr, u6.gpr, u5.gpr]
  have r48 : Rest [] s4 s8 := ⟨fun r _ => by rw [g8], by rw [u8.rd, u7.rd, u6.rd, u5.rd],
    by rw [u8.wr, u7.wr, u6.wr, u5.wr], by rw [u8.sp, u7.sp, u6.sp, u5.sp]⟩
  refine ⟨hc4.of_rest r48 (by decide), r4.trans (r48.mono (by decide)), ?_, ?_⟩
  · rw [hm]
    have c : ∀ k < 4, (⟨b + BitVec.ofNat 64 o, 32⟩ : Region).Contains (b + BitVec.ofNat 64 (o + 8 * k)) 8 :=
      fun k hk => Offset.contains b (by omega) (by omega) (by omega)
    have c0 := c 0 (by decide)
    have c1 := c 1 (by decide)
    have c2 := c 2 (by decide)
    have c3 := c 3 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at c0 c1 c2 c3
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW
      (List.mem_singleton_self _) _ c1).writeW (List.mem_singleton_self _) _ c2).writeW
      (List.mem_singleton_self _) _ c3
  · have e : ∀ k, (b + BitVec.ofNat 64 o) + BitVec.ofNat 64 k = b + BitVec.ofNat 64 (o + k) := fun k => by
      rw [BitVec.add_assoc, BitVec.ofNat_add]
    have r : ∀ k, dw s8.mem (b + BitVec.ofNat 64 o) k = dw s8.mem b (o + k) := fun k => by
      simp only [dw, e]
    simp only [d4, r, Nat.add_zero]
    rw [hm, dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_other _ _ _ (by omega) (by omega) (by omega),
      dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_self,
      dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_other _ _ _ (by omega) (by omega) (by omega),
      dw_write_self, dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_self, dw_write_self,
      v0, v1, v2, v3]
    rfl

open VG.Proof.X25519.RISCV64.R64 (val4 V_eq4 accW accW_eq product_ok square_ok AR)
open VG.Impl.X25519.RISCV64.R64 (product square)

/-- The four doublewords at `b + o`, as offsets from `b`. -/
theorem d4_add (m : Mem) (b : Addr) (o : Nat) :
    d4 m (b + BitVec.ofNat 64 o) = val4 (fun i => dw m b (o + 8 * i)) := by
  have e : ∀ k, (b + BitVec.ofNat 64 o) + BitVec.ofNat 64 k = b + BitVec.ofNat 64 (o + k) := fun k => by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  simp only [d4, val4, dw, e, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul]
  omega

/-- The number `V` of X25519's code at `b + o`. -/
theorem V_d4 (m : Mem) (b : Addr) (o : Nat) : V m b o = d4 m (b + BitVec.ofNat 64 o) := by
  rw [V_eq4, d4_add]

/-- The product's words, as `reduce` reads them. -/
theorem accW_prodV (m : Mem) (b : Addr) : accW ACC m b 8 = prodV m b := by
  rw [accW_eq]
  simp only [VG.Proof.X448.RISCV64.R64.colsV, prodV, upW, T, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]
  omega

theorem d4_lt (m : Mem) (O : Addr) : d4 m O < 2 ^ 256 := by
  have := dw_lt m O 0; have := dw_lt m O 8; have := dw_lt m O 16; have := dw_lt m O 24
  unfold d4; omega

/-- `b + o` from `W`, for `b = W + e`. -/
theorem off_add (W : Addr) (e o : Nat) :
    W + BitVec.ofNat 64 e + BitVec.ofNat 64 o = W + BitVec.ofNat 64 (e + o) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- The four doublewords at `W + x`, through a frame of a region apart from them. -/
theorem d4_frame {m m' : Mem} {W : Addr} {e k x : Nat} (hf : Frame [⟨W + BitVec.ofNat 64 e, k⟩] m m')
    (hd : x + 32 ≤ e ∨ e + k ≤ x) (hx : x + 32 ≤ 2 ^ 64) (he : e + k ≤ 2 ^ 64) :
    d4 m' (W + BitVec.ofNat 64 x) = d4 m (W + BitVec.ofNat 64 x) := by
  rw [d4_add, d4_add]
  simp only [val4]
  have g : ∀ i < 4, dw m' W (x + 8 * i) = dw m W (x + 8 * i) := fun i hi =>
    dw_frame hf fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint W (by omega) (by omega) he
  rw [g 0 (by decide), g 1 (by decide), g 2 (by decide), g 3 (by decide)]

/-- The working space at `W`, its own area from `W + 2048`, and `a3` its base. -/
structure WsAt (W : Addr) (s : State) : Prop where
  al : W.toNat % 8 = 0
  wr : (⟨W, 8192⟩ : Region) ∈ s.wr
  fit : W.toNat + 8192 ≤ 2 ^ 64
  a3 : s.gpr .a3 = W + BitVec.ofNat 64 2048

theorem WsAt.ctx {W : Addr} {s : State} (h : WsAt W s) : Ctx (W + BitVec.ofNat 64 2048) s :=
  ⟨h.a3, al8 h.al (by decide), fun d n hd => by
    rw [off_add]; exact VG.Proof.X25519.RISCV64.in_base h.wr (by omega) (by omega)⟩

theorem WsAt.of_rest {W : Addr} {s s' : State} {ws : List Reg} (h : WsAt W s) (hr : Rest ws s s')
    (h3 : Reg.a3 ∉ ws) : WsAt W s' :=
  ⟨h.al, by rw [hr.wr]; exact h.wr, h.fit, by rw [hr.gpr _ h3, h.a3]⟩

/-- A pointer to the `32` bytes at `W + x` of the working space. -/
theorem WsAt.inR {W : Addr} {s : State} (h : WsAt W s) {x : Nat} (hx : x + 32 ≤ 8192) :
    ∀ j < 4, InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 x + BitVec.ofNat 64 (8 * j)) 8 := fun j hj => by
  rw [off_add]
  obtain ⟨r, hr, hc⟩ := VG.Proof.X25519.RISCV64.in_base (n := 8) h.wr (d := x + 8 * j) (by omega) (by omega)
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem WsAt.inW {W : Addr} {s : State} (h : WsAt W s) {x : Nat} (hx : x + 32 ≤ 8192) :
    ∀ j < 4, InRegions s.wr (W + BitVec.ofNat 64 x + BitVec.ofNat 64 (8 * j)) 8 := fun j hj => by
  rw [off_add]
  exact VG.Proof.X25519.RISCV64.in_base h.wr (by omega) (by omega)

/-- The regions `mulCore` writes, from `W`: the copies, the product and the result. -/
abbrev mulW (W : Addr) (o : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 3840, 32⟩, ⟨W + BitVec.ofNat 64 3872, 32⟩, ⟨W + BitVec.ofNat 64 3904, 64⟩,
    ⟨W + BitVec.ofNat 64 o, 32⟩]

/-- An operand apart from the copies and the product. -/
abbrev Apart (x : Nat) : Prop := x + 32 ≤ 3840 ∨ 3968 ≤ x

theorem P_pos : 0 < P := by unfold P; omega

/-- `mulWith red sum`: `[t2] = [t4] [t5] 2⁻²⁵⁶ mod m`, for a reduction `red` as
`reduce_ok`'s and a `sum` as `csubWith_ok`'s. -/
theorem mulWith_ok {red sum : List Instr} {M : Nat} (hM0 : 0 < M) (hM : M ≤ 2 ^ 256)
    (hred : ∀ {b : Addr} {s : State}, Ctx b s → WP isa (.block red) s fun s' =>
      Ctx b s' ∧ Rest clobM s s' ∧ s'.mem = s.mem ∧ (s'.gpr XC).toNat ≤ 1 ∧
      ∃ Q, Q < 2 ^ 256 ∧
        ((s'.gpr X0).toNat + 2 ^ 64 * (s'.gpr X1).toNat + 2 ^ 128 * (s'.gpr X2).toNat +
          2 ^ 192 * (s'.gpr X3).toNat + 2 ^ 256 * (s'.gpr XC).toNat) * 2 ^ 256 = prodV s.mem b + Q * M)
    (hs : ∀ s : State, WP isa (.block sum) s fun s' =>
      v4 s' .t6 .a4 .a5 .a6 + 2 ^ 256 * (s'.gpr .a7).toNat = v4 s X0 X1 X2 X3 + (2 ^ 256 - M) ∧
      (s'.gpr .a7).toNat ≤ 1 ∧ Keeps clobC s s')
    {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 32 ≤ 8192) (hb : bb + 32 ≤ 8192) (ho : o + 32 ≤ 8192) (hdb : Apart bb)
    (hB : d4 s.mem (W + BitVec.ofNat 64 bb) < M) :
    WP isa (mulWith red sum) s fun s' =>
      d4 s'.mem (W + BitVec.ofNat 64 o) < M ∧
      d4 s'.mem (W + BitVec.ofNat 64 o) * 2 ^ 256 % M =
        d4 s.mem (W + BitVec.ofNat 64 a) * d4 s.mem (W + BitVec.ofNat 64 bb) % M ∧
      Frame (mulW W o) s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hc := hw.ctx
  have alA : (W + BitVec.ofNat 64 a).toNat % 8 = 0 := al8 hw.al ha8
  have alB : (W + BitVec.ofNat 64 bb).toNat % 8 = 0 := al8 hw.al hb8
  have eMA : W + BitVec.ofNat 64 2048 + BitVec.ofNat 64 MA = W + BitVec.ofNat 64 3840 := off_add _ _ _
  have eMB : W + BitVec.ofNat 64 2048 + BitVec.ofNat 64 MB = W + BitVec.ofNat 64 3872 := off_add _ _ _
  have eAC : W + BitVec.ofNat 64 2048 + BitVec.ofNat 64 ACC = W + BitVec.ofNat 64 3904 := off_add _ _ _
  -- The product at `ACC`, by either branch.
  have hprod : WP isa prodCode s fun s' =>
      Ctx (W + BitVec.ofNat 64 2048) s' ∧ Rest clob64 s s' ∧ Frame (mulW W o) s.mem s'.mem ∧
      prodV s'.mem (W + BitVec.ofNat 64 2048) =
        d4 s.mem (W + BitVec.ofNat 64 a) * d4 s.mem (W + BitVec.ofNat 64 bb) := by
    refine WP.ite (s.gpr .t4 == s.gpr .t5) rfl (fun heq => ?_) (fun _ => ?_)
    · have hab : W + BitVec.ofNat 64 a = W + BitVec.ofNat 64 bb := by
        rw [← h4, ← h5]; exact beq_iff_eq.mp heq
      refine WP.block_append (WP.mono (copyIn_ok hc (p := .t4) h4 (hal := alA) (hr := hw.inR ha) (o := MA) (ho := by decide) (ho8 := by decide))
        fun s1 ⟨c1, r1, f1, v1⟩ => ?_)
      refine WP.mono (square_ok (acc := ACC) (x := MA) (by decide) (by decide) (by decide) (by decide) c1)
        fun s2 ⟨c2, r2, f2, v2⟩ => ⟨c2, (r1.mono (by decide)).trans r2, ?_, ?_⟩
      · rw [eMA] at f1
        simp only [AR, eAC] at f2
        exact (f1.mono (by simp)).trans (f2.mono (by simp))
      · rw [← accW_prodV, v2, V_d4, v1, ← hab]
    · refine WP.block_append (WP.block_append (WP.mono
        (copyIn_ok hc (p := .t4) h4 (hal := alA) (hr := hw.inR ha) (o := MA) (ho := by decide) (ho8 := by decide))
        fun s1 ⟨c1, r1, f1, v1⟩ => WP.mono (copyIn_ok c1 (p := .t5) (by rw [r1.gpr _ (by decide), h5]) (hal := alB)
          (hr := (hw.of_rest r1 (by decide)).inR hb) (o := MB) (ho := by decide) (ho8 := by decide))
        fun s2 ⟨c2, r2, f2, v2⟩ => ?_))
      refine WP.mono (product_ok (acc := ACC) (x := MA) (y := MB) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) c2) fun s3 ⟨c3, r3, f3, v3⟩ => ⟨c3, ((r1.trans r2).mono (by decide)).trans r3, ?_, ?_⟩
      · rw [eMA] at f1
        rw [eMB] at f2
        simp only [AR, eAC] at f3
        exact ((f1.mono (by simp)).trans (f2.mono (by simp))).trans (f3.mono (by simp))
      · rw [eMA] at f1 v1
        rw [eMB] at f2 v2
        rw [← accW_prodV, v3, V_d4, V_d4, eMA, eMB, v2, d4_frame f1 (by unfold Apart at hdb; omega) (by omega)
          (by omega), d4_frame f2 (by omega) (by omega) (by omega), v1]
  refine WP.seq (WP.mono hprod fun s1 ⟨c1, r1, f1, v1⟩ => ?_)
  refine WP.block_append (WP.mono (hred c1) fun s2 ⟨c2, r2, m2, x2, Q, hQ, hv2⟩ => ?_)
  have hw2 : WsAt W s2 := hw.of_rest ((r1.mono (by decide) : Rest clobM _ _).trans r2) (by decide)
  have hlt : prodV s1.mem (W + BitVec.ofNat 64 2048) < 2 ^ 256 * M := by
    rw [v1]
    exact Nat.mul_lt_mul_of_lt_of_le (d4_lt _ _) (Nat.le_of_lt hB) hM0
  have hx : v4 s2 X0 X1 X2 X3 + 2 ^ 256 * (s2.gpr XC).toNat < 2 * M := by
    simp only [v4]
    generalize (s2.gpr X0).toNat + 2 ^ 64 * (s2.gpr X1).toNat + 2 ^ 128 * (s2.gpr X2).toNat +
      2 ^ 192 * (s2.gpr X3).toNat + 2 ^ 256 * (s2.gpr XC).toNat = x at hv2 ⊢
    have h1 : Q * M < 2 ^ 256 * M := Nat.mul_lt_mul_of_pos_right hQ hM0
    have h2 : x * 2 ^ 256 < 2 * M * 2 ^ 256 := by
      rw [hv2]
      calc _ < 2 ^ 256 * M + 2 ^ 256 * M := Nat.add_lt_add hlt h1
        _ = 2 * M * 2 ^ 256 := by rw [← Nat.two_mul, Nat.mul_comm (2 ^ 256) M, Nat.mul_assoc]
    exact Nat.lt_of_mul_lt_mul_right h2
  refine WP.mono (csubWith_ok hM (hs s2) (O := W + BitVec.ofNat 64 o) (by rw [((r1.mono (by decide) : Rest clobM _ _).trans r2).gpr _ (by decide), h2])
    (al8 hw.al ho8) (hw2.inW ho) x2 hx) fun s3 ⟨v3, f3, g3, rd3, wr3, sp3⟩ => ?_
  have hm2 : s2.mem = s1.mem := m2
  rw [hm2] at f3
  refine ⟨by rw [v3]; exact Nat.mod_lt _ hM0, ?_, f1.trans (f3.mono (by simp)), fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [v3, Nat.mod_mul_mod]
    simp only [v4] at hv2 ⊢
    rw [hv2, Nat.add_mul_mod_self_right, v1]
  · have sC : ∀ x ∈ clobC, x ∈ clobM := by decide
    have s6 : ∀ x ∈ clob64, x ∈ clobM := by decide
    rw [g3 r (fun h => hr (sC r h)), ((r1.mono (by decide) : Rest clobM _ _).trans r2).gpr r hr]
  · rw [rd3, r2.rd, r1.rd]
  · rw [wr3, r2.wr, r1.wr]
  · rw [sp3, r2.sp, r1.sp]

/-- `mulCore`: `[t2] = [t4] [t5] 2⁻²⁵⁶ mod p`. -/
theorem mulCore_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 32 ≤ 8192) (hb : bb + 32 ≤ 8192) (ho : o + 32 ≤ 8192) (hdb : Apart bb)
    (hB : d4 s.mem (W + BitVec.ofNat 64 bb) < P) :
    WP isa mulCore s fun s' =>
      d4 s'.mem (W + BitVec.ofNat 64 o) < P ∧
      d4 s'.mem (W + BitVec.ofNat 64 o) * 2 ^ 256 % P =
        d4 s.mem (W + BitVec.ofNat 64 a) * d4 s.mem (W + BitVec.ofNat 64 bb) % P ∧
      Frame (mulW W o) s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  mulWith_ok P_pos (by unfold P; omega)
    (fun hc => WP.mono (reduce_ok hc) fun _ ⟨c, r, m, x, q⟩ => ⟨c, r.mono (by decide), m, x, q⟩) (fun _ => sumN_ok) hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB

end VG.Proof.Weierstrass.RISCV64.P256Field

/-!
## P-256's field on RISC-V: sums and differences

`addCore` (`addCore_ok`): the operands' words loaded (`loadAB_ok`), their sum
with carries (below `2p`), reduced by `csub`. `subCore` (`subCore_ok`): their
difference with borrows, and `p` added back under the mask of the borrow, a
word at a time, each stored at `[t2]` (`addPWord_ok`).
-/

namespace VG.Proof.Weierstrass.RISCV64.P256Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Proof.X25519.RISCV64 (Ctx Rest)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt clob64 dw_write_self dw_write_other al8 Keeps.rest)

/-- `s'` is `s` but for the registers `rs` and the memory. -/
def Keeps' (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

/-- The words of `[t4]` and `[t5]` in registers. -/
theorem loadAB_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ha : a + 32 ≤ 8192) (hb : bb + 32 ≤ 8192) :
    WP isa (.block loadAB) s fun s' =>
      v4 s' .a1 .t3 .t6 .a4 = d4 s.mem (W + BitVec.ofNat 64 a) ∧
      v4 s' .a5 .a6 .a7 .t0 = d4 s.mem (W + BitVec.ofNat 64 bb) ∧
      Rest [.a1, .t3, .t6, .a4, .a5, .a6, .a7, .t0] s s' ∧ s'.mem = s.mem := by
  have rA := hw.inR ha
  have rB := hw.inR hb
  have alA := al8 hw.al ha8
  have alB := al8 hw.al hb8
  simp only [off_add] at rA rB
  have rA0 := rA 0 (by decide); have rA1 := rA 1 (by decide); have rA2 := rA 2 (by decide)
  have rA3 := rA 3 (by decide)
  have rB0 := rB 0 (by decide); have rB1 := rB 1 (by decide); have rB2 := rB 2 (by decide)
  have rB3 := rB 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at rA0 rA1 rA2 rA3 rB0 rB1 rB2 rB3
  unfold loadAB
  refine wp_ld (off := 0) (a := W + BitVec.ofNat 64 a) (by decide) (by rw [h4]; simp) alA rA0 fun s1 u1 => ?_
  refine wp_ld (off := 8) (a := W + BitVec.ofNat 64 (a + 8)) (by decide) (by rw [u1.other _ (by decide), h4, off_add])
    (al8 hw.al (by omega)) (by rw [u1.rd, u1.wr]; exact rA1) fun s2 u2 => ?_
  refine wp_ld (off := 16) (a := W + BitVec.ofNat 64 (a + 16)) (by decide)
    (by rw [u2.other _ (by decide), u1.other _ (by decide), h4, off_add])
    (al8 hw.al (by omega)) (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact rA2) fun s3 u3 => ?_
  refine wp_ld (off := 24) (a := W + BitVec.ofNat 64 (a + 24)) (by decide)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h4, off_add])
    (al8 hw.al (by omega)) (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact rA3) fun s4 u4 => ?_
  have g4 : s4.gpr .t5 = s.gpr .t5 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
  have p4 : s4.rd ++ s4.wr = s.rd ++ s.wr := by rw [u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]
  refine wp_ld (off := 0) (a := W + BitVec.ofNat 64 bb) (by decide) (by rw [g4, h5]; simp) alB
    (by rw [p4]; exact rB0) fun s5 u5 => ?_
  refine wp_ld (off := 8) (a := W + BitVec.ofNat 64 (bb + 8)) (by decide)
    (by rw [u5.other _ (by decide), g4, h5, off_add])
    (al8 hw.al (by omega)) (by rw [u5.rd, u5.wr, p4]; exact rB1) fun s6 u6 => ?_
  refine wp_ld (off := 16) (a := W + BitVec.ofNat 64 (bb + 16)) (by decide)
    (by rw [u6.other _ (by decide), u5.other _ (by decide), g4, h5, off_add])
    (al8 hw.al (by omega)) (by rw [u6.rd, u6.wr, u5.rd, u5.wr, p4]; exact rB2) fun s7 u7 => ?_
  refine wp_ld (off := 24) (a := W + BitVec.ofNat 64 (bb + 24)) (by decide)
    (by rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), g4, h5, off_add])
    (al8 hw.al (by omega)) (by rw [u7.rd, u7.wr, u6.rd, u6.wr, u5.rd, u5.wr, p4]; exact rB3)
    fun s8 u8 => WP.block_nil ?_
  have m8 : s8.mem = s.mem := by
    rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨?_, ?_, ?_, m8⟩
  · simp only [v4, d4, dw]
    rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide),
      u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr,
      u8.other .t3 (by decide), u7.other .t3 (by decide), u6.other .t3 (by decide), u5.other .t3 (by decide),
      u4.other .t3 (by decide), u3.other .t3 (by decide), u2.gpr, u1.mem,
      u8.other .t6 (by decide), u7.other .t6 (by decide), u6.other .t6 (by decide), u5.other .t6 (by decide),
      u4.other .t6 (by decide), u3.gpr, u2.mem, u1.mem,
      u8.other .a4 (by decide), u7.other .a4 (by decide), u6.other .a4 (by decide), u5.other .a4 (by decide),
      u4.gpr, u3.mem, u2.mem, u1.mem]
    simp only [off_add, Nat.add_zero]
  · simp only [v4, d4, dw]
    rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.gpr,
      u8.other .a6 (by decide), u7.other .a6 (by decide), u6.gpr, u5.mem,
      u8.other .a7 (by decide), u7.gpr, u6.mem, u5.mem, u8.gpr, u7.mem, u6.mem, u5.mem,
      u4.mem, u3.mem, u2.mem, u1.mem]
    simp only [off_add, Nat.add_zero]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
      ((u7.rest (by decide)).trans (u8.rest (by decide))))))))

/-- `addSum ++ (sum ++ csubTail)`: `[t2] = ([t4] + [t5]) mod m`, for a sum below
`2m` and a `sum` as `csubWith_ok`'s. -/
theorem addWith_ok {sum : List Instr} {M : Nat} (hM : M ≤ 2 ^ 256)
    (hs : ∀ s : State, WP isa (.block sum) s fun s' =>
      v4 s' .t6 .a4 .a5 .a6 + 2 ^ 256 * (s'.gpr .a7).toNat = v4 s X0 X1 X2 X3 + (2 ^ 256 - M) ∧
      (s'.gpr .a7).toNat ≤ 1 ∧ Keeps clobC s s')
    {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 32 ≤ 8192) (hb : bb + 32 ≤ 8192) (ho : o + 32 ≤ 8192)
    (hab : d4 s.mem (W + BitVec.ofNat 64 a) + d4 s.mem (W + BitVec.ofNat 64 bb) < 2 * M) :
    WP isa (.block (addSum ++ (sum ++ csubTail))) s fun s' =>
      d4 s'.mem (W + BitVec.ofNat 64 o) =
        (d4 s.mem (W + BitVec.ofNat 64 a) + d4 s.mem (W + BitVec.ofNat 64 bb)) % M ∧
      Frame [⟨W + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold addSum addWord
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (loadAB_ok hw h4 h5 ha8 hb8 ha hb) fun s1 ⟨vA, vB, r1, m1⟩ => ?_)
  refine WP.block_append (WP.mono (add1_ok (d := .a1) (y := .a5) (c := .a2)) fun s2 ⟨e2, k2⟩ => ?_)
  refine WP.block_append (WP.mono (adc_ok (d := .t3) (x := .t3) (y := .a6) (c := .a2) (u := .a5))
    fun s3 ⟨e3, k3⟩ => ?_)
  refine WP.block_append (WP.mono (adc_ok (d := .t4) (x := .t6) (y := .a7) (c := .a2) (u := .a5))
    fun s4 ⟨e4, k4⟩ => ?_)
  refine WP.block_append (WP.mono (adc_ok (d := .t5) (x := .a4) (y := .t0) (c := .a2) (u := .a5))
    fun s5 ⟨e5, k5⟩ => ?_)
  have b2 := (s2.gpr .a1).isLt
  have c2 : (s2.gpr .a2).toNat ≤ 1 := by have := (s1.gpr .a1).isLt; have := (s1.gpr .a5).isLt; omega
  have e3' := e3 c2
  rw [k2.1 .t3 (by decide), k2.1 .a6 (by decide)] at e3'
  have b3 := (s3.gpr .t3).isLt
  have c3 : (s3.gpr .a2).toNat ≤ 1 := by
    have := (s1.gpr .t3).isLt; have := (s1.gpr .a6).isLt; omega
  have e4' := e4 c3
  rw [k3.1 .t6 (by decide), k3.1 .a7 (by decide), k2.1 .t6 (by decide), k2.1 .a7 (by decide)] at e4'
  have b4 := (s4.gpr .t4).isLt
  have c4 : (s4.gpr .a2).toNat ≤ 1 := by
    have := (s1.gpr .t6).isLt; have := (s1.gpr .a7).isLt; omega
  have e5' := e5 c4
  rw [k4.1 .a4 (by decide), k4.1 .t0 (by decide), k3.1 .a4 (by decide), k3.1 .t0 (by decide),
    k2.1 .a4 (by decide), k2.1 .t0 (by decide)] at e5'
  have hr5 : Rest clobM s s5 := (r1.mono (by decide)).trans (((Keeps.rest k2).mono (by decide)).trans
    (((Keeps.rest k3).mono (by decide)).trans (((Keeps.rest k4).mono (by decide)).trans
    ((Keeps.rest k5).mono (by decide)))))
  have w5 : WsAt W s5 := hw.of_rest hr5 (by decide)
  have g5 : ∀ r, r ∉ clobM → s5.gpr r = s.gpr r := hr5.gpr
  have hsum : v4 s5 X0 X1 X2 X3 + 2 ^ 256 * (s5.gpr XC).toNat =
      d4 s.mem (W + BitVec.ofNat 64 a) + d4 s.mem (W + BitVec.ofNat 64 bb) := by
    rw [← vA, ← vB]
    simp only [v4, X0, X1, X2, X3, XC]
    rw [k5.1 .a1 (by decide), k4.1 .a1 (by decide), k3.1 .a1 (by decide), k5.1 .t3 (by decide),
      k4.1 .t3 (by decide), k5.1 .t4 (by decide)]
    omega
  refine WP.mono (csubWith_ok hM (hs s5) (O := W + BitVec.ofNat 64 o) (by rw [g5 _ (by decide), h2])
    (al8 hw.al ho8) (w5.inW ho) (by show (s5.gpr .a2).toNat ≤ 1; have := e5'; omega) (by rw [hsum]; exact hab))
    fun s6 ⟨v6, f6, g6, rd6, wr6, sp6⟩ => ⟨by rw [v6, hsum], ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have m5 : s5.mem = s.mem := by rw [k5.2.1, k4.2.1, k3.2.1, k2.2.1, m1]
    rw [m5] at f6; exact f6
  · have sC : ∀ x ∈ clobC, x ∈ clobM := by decide
    rw [g6 r (fun h => hr (sC r h)), g5 r hr]
  · rw [rd6, hr5.rd]
  · rw [wr6, hr5.wr]
  · rw [sp6, hr5.sp]

/-- `addCore`: `[t2] = ([t4] + [t5]) mod p`, for a sum below `2p`. -/
theorem addCore_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 32 ≤ 8192) (hb : bb + 32 ≤ 8192) (ho : o + 32 ≤ 8192)
    (hab : d4 s.mem (W + BitVec.ofNat 64 a) + d4 s.mem (W + BitVec.ofNat 64 bb) < 2 * P) :
    WP isa (.block addCore) s fun s' =>
      d4 s'.mem (W + BitVec.ofNat 64 o) =
        (d4 s.mem (W + BitVec.ofNat 64 a) + d4 s.mem (W + BitVec.ofNat 64 bb)) % P ∧
      Frame [⟨W + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  addWith_ok (sum := sumP) (by unfold P; omega) (fun _ => sumN_ok) hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hab

set_option linter.unusedSimpArgs false in
/-- `d := d - y` and its borrow into `c`. -/
theorem sub1_ok {s : State} {d y c : Reg} (hdc : d ≠ c := by decide) (hcy : c ≠ y := by decide) :
    WP isa (.block [.sltu c d y, .sub d d y]) s fun s' =>
      (s'.gpr d).toNat + (s.gpr y).toNat = (s.gpr d).toNat + 2 ^ 64 * (s'.gpr c).toNat ∧
      (s'.gpr c).toNat ≤ 1 ∧ Keeps [d, c] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_sub, exec_sltu,
    RegUpd.gpr_write, hdc, hcy, Ne.symm hdc, Ne.symm hcy, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  have := sub_borrow (s.gpr d) (s.gpr y)
  have b := sltu_toNat (s.gpr d) (s.gpr y)
  refine ⟨by rw [this, b], by rw [b]; split <;> omega, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- The difference of the words in registers, `D + B = A + 2²⁵⁶ β`. -/
theorem diff_ok {s : State} :
    WP isa (.block (([.sltu .a2 .a1 .a5, .sub .a1 .a1 .a5] : List Instr) ++ subWord .t3 .t3 .a6 ++ subWord .t4 .t6 .a7 ++
      subWord .t5 .a4 .t0)) s fun s' =>
      v4 s' .a1 .t3 .t4 .t5 + v4 s .a5 .a6 .a7 .t0 = v4 s .a1 .t3 .t6 .a4 + 2 ^ 256 * (s'.gpr .a2).toNat ∧
      (s'.gpr .a2).toNat ≤ 1 ∧ Keeps [.a1, .a2, .t3, .a5, .a0, .t4, .t5] s s' := by
  unfold subWord
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (sub1_ok (d := .a1) (y := .a5) (c := .a2)) fun s1 ⟨e1, c1, k1⟩ => ?_)
  refine WP.block_append (WP.mono (sbb_ok (d := .t3) (x := .t3) (y := .a6) (c := .a2) (u := .a5) (v := .a0))
    fun s2 ⟨e2, k2⟩ => ?_)
  refine WP.block_append (WP.mono (sbb_ok (d := .t4) (x := .t6) (y := .a7) (c := .a2) (u := .a5) (v := .a0))
    fun s3 ⟨e3, k3⟩ => ?_)
  refine WP.mono (sbb_ok (d := .t5) (x := .a4) (y := .t0) (c := .a2) (u := .a5) (v := .a0))
    fun s4 ⟨e4, k4⟩ => ?_
  obtain ⟨e2, c2⟩ := e2 c1
  obtain ⟨e3, c3⟩ := e3 c2
  obtain ⟨e4, c4⟩ := e4 c3
  rw [k1.1 .t3 (by decide), k1.1 .a6 (by decide)] at e2
  rw [k2.1 .t6 (by decide), k2.1 .a7 (by decide), k1.1 .t6 (by decide), k1.1 .a7 (by decide)] at e3
  rw [k3.1 .a4 (by decide), k3.1 .t0 (by decide), k2.1 .a4 (by decide), k2.1 .t0 (by decide),
    k1.1 .a4 (by decide), k1.1 .t0 (by decide)] at e4
  refine ⟨?_, c4, ((k1.trans k2).trans (k3.trans k4)).mono (by decide)⟩
  simp only [v4]
  rw [k4.1 .a1 (by decide), k3.1 .a1 (by decide), k2.1 .a1 (by decide), k4.1 .t3 (by decide),
    k3.1 .t3 (by decide), k4.1 .t4 (by decide)]
  omega

/-- The words of `p` under the mask of a borrow `β`. -/
theorem pmask {β : BitVec 64} (hb : β.toNat ≤ 1) :
    (0 - β).toNat = (if β.toNat = 1 then 2 ^ 64 - 1 else 0) ∧
    ((0 - β) >>> 32).toNat = (if β.toNat = 1 then 2 ^ 32 - 1 else 0) ∧
    ((0 - β) <<< 32 ||| (0 - β) >>> 63).toNat = (if β.toNat = 1 then 2 ^ 64 - 2 ^ 32 + 1 else 0) := by
  have h : β = 0 ∨ β = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h | h
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  rcases h with rfl | rfl <;> decide

/-- `a1 += t6`, the carry into `a7`, stored at `[t2]`. -/
theorem addP0_ok {s : State} {O : Addr} (ht2 : s.gpr .t2 = O) (hal : O.toNat % 8 = 0)
    (hw : InRegions s.wr O 8) :
    WP isa (.block (addPWord .a1 0)) s fun s' =>
      (s'.gpr .a1).toNat + 2 ^ 64 * (s'.gpr .a7).toNat = (s.gpr .a1).toNat + (s.gpr .t6).toNat ∧
      s'.mem = s.mem.writeW O (s'.gpr .a1) ∧ Keeps' [.a1, .a7] s s' := by
  unfold addPWord
  simp only [↓reduceIte, Nat.mul_zero, List.cons_append, List.nil_append]
  rw [show ([.add .a1 .a1 .t6, .sltu .a7 .a1 .t6, .store .d .a1 .t2 0] : List Instr) =
    [.add .a1 .a1 .t6, .sltu .a7 .a1 .t6] ++ [.store .d .a1 .t2 0] from rfl]
  refine WP.block_append (WP.mono (add1_ok (d := .a1) (y := .t6) (c := .a7)) fun s1 ⟨e1, k1⟩ => ?_)
  refine wp_sd (off := 0) (a := O) (by decide) (by rw [k1.1 .t2 (by decide), ht2]; simp) hal
    (by rw [k1.2.2.2.1]; exact hw) fun s2 u2 => WP.block_nil ?_
  refine ⟨by rw [u2.gpr]; exact e1, by rw [u2.mem, k1.2.1, u2.gpr], ?_⟩
  exact ⟨fun r hr => by rw [u2.gpr]; exact k1.1 r hr, by rw [u2.rd, k1.2.2.1], by rw [u2.wr, k1.2.2.2.1],
    by rw [u2.sp, k1.2.2.2.2]⟩

/-- `x += t6 + c` (`c` in `a7`), stored at `[t2 + 8j]`. -/
theorem addPStep_ok {s : State} {O : Addr} {x : Reg} {j : Nat} (hj : j < 4) (ht2 : s.gpr .t2 = O)
    (hal : O.toNat % 8 = 0) (hw : InRegions s.wr (O + BitVec.ofNat 64 (8 * j)) 8) (hj0 : 0 < j)
    (hc : (s.gpr .a7).toNat ≤ 1) (hx6 : x ≠ .t6 := by decide) (hx7 : x ≠ .a7 := by decide)
    (hx0 : x ≠ .a0 := by decide) (hx2 : x ≠ .t2 := by decide) :
    WP isa (.block (addPWord x j)) s fun s' =>
      (s'.gpr x).toNat + 2 ^ 64 * (s'.gpr .a7).toNat = (s.gpr x).toNat + (s.gpr .t6).toNat + (s.gpr .a7).toNat ∧
      s'.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j)) (s'.gpr x) ∧ Keeps' [x, .a0, .a7] s s' := by
  unfold addPWord
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
  refine WP.block_append (WP.mono (adc_ok (d := x) (x := x) (y := .t6) (c := .a7) (u := .a0) hx6 hx7
      (Ne.symm hx0))
    fun s1 ⟨e1, k1⟩ => ?_)
  refine wp_sd (by omega) (by rw [k1.1 .t2 (by simp [Ne.symm hx2]), ht2]) (al8 hal (by omega))
    (by rw [k1.2.2.2.1]; exact hw) fun s2 u2 => WP.block_nil ?_
  refine ⟨by rw [u2.gpr]; exact e1 hc, by rw [u2.mem, k1.2.1, u2.gpr], ?_⟩
  exact ⟨fun r hr => by rw [u2.gpr]; exact k1.1 r hr, by rw [u2.rd, k1.2.2.1], by rw [u2.wr, k1.2.2.2.1],
    by rw [u2.sp, k1.2.2.2.2]⟩

/-! The value `subWith` stores, in steps small enough for `omega`. -/

theorem chain4 {o0 o1 o2 o3 k0 k1 k2 k3 D0 D1 D2 D3 m0 m1 m2 m3 : Nat}
    (e0 : o0 + 2 ^ 64 * k0 = D0 + m0) (e1 : o1 + 2 ^ 64 * k1 = D1 + m1 + k0)
    (e2 : o2 + 2 ^ 64 * k2 = D2 + m2 + k1) (e3 : o3 + 2 ^ 64 * k3 = D3 + m3 + k2) :
    o0 + 2 ^ 64 * (o1 + 2 ^ 64 * (o2 + 2 ^ 64 * o3)) + 2 ^ 256 * k3 =
      D0 + 2 ^ 64 * D1 + 2 ^ 128 * D2 + 2 ^ 192 * D3 + (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) := by
  omega

theorem lt4 {o0 o1 o2 o3 : Nat} (b0 : o0 < 2 ^ 64) (b1 : o1 < 2 ^ 64) (b2 : o2 < 2 ^ 64) (b3 : o3 < 2 ^ 64) :
    o0 + 2 ^ 64 * (o1 + 2 ^ 64 * (o2 + 2 ^ 64 * o3)) < 2 ^ 256 := by omega

theorem lt4' {o0 o1 o2 o3 : Nat} (b0 : o0 < 2 ^ 64) (b1 : o1 < 2 ^ 64) (b2 : o2 < 2 ^ 64) (b3 : o3 < 2 ^ 64) :
    o0 + 2 ^ 64 * o1 + 2 ^ 128 * o2 + 2 ^ 192 * o3 < 2 ^ 256 := by omega

theorem fin1 {O k D M A B : Nat} (hO : O < 2 ^ 256) (hM : M ≤ 2 ^ 256) (hA : A < M) (hB : B < M)
    (h : O + 2 ^ 256 * k = D + M) (hD : D + B = A + 2 ^ 256 * 1) (hDl : D < 2 ^ 256) :
    O = (A + M - B) % M := by
  rw [Nat.mod_eq_of_lt (by omega)]
  have : k = 1 := by omega
  omega

theorem fin0 {O k D M A B : Nat} (hO : O < 2 ^ 256) (hA : A < M) (hB : B < M)
    (h : O + 2 ^ 256 * k = D) (hD : D + B = A + 2 ^ 256 * 0) (hDl : D < 2 ^ 256) :
    O = (A + M - B) % M := by
  rw [show A + M - B = (A - B) + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have : k = 0 := by omega
  omega

/-- The value `subWith` stores, for a modulus `M` of words `mⱼ`. -/
theorem sub_final {M m0 m1 m2 m3 A B D0 D1 D2 D3 β o0 o1 o2 o3 k0 k1 k2 k3 : Nat}
    (hM : M = m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) (hA : A < M) (hB : B < M)
    (hD : D0 + 2 ^ 64 * D1 + 2 ^ 128 * D2 + 2 ^ 192 * D3 + B = A + 2 ^ 256 * β) (hβ : β ≤ 1)
    (b0 : o0 < 2 ^ 64) (b1 : o1 < 2 ^ 64) (b2 : o2 < 2 ^ 64) (b3 : o3 < 2 ^ 64)
    (c0 : D0 < 2 ^ 64) (c1 : D1 < 2 ^ 64) (c2 : D2 < 2 ^ 64) (c3 : D3 < 2 ^ 64)
    (n0 : m0 < 2 ^ 64) (n1 : m1 < 2 ^ 64) (n2 : m2 < 2 ^ 64) (n3 : m3 < 2 ^ 64)
    (e0 : o0 + 2 ^ 64 * k0 = D0 + (if β = 1 then m0 else 0))
    (e1 : o1 + 2 ^ 64 * k1 = D1 + (if β = 1 then m1 else 0) + k0)
    (e2 : o2 + 2 ^ 64 * k2 = D2 + (if β = 1 then m2 else 0) + k1)
    (e3 : o3 + 2 ^ 64 * k3 = D3 + (if β = 1 then m3 else 0) + k2) :
    o0 + 2 ^ 64 * (o1 + 2 ^ 64 * (o2 + 2 ^ 64 * o3)) = (A + M - B) % M := by
  have hO := lt4 b0 b1 b2 b3
  have hDl := lt4' c0 c1 c2 c3
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hβ with rfl | rfl
  · simp only [Nat.zero_ne_one, ↓reduceIte] at e0 e1 e2 e3
    have h := chain4 e0 e1 e2 e3
    simp only [Nat.mul_zero, Nat.add_zero] at h
    exact fin0 hO hA hB h hD hDl
  · simp only [↓reduceIte] at e0 e1 e2 e3
    have h := chain4 e0 e1 e2 e3
    rw [← hM] at h
    exact fin1 hO (by rw [hM]; exact Nat.le_of_lt (lt4' n0 n1 n2 n3)) hA hB h hD hDl

/-- A block that puts the word `m` of a modulus, under the mask `0 - β` of a
borrow `β` in `t0`, into `t6`, through `a0` and `a4`. -/
def KOk (k : List Instr) (m : Nat) : Prop :=
  ∀ (s : State) (β : BitVec 64), β.toNat ≤ 1 → s.gpr .t0 = 0 - β → WP isa (.block k) s fun s' =>
    (s'.gpr .t6).toNat = (if β.toNat = 1 then m else 0) ∧ Keeps' [.t6, .a0, .a4] s s' ∧ s'.mem = s.mem

/-- `subWith k0 k1 k2 k3`: `[t2] = ([t4] - [t5]) mod m`, for operands below
`m` and blocks `kⱼ` putting `m`'s words. -/
theorem subWith_ok {k0 k1 k2 k3 : List Instr} {M m0 m1 m2 m3 : Nat}
    (hM : M = m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3)
    (n0 : m0 < 2 ^ 64) (n1 : m1 < 2 ^ 64) (n2 : m2 < 2 ^ 64) (n3 : m3 < 2 ^ 64)
    (hk0 : KOk k0 m0) (hk1 : KOk k1 m1) (hk2 : KOk k2 m2) (hk3 : KOk k3 m3)
    {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 32 ≤ 8192) (hb : bb + 32 ≤ 8192) (ho : o + 32 ≤ 8192)
    (hA : d4 s.mem (W + BitVec.ofNat 64 a) < M) (hB : d4 s.mem (W + BitVec.ofNat 64 bb) < M) :
    WP isa (.block (subWith k0 k1 k2 k3)) s fun s' =>
      d4 s'.mem (W + BitVec.ofNat 64 o) =
        (d4 s.mem (W + BitVec.ofNat 64 a) + M - d4 s.mem (W + BitVec.ofNat 64 bb)) % M ∧
      Frame [⟨W + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hW := hw.inW ho
  have w0 := hW 0 (by decide); have w1 := hW 1 (by decide); have w2 := hW 2 (by decide)
  have w3 := hW 3 (by decide)
  have alO := al8 hw.al ho8
  unfold subWith subDiff
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (loadAB_ok hw h4 h5 ha8 hb8 ha hb) fun s1 ⟨vA, vB, r1, m1⟩ => ?_)
  rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
  refine WP.block_append (WP.mono diff_ok fun s2 ⟨e2, c2, k2⟩ => ?_)
  refine wp_li (imm := 0) (by decide) fun s3 u3 => wp_sub fun s4 u4 => ?_
  have hm : s4.gpr .t0 = 0 - s2.gpr .a2 := by
    rw [u4.gpr, u3.gpr, u3.other _ (by decide)]; rfl
  have g4 : ∀ r, r ≠ .t0 → s4.gpr r = s2.gpr r := fun r h0 => by rw [u4.other _ h0, u3.other _ h0]
  have t2_4 : s4.gpr .t2 = W + BitVec.ofNat 64 o := by
    rw [g4 _ (by decide), k2.1 _ (by decide), r1.gpr _ (by decide), h2]
  have wr4 : s4.wr = s.wr := by rw [u4.wr, u3.wr, k2.2.2.2.1, r1.wr]
  -- Word 0.
  show WP isa (.block (k0 ++ _)) s4 _
  refine WP.block_append (WP.mono (hk0 s4 _ c2 hm) fun s5 ⟨q0, g5, mm5⟩ => ?_)
  refine WP.block_append (WP.mono (addP0_ok (O := W + BitVec.ofNat 64 o) (by rw [g5.1 _ (by decide), t2_4])
    alO (by rw [g5.2.2.1, wr4]; simpa using w0)) fun s6 ⟨e6, m6, k6⟩ => ?_)
  -- Word 1.
  have t0_6 : s6.gpr .t0 = 0 - s2.gpr .a2 := by rw [k6.1 _ (by decide), g5.1 _ (by decide), hm]
  refine WP.block_append (WP.mono (hk1 s6 _ c2 t0_6) fun s7 ⟨q1, g7, mm7⟩ => ?_)
  have c6 : (s7.gpr .a7).toNat ≤ 1 := by
    rw [g7.1 _ (by decide)]; have := (s6.gpr .a1).isLt; have := (s5.gpr .a1).isLt
    have := (s5.gpr .t6).isLt; omega
  refine WP.block_append (WP.mono (addPStep_ok (O := W + BitVec.ofNat 64 o) (x := .t3) (j := 1) (by decide)
    (by rw [g7.1 _ (by decide), k6.1 _ (by decide), g5.1 _ (by decide), t2_4]) alO
    (by rw [g7.2.2.1, k6.2.2.1, g5.2.2.1, wr4]; exact w1) (by decide) c6) fun s8 ⟨e8, m8, k8⟩ => ?_)
  -- Word 2.
  have t0_8 : s8.gpr .t0 = 0 - s2.gpr .a2 := by
    rw [k8.1 _ (by decide), g7.1 _ (by decide), t0_6]
  refine WP.block_append (WP.mono (hk2 s8 _ c2 t0_8) fun s9 ⟨q2, g9, mm9⟩ => ?_)
  have c8 : (s9.gpr .a7).toNat ≤ 1 := by
    rw [g9.1 _ (by decide)]; have := (s8.gpr .t3).isLt; have := (s7.gpr .t3).isLt
    have := (s7.gpr .t6).isLt; omega
  refine WP.block_append (WP.mono (addPStep_ok (O := W + BitVec.ofNat 64 o) (x := .t4) (j := 2) (by decide)
    (by rw [g9.1 _ (by decide), k8.1 _ (by decide), g7.1 _ (by decide), k6.1 _ (by decide),
      g5.1 _ (by decide), t2_4]) alO
    (by rw [g9.2.2.1, k8.2.2.1, g7.2.2.1, k6.2.2.1, g5.2.2.1, wr4]; exact w2) (by decide) c8)
    fun s10 ⟨e10, m10, k10⟩ => ?_)
  -- Word 3.
  have t0_10 : s10.gpr .t0 = 0 - s2.gpr .a2 := by
    rw [k10.1 _ (by decide), g9.1 _ (by decide), t0_8]
  refine WP.block_append (WP.mono (hk3 s10 _ c2 t0_10) fun s11 ⟨q3, g11, mm11⟩ => ?_)
  have c10 : (s11.gpr .a7).toNat ≤ 1 := by
    rw [g11.1 _ (by decide)]; have := (s10.gpr .t4).isLt; have := (s9.gpr .t4).isLt
    have := (s9.gpr .t6).isLt; omega
  refine WP.mono (addPStep_ok (O := W + BitVec.ofNat 64 o) (x := .t5) (j := 3) (by decide)
    (by rw [g11.1 _ (by decide), k10.1 _ (by decide), g9.1 _ (by decide), k8.1 _ (by decide),
      g7.1 _ (by decide), k6.1 _ (by decide), g5.1 _ (by decide), t2_4]) alO
    (by rw [g11.2.2.1, k10.2.2.1, g9.2.2.1, k8.2.2.1, g7.2.2.1, k6.2.2.1, g5.2.2.1, wr4]; exact w3)
    (by decide) c10) fun s12 ⟨e12, m12, k12⟩ => ?_
  -- The words of the difference, through the steps.
  have d0 : s5.gpr .a1 = s2.gpr .a1 := by rw [g5.1 _ (by decide), g4 _ (by decide)]
  have d1 : s7.gpr .t3 = s2.gpr .t3 := by
    rw [g7.1 _ (by decide), k6.1 _ (by decide), g5.1 _ (by decide), g4 _ (by decide)]
  have d2 : s9.gpr .t4 = s2.gpr .t4 := by
    rw [g9.1 _ (by decide), k8.1 _ (by decide), g7.1 _ (by decide), k6.1 _ (by decide),
      g5.1 _ (by decide), g4 _ (by decide)]
  have d3 : s11.gpr .t5 = s2.gpr .t5 := by
    rw [g11.1 _ (by decide), k10.1 _ (by decide), g9.1 _ (by decide), k8.1 _ (by decide),
      g7.1 _ (by decide), k6.1 _ (by decide), g5.1 _ (by decide), g4 _ (by decide)]
  have a7_7 : s7.gpr .a7 = s6.gpr .a7 := g7.1 _ (by decide)
  have a7_9 : s9.gpr .a7 = s8.gpr .a7 := g9.1 _ (by decide)
  have a7_11 : s11.gpr .a7 = s10.gpr .a7 := g11.1 _ (by decide)
  rw [d0, q0] at e6
  rw [d1, q1, a7_7] at e8
  rw [d2, q2, a7_9] at e10
  rw [d3, q3, a7_11] at e12
  -- The memory.
  have m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, k2.2.1, m1]
  have hmem : s12.mem = (((s.mem.writeW (W + BitVec.ofNat 64 o) (s6.gpr .a1)).writeW
      (W + BitVec.ofNat 64 o + BitVec.ofNat 64 (8 * 1)) (s8.gpr .t3)).writeW
      (W + BitVec.ofNat 64 o + BitVec.ofNat 64 (8 * 2)) (s10.gpr .t4)).writeW
      (W + BitVec.ofNat 64 o + BitVec.ofNat 64 (8 * 3)) (s12.gpr .t5) := by
    rw [m12, mm11, m10, mm9, m8, mm7, m6, mm5, m4]
  have hrest : ∀ r, r ∉ clobM → s12.gpr r = s.gpr r := fun r hr => by
    have n : ∀ x ∈ [Reg.a1, .t3, .t6, .a4, .a5, .a6, .a7, .t0, .a2, .a0, .t4, .t5], x ∈ clobM := by decide
    have h' : ∀ x, x ∈ [Reg.a1, .t3, .t6, .a4, .a5, .a6, .a7, .t0, .a2, .a0, .t4, .t5] → r ≠ x := fun x hx e =>
      hr (e ▸ n x hx)
    have kk : r ∉ [Reg.t6, .a0, .a4] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h' _ (by simp), h' _ (by simp), h' _ (by simp)⟩
    rw [k12.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨h' _ (by simp), h' _ (by simp), h' _ (by simp)⟩),
      g11.1 r kk,
      k10.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨h' _ (by simp), h' _ (by simp), h' _ (by simp)⟩),
      g9.1 r kk,
      k8.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨h' _ (by simp), h' _ (by simp), h' _ (by simp)⟩),
      g7.1 r kk,
      k6.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨h' _ (by simp), h' _ (by simp)⟩),
      g5.1 r kk, u4.other _ (h' _ (by simp)), u3.other _ (h' _ (by simp)),
      k2.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨h' _ (by simp), h' _ (by simp), h' _ (by simp), h' _ (by simp), h' _ (by simp), h' _ (by simp),
          h' _ (by simp)⟩),
      r1.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨h' _ (by simp), h' _ (by simp), h' _ (by simp), h' _ (by simp), h' _ (by simp), h' _ (by simp),
          h' _ (by simp), h' _ (by simp)⟩)]
  refine ⟨?_, ?_, hrest, ?_, ?_, ?_⟩
  · rw [hmem, d4_add]
    simp only [Nat.mul_one, Nat.reduceMul, off_add, VG.Proof.X25519.RISCV64.R64.val4, Nat.mul_zero,
      Nat.add_zero]
    rw [dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_other _ _ _ (by omega) (by omega) (by omega),
      dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_self,
      dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_other _ _ _ (by omega) (by omega) (by omega),
      dw_write_self, dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_self, dw_write_self]
    exact sub_final hM hA hB (by rw [← vA, ← vB]; exact e2) c2 (BitVec.isLt _) (BitVec.isLt _)
      (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
      n0 n1 n2 n3 e6 e8 e10 e12
  · rw [hmem]
    have cc : ∀ k < 4, (⟨W + BitVec.ofNat 64 o, 32⟩ : Region).Contains
        (W + BitVec.ofNat 64 o + BitVec.ofNat 64 (8 * k)) 8 := fun k hk => out_contains _ hk
    have c0 := cc 0 (by decide)
    simp only [Nat.mul_zero] at c0
    rw [show W + BitVec.ofNat 64 o + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 o by simp] at c0
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW
      (List.mem_singleton_self _) _ (cc 1 (by decide))).writeW (List.mem_singleton_self _) _
      (cc 2 (by decide))).writeW (List.mem_singleton_self _) _ (cc 3 (by decide))
  · rw [k12.2.1, g11.2.1, k10.2.1, g9.2.1, k8.2.1, g7.2.1, k6.2.1, g5.2.1, u4.rd, u3.rd,
      k2.2.2.1, r1.rd]
  · rw [k12.2.2.1, g11.2.2.1, k10.2.2.1, g9.2.2.1, k8.2.2.1, g7.2.2.1, k6.2.2.1, g5.2.2.1, wr4]
  · rw [k12.2.2.2, g11.2.2.2, k10.2.2.2, g9.2.2.2, k8.2.2.2, g7.2.2.2, k6.2.2.2, g5.2.2.2, u4.sp, u3.sp,
      k2.2.2.2.2, r1.sp]

/-! `p`'s words under the mask. -/

theorem kP0 : KOk [.addi .t6 .t0 0] (2 ^ 64 - 1) := fun s β hb ht => by
  refine wp_mv fun s1 u1 => WP.block_nil ⟨?_, ⟨fun r hr => u1.other _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.1), u1.rd, u1.wr, u1.sp⟩,
    u1.mem⟩
  rw [u1.gpr, ht]; exact (pmask hb).1

theorem kP1 : KOk [.shift .srl .d .t6 .t0 32] (2 ^ 32 - 1) := fun s β hb ht => by
  refine wp_srl (by decide) fun s1 u1 => WP.block_nil ⟨?_, ⟨fun r hr => u1.other _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.1), u1.rd,
    u1.wr, u1.sp⟩, u1.mem⟩
  rw [u1.gpr, ht]; exact (pmask hb).2.1

theorem kP2 : KOk [.li .t6 0] 0 := fun s β hb ht => by
  refine wp_li (imm := 0) (by decide) fun s1 u1 => WP.block_nil ⟨?_, ⟨fun r hr => u1.other _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.1),
    u1.rd, u1.wr, u1.sp⟩, u1.mem⟩
  rw [u1.gpr]; split <;> rfl

theorem kP3 : KOk [.shift .sll .d .t6 .t0 32, .shift .srl .d .a4 .t0 63, .logic .or .t6 .t6 .a4]
    (2 ^ 64 - 2 ^ 32 + 1) := fun s β hb ht => by
  refine wp_sll (by decide) fun s1 u1 => wp_srl (by decide) fun s2 u2 => wp_or fun s3 u3 => WP.block_nil
    ⟨?_, ⟨fun r hr => ?_, by rw [u3.rd, u2.rd, u1.rd], by rw [u3.wr, u2.wr, u1.wr], by rw [u3.sp, u2.sp, u1.sp]⟩,
      by rw [u3.mem, u2.mem, u1.mem]⟩
  · rw [u3.gpr, u2.other _ (by decide), u2.gpr, u1.gpr, u1.other _ (by decide), ht]; exact (pmask hb).2.2
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u3.other _ hr.1, u2.other _ hr.2.2, u1.other _ hr.1]

/-- `subCore`: `[t2] = ([t4] - [t5]) mod p`, for operands below `p`. -/
theorem subCore_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 32 ≤ 8192) (hb : bb + 32 ≤ 8192) (ho : o + 32 ≤ 8192)
    (hA : d4 s.mem (W + BitVec.ofNat 64 a) < P) (hB : d4 s.mem (W + BitVec.ofNat 64 bb) < P) :
    WP isa (.block subCore) s fun s' =>
      d4 s'.mem (W + BitVec.ofNat 64 o) =
        (d4 s.mem (W + BitVec.ofNat 64 a) + P - d4 s.mem (W + BitVec.ofNat 64 bb)) % P ∧
      Frame [⟨W + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  subWith_ok (by unfold P; omega) (by decide) (by decide) (by decide) (by decide) kP0 kP1 kP2 kP3
    hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hA hB

end VG.Proof.Weierstrass.RISCV64.P256Field

/-!
## P-256's field on RISC-V: operands at offsets not multiples of 8

The byte-wise copies of `fn`'s other branch (`Impl/Weierstrass/RISCV64/P256Field.lean`):
the operands into `SA` and `SB` of the own working space, the pointers to
them and to `SO` (`slowIn_ok`), and the result from `SO` to `[o]`
(`slowOut_ok`), each copy as Ed25519's (`unpackField_ok`, `packField_ok`),
whose words are the four doublewords (`V_d4`).
-/

namespace VG.Proof.Weierstrass.RISCV64.P256Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Proof.X25519.RISCV64 (Ctx Rest V limb wd wd_shift wd_frame in_base)
open VG.Proof.Ed25519.RISCV64 (unpackField_ok packField_ok PackInv)

/-- The number of the words at `q`, read 32 bits at a time, is its four doublewords. -/
theorem V_zero (m : Mem) (q : Addr) : V m q 0 = d4 m q := by
  rw [V_d4]; simp

/-- `unpackField p o 0` of the operand at `W + x` into `W + 2048 + o`. -/
theorem unpack_ok {W : Addr} {s : State} (hw : WsAt W s) {p : Reg} (hp : p ∉ [Reg.a4, .a5]) {x : Nat}
    (h : s.gpr p = W + BitVec.ofNat 64 x) (hx : x + 32 ≤ 3840) {o : Nat} (ho : 1952 ≤ o) (ho' : o + 32 ≤ 2048)
    (ho4 : o % 4 = 0) :
    WP isa (.block (VG.Impl.Ed25519.RISCV64.unpackField p o 0)) s fun t =>
      Rest [.a4, .a5] s t ∧ Frame [⟨W + BitVec.ofNat 64 (2048 + o), 32⟩] s.mem t.mem ∧
      d4 t.mem (W + BitVec.ofNat 64 (2048 + o)) = d4 s.mem (W + BitVec.ofNat 64 x) := by
  refine WP.mono (unpackField_ok hw.ctx hp h (o := o) (src := 0) ho' ho4 (by decide)
    (fun k hk => by
      rw [Nat.zero_add, off_add]
      obtain ⟨r, hr, hc⟩ := in_base (n := 4) hw.wr (d := x + 4 * k) (by omega) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [off_add, Nat.add_zero, off_add]; exact Offset.disjoint W (by omega) (by omega) (by omega)))
    fun t ⟨r, f, v⟩ => ⟨r, by rw [off_add] at f; exact f, ?_⟩
  rw [← off_add, ← V_d4, ← V_zero]
  unfold V
  exact VG.Proof.X25519.val32_congr fun k hk => by rw [v k hk, limb]

/-- The slow branch's copies in, and its pointers. -/
theorem slowIn_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha : a + 32 ≤ 3840) (hb : bb + 32 ≤ 3840) :
    WP isa (.block (([.addi .t1 .t2 0] : List Instr) ++ VG.Impl.Ed25519.RISCV64.unpackField .t4 SA 0 ++
        VG.Impl.Ed25519.RISCV64.unpackField .t5 SB 0 ++ ([.addi .t4 .a3 SA, .addi .t5 .a3 SB, .addi .t2 .a3 SO] : List Instr))) s
      fun t => WsAt W t ∧ t.gpr .t1 = W + BitVec.ofNat 64 o ∧ t.gpr .t4 = W + BitVec.ofNat 64 4000 ∧
        t.gpr .t5 = W + BitVec.ofNat 64 4032 ∧ t.gpr .t2 = W + BitVec.ofNat 64 4064 ∧
        d4 t.mem (W + BitVec.ofNat 64 4000) = d4 s.mem (W + BitVec.ofNat 64 a) ∧
        d4 t.mem (W + BitVec.ofNat 64 4032) = d4 s.mem (W + BitVec.ofNat 64 bb) ∧
        Frame [⟨W + BitVec.ofNat 64 4000, 32⟩, ⟨W + BitVec.ofNat 64 4032, 32⟩] s.mem t.mem ∧
        Rest [.t1, .t2, .t4, .t5, .a4, .a5] s t := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mv fun s1 u1 => ?_
  have hw1 : WsAt W s1 := hw.of_rest (u1.rest (ws := [.t1]) (by decide)) (by decide)
  refine WP.block_append (WP.mono (unpack_ok hw1 (p := .t4) (by decide) (by rw [u1.other _ (by decide), h4]) ha
    (o := SA) (by decide) (by decide) (by decide)) fun s2 ⟨r2, f2, v2⟩ => ?_)
  have hw2 : WsAt W s2 := hw1.of_rest r2 (by decide)
  refine WP.block_append (WP.mono (unpack_ok hw2 (p := .t5) (by decide)
    (by rw [r2.gpr _ (by decide), u1.other _ (by decide), h5]) hb (o := SB) (by decide) (by decide) (by decide))
    fun s3 ⟨r3, f3, v3⟩ => ?_)
  have hw3 : WsAt W s3 := hw2.of_rest r3 (by decide)
  refine wp_addi (by decide) fun s4 u4 => wp_addi (by decide) fun s5 u5 => wp_addi (by decide) fun s6 u6 =>
    WP.block_nil ?_
  have a3 : ∀ t : State, WsAt W t → t.gpr .a3 = W + BitVec.ofNat 64 2048 := fun t h => h.a3
  have r6 : Rest [.t1, .t2, .t4, .t5, .a4, .a5] s s6 :=
    (u1.rest (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  have m6 : s6.mem = s3.mem := by rw [u6.mem, u5.mem, u4.mem]
  have f2' := f2
  rw [show 2048 + SA = 4000 from rfl] at f2' v2
  rw [show 2048 + SB = 4032 from rfl] at f3 v3
  refine ⟨hw.of_rest r6 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, r6⟩
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r3.gpr _ (by decide),
      r2.gpr _ (by decide), u1.gpr, h2]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, a3 s3 hw3, off_add]; rfl
  · rw [u6.other _ (by decide), u5.gpr, u4.other _ (by decide), a3 s3 hw3, off_add]; rfl
  · rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), a3 s3 hw3, off_add]; rfl
  · rw [m6, d4_frame f3 (by omega) (by omega) (by omega), v2, u1.mem]
  · rw [m6, v3, d4_frame f2' (by omega) (by omega) (by omega), u1.mem]
  · rw [m6, ← u1.mem]
    exact (f2'.mono (by simp)).trans (f3.mono (by simp))

/-- The slow branch's copy out: `[o]` from `SO`. -/
theorem slowOut_ok {W : Addr} {s : State} (hw : WsAt W s) {o : Nat}
    (h1 : s.gpr .t1 = W + BitVec.ofNat 64 o) (ho : o + 32 ≤ 3840) :
    WP isa (.block (VG.Impl.Ed25519.RISCV64.packField .t1 SO 0)) s fun t =>
      Rest [.a4, .a5] s t ∧ Frame [⟨W + BitVec.ofNat 64 o, 32⟩] s.mem t.mem ∧
      d4 t.mem (W + BitVec.ofNat 64 o) = d4 s.mem (W + BitVec.ofNat 64 4064) := by
  refine WP.mono (packField_ok hw.ctx (p := .t1) (by decide) h1 (a := SO) (dst := 0) (by decide) (by decide)
    (by decide) (fun k hk => by
      rw [Nat.zero_add, off_add]
      exact in_base (n := 4) hw.wr (by omega) (by omega))
    (by
      rw [off_add, Nat.add_zero, off_add]
      exact Offset.disjoint W (d := o) (n := 32) (e := 2048 + SO) (k := 32) (by unfold SO; omega) (by omega)
        (by unfold SO; omega)))
    fun t ht => ⟨ht.rest, ?_, ?_⟩
  · have f := ht.frame
    rw [off_add, Nat.add_zero] at f
    exact f
  · rw [← V_zero, show (4064 : Nat) = 2048 + SO from rfl, ← off_add, ← V_d4]
    unfold V
    exact VG.Proof.X25519.val32_congr fun k hk => by rw [limb, ht.outs k hk]

end VG.Proof.Weierstrass.RISCV64.P256Field

namespace VG.Proof.Weierstrass.RISCV64.P256Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Proof.X25519.RISCV64 (Ctx Rest)
open VG.Proof.X448.RISCV64.R64 (al8)

/-- What an operation on the pointers `t4`, `t5` and `t2` does, for operands
satisfying `pre`: its result `res` of the operands, written at `[t2]`. -/
def CoreOk (core : Prog isa) (pre : Nat → Nat → Prop) (res : Nat → Nat → Nat → Prop) : Prop :=
  ∀ {W : Addr} {s : State} {a bb o : Nat}, WsAt W s → s.gpr .t4 = W + BitVec.ofNat 64 a →
    s.gpr .t5 = W + BitVec.ofNat 64 bb → s.gpr .t2 = W + BitVec.ofNat 64 o → a % 8 = 0 → bb % 8 = 0 →
    o % 8 = 0 → a + 32 ≤ 8192 → bb + 32 ≤ 8192 → o + 32 ≤ 8192 → Apart bb →
    pre (d4 s.mem (W + BitVec.ofNat 64 a)) (d4 s.mem (W + BitVec.ofNat 64 bb)) →
    WP isa core s fun s' =>
      res (d4 s.mem (W + BitVec.ofNat 64 a)) (d4 s.mem (W + BitVec.ofNat 64 bb)) (d4 s'.mem (W + BitVec.ofNat 64 o)) ∧
      Frame (mulW W o) s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

/-- Montgomery's product modulo `p`. -/
abbrev mulRes (A B r : Nat) : Prop := r < P ∧ r * 2 ^ 256 % P = A * B % P

theorem mulCore_core : CoreOk mulCore (fun _ B => B < P) mulRes :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB =>
    WP.mono (mulCore_ok hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB) fun _ ⟨v1, v2, f, g, rd, wr, sp⟩ =>
      ⟨⟨v1, v2⟩, f, g, rd, wr, sp⟩

theorem addCore_core : CoreOk (.block addCore) (fun A B => A + B < 2 * P) (fun A B r => r = (A + B) % P) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho _ hAB =>
    WP.mono (addCore_ok hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hAB) fun _ ⟨v, f, g, rd, wr, sp⟩ =>
      ⟨v, f.mono (by simp), g, rd, wr, sp⟩

theorem subCore_core : CoreOk (.block subCore) (fun A B => A < P ∧ B < P) (fun A B r => r = (A + P - B) % P) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho _ hAB =>
    WP.mono (subCore_ok hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hAB.1 hAB.2) fun _ ⟨v, f, g, rd, wr, sp⟩ =>
      ⟨v, f.mono (by simp), g, rd, wr, sp⟩

/-! ## The entry -/

/-- An offset argument: the low word of its register. -/
abbrev lo (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- A pointer `W + x` is a multiple of 8 if and only if `x` is, for `W` one and no wrap around. -/
theorem ptr_mod8 {W : Addr} (hW : W.toNat % 8 = 0) {x : Nat} (hx : W.toNat + x < 2 ^ 64) :
    (W + BitVec.ofNat 64 x).toNat % 8 = x % 8 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), Nat.mod_eq_of_lt hx]
  omega

/-- The low three bits of an `or` are zero only if each operand's are. -/
theorem aligned_of {x y z : BitVec 64} (h : (x ||| y ||| z) &&& BitVec.ofInt 64 7 = 0) :
    x.toNat % 8 = 0 ∧ y.toNat % 8 = 0 ∧ z.toNat % 8 = 0 := by
  have e : ∀ v : BitVec 64, (v &&& BitVec.ofInt 64 7).toNat = v.toNat % 8 := fun v => by
    rw [BitVec.toNat_and, show (BitVec.ofInt 64 7).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.and_or_distrib_right, BitVec.and_or_distrib_right] at h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_or, BitVec.toNat_or, e, e, e] at h1
  rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at h1
  have h2 := Nat.or_eq_zero_iff.mp h1
  have h3 := Nat.or_eq_zero_iff.mp h2.1
  exact ⟨h3.1, h3.2, h2.2⟩

/-- What the pointers' block leaves, after the zero-extension from `σ`. -/
theorem ptrs_ok {W : Addr} {σ s : State} (hz : VG.Proof.Ed25519.RISCV64.zextF σ s) (h0 : σ.gpr .a0 = W) :
    WP isa (.block ptrs) s fun t =>
      t.gpr .t2 = W + BitVec.ofNat 64 (lo σ .a1) ∧ t.gpr .t4 = W + BitVec.ofNat 64 (lo σ .a2) ∧
      t.gpr .t5 = W + BitVec.ofNat 64 (lo σ .a3) ∧ t.gpr .a3 = W + BitVec.ofNat 64 2048 ∧
      t.gpr .t0 = ((W + BitVec.ofNat 64 (lo σ .a1)) ||| (W + BitVec.ofNat 64 (lo σ .a2)) |||
        (W + BitVec.ofNat 64 (lo σ .a3))) &&& BitVec.ofInt 64 7 ∧
      Rest [.a3, .t0, .t2, .t4, .t5] s t ∧ t.mem = s.mem := by
  obtain ⟨-, e0, ek⟩ := hz
  have e1 := ek .a1 (by simp)
  have e2 := ek .a2 (by simp)
  have e3 := ek .a3 (by simp)
  rw [h0] at e0
  simp only [ptrs]
  refine wp_add fun s7 u7 => wp_add fun s8 u8 => wp_add fun s9 u9 => wp_addi (by decide) fun s10 u10 =>
    wp_addi (by decide) fun s11 u11 => wp_or fun s12 u12 => wp_or fun s13 u13 =>
    wp_andi (by decide) fun s14 u14 => WP.block_nil ?_
  have p2 : s9.gpr .t2 = W + BitVec.ofNat 64 (lo σ .a1) := by
    rw [u9.other _ (by decide), u8.other _ (by decide), u7.gpr, e0, e1]
  have p4 : s9.gpr .t4 = W + BitVec.ofNat 64 (lo σ .a2) := by
    rw [u9.other _ (by decide), u8.gpr, u7.other _ (by decide), u7.other .a2 (by decide), e0, e2]
  have p5 : s9.gpr .t5 = W + BitVec.ofNat 64 (lo σ .a3) := by
    rw [u9.gpr, u8.other _ (by decide), u8.other .a3 (by decide), u7.other _ (by decide),
      u7.other .a3 (by decide), e0, e3]
  have g14 : ∀ r, r ≠ .t0 → r ≠ .a3 → s14.gpr r = s9.gpr r := fun r h0 h3 => by
    rw [u14.other _ h0, u13.other _ h0, u12.other _ h0, u11.other _ h3, u10.other _ h3]
  refine ⟨by rw [g14 _ (by decide) (by decide), p2], by rw [g14 _ (by decide) (by decide), p4],
    by rw [g14 _ (by decide) (by decide), p5], ?_, ?_, ?_, ?_⟩
  · rw [u14.other _ (by decide), u13.other _ (by decide), u12.other _ (by decide), u11.gpr, u10.gpr,
      u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), e0, BitVec.add_assoc]
    rfl
  · rw [u14.gpr, u13.gpr, u12.gpr, u12.other .t5 (by decide)]
    rw [u11.other .t2 (by decide), u11.other .t4 (by decide), u11.other .t5 (by decide), u10.other .t2 (by decide),
      u10.other .t4 (by decide), u10.other .t5 (by decide), p2, p4, p5]
  · exact (u7.rest (by decide)).trans ((u8.rest (by decide)).trans ((u9.rest (by decide)).trans
      ((u10.rest (by decide)).trans ((u11.rest (by decide)).trans ((u12.rest (by decide)).trans
      ((u13.rest (by decide)).trans (u14.rest (by decide))))))))
  · rw [u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem]

/-- The zero-extension, with what it keeps. -/
theorem zext_ok (σ : State) : WP isa (.block zext) σ fun t =>
    VG.Proof.Ed25519.RISCV64.zextF σ t ∧ Rest [.a1, .a2, .a3] σ t ∧ t.mem = σ.mem := by
  unfold zext Impl.Ed25519.RISCV64.mulZext
  refine wp_sll (by decide) fun s1 u1 => wp_srl (by decide) fun s2 u2 => wp_sll (by decide) fun s3 u3 =>
    wp_srl (by decide) fun s4 u4 => wp_sll (by decide) fun s5 u5 => wp_srl (by decide) fun s6 u6 =>
    WP.block_nil ?_
  have h0 : s6.gpr .a0 = σ.gpr .a0 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide)]
  have hk : ∀ r ∈ [Reg.a1, .a2, .a3], s6.gpr r = BitVec.ofNat 64 ((σ.gpr r).setWidth 32).toNat := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
        u2.gpr, u1.gpr, Ed25519.RISCV64.zext_shifts]
    · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.gpr, u2.other _ (by decide),
        u1.other _ (by decide), Ed25519.RISCV64.zext_shifts]
    · rw [u6.gpr, u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
        u1.other _ (by decide), Ed25519.RISCV64.zext_shifts]
  have hr : Rest [.a1, .a2, .a3] σ s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  exact ⟨⟨by rw [u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp], h0, hk⟩, hr,
    by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]⟩

/-- The registers the functions write. -/
abbrev clobF : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-- The regions the functions write: their own working space and the result. -/
abbrev fnW (W : Addr) (o : Nat) : List Region := [⟨W + BitVec.ofNat 64 3840, 256⟩, ⟨W + BitVec.ofNat 64 o, 32⟩]

theorem mulW_fnW (W : Addr) (o : Nat) {m m' : Mem} (h : Frame (mulW W o) m m') : Frame (fnW W o) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩

/-- `fn core`, from the working space at `W` and offsets below its own working space. -/
theorem fn_ok {core : Prog isa} {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop}
    (hcore : CoreOk core pre res) {W : Addr} {s : State} (h0 : s.gpr .a0 = W) (hal : W.toNat % 8 = 0)
    (hwr : (⟨W, 8192⟩ : Region) ∈ s.wr) (hfit : W.toNat + 8192 ≤ 2 ^ 64)
    (ho : lo s .a1 + 32 ≤ 3840) (ha : lo s .a2 + 32 ≤ 3840) (hb : lo s .a3 + 32 ≤ 3840)
    (hpre : pre (d4 s.mem (W + BitVec.ofNat 64 (lo s .a2))) (d4 s.mem (W + BitVec.ofNat 64 (lo s .a3)))) :
    WP isa (fn core) s fun s' =>
      res (d4 s.mem (W + BitVec.ofNat 64 (lo s .a2))) (d4 s.mem (W + BitVec.ofNat 64 (lo s .a3)))
        (d4 s'.mem (W + BitVec.ofNat 64 (lo s .a1))) ∧
      Frame (fnW W (lo s .a1)) s.mem s'.mem ∧ (∀ r, r ∉ clobF → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold fn
  refine WP.seq (WP.mono (zext_ok s) fun s0 ⟨z0, r0, m0⟩ => ?_)
  refine WP.seq (WP.mono (ptrs_ok z0 h0) fun s1 ⟨p2, p4, p5, p3, p0, r1', m1'⟩ => ?_)
  have r1 : Rest [.a1, .a2, .a3, .t0, .t2, .t4, .t5] s s1 := (r0.mono (by decide)).trans (r1'.mono (by decide))
  have m1 : s1.mem = s.mem := by rw [m1', m0]
  have hw1 : WsAt W s1 := ⟨hal, by rw [r1.wr]; exact hwr, hfit, p3⟩
  have sub1 : ∀ x ∈ [Reg.a1, .a2, .a3, .t0, .t2, .t4, .t5], x ∈ clobF := by decide
  have subM : ∀ x ∈ clobM, x ∈ clobF := by decide
  refine WP.ite (s1.gpr .t0 == 0) rfl (fun hz => ?_) (fun _ => ?_)
  · -- The offsets are multiples of 8.
    rw [p0] at hz
    obtain ⟨al1, al2, al3⟩ := aligned_of (beq_iff_eq.mp hz)
    rw [ptr_mod8 hal (by omega)] at al1 al2 al3
    refine WP.mono (hcore hw1 p4 p5 p2 al2 al3 al1 (by omega) (by omega) (by omega) (.inl (by omega))
      (by rw [m1]; exact hpre)) fun s2 ⟨v2, f2, g2, rd2, wr2, sp2⟩ => ⟨by rw [← m1]; exact v2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← m1]; exact mulW_fnW W _ f2
    · intro r hr
      rw [g2 r (fun h => hr (subM r h)), r1.gpr r (fun h => hr (sub1 r h))]
    · rw [rd2, r1.rd]
    · rw [wr2, r1.wr]
    · rw [sp2, r1.sp]
  · -- The byte-wise copies.
    refine WP.seq (WP.mono (slowIn_ok hw1 p4 p5 p2 ha hb) fun s2 ⟨hw2, q1, q4, q5, q2, v4, v5, f2, r2⟩ => ?_)
    refine WP.seq (WP.mono (hcore hw2 q4 q5 q2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (.inr (by decide)) (by rw [v4, v5, m1]; exact hpre)) fun s3 ⟨v3, f3, g3, rd3, wr3, sp3⟩ => ?_)
    have hw3 : WsAt W s3 := ⟨hal, by rw [wr3]; exact hw2.wr, hfit, by rw [g3 _ (by decide), hw2.a3]⟩
    refine WP.mono (slowOut_ok hw3 (by rw [g3 _ (by decide), q1]) ho) fun s4 ⟨r4, f4, v4'⟩ =>
      ⟨by rw [v4']; rw [v4, v5, m1] at v3; exact v3, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← m1]
      refine (f2.sub fun r hr => ?_).trans ((f3.sub fun r hr => ?_).trans (f4.sub fun r hr => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
      · rw [List.mem_singleton.mp hr]
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    · intro r hr
      have s2' : ∀ x ∈ [Reg.t1, .t2, .t4, .t5, .a4, .a5], x ∈ clobF := by decide
      have s4' : ∀ x ∈ [Reg.a4, .a5], x ∈ clobF := by decide
      rw [r4.gpr r (fun h => hr (s4' r h)), g3 r (fun h => hr (subM r h)), r2.gpr r (fun h => hr (s2' r h)),
        r1.gpr r (fun h => hr (sub1 r h))]
    · rw [r4.rd, rd3, r2.rd, r1.rd]
    · rw [r4.wr, wr3, r2.wr, r1.wr]
    · rw [r4.sp, sp3, r2.sp, r1.sp]

end VG.Proof.Weierstrass.RISCV64.P256Field
