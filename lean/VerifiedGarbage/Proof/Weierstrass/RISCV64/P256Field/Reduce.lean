module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.X448.RISCV64.R64.Product
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-256's field on RISC-V: Montgomery's reduction

`reduce` (`Impl/Weierstrass/RISCV64/P256Field.lean`) reduces the eight words
`T` at `ACC`: after round `i`, the registers `rw i`–`rw (i + 3)`, the carry
`a2` and the words of `T` from `i + 4` on, as a number `wv i` (`RedInv`), are
`(T + Q p) / 2^(64 i)` for some `Q < 2^(64 i)` (`round_ok`: a round adds
`q p` for the low word `q`, which `p ≡ -1 (mod 2⁶⁴)` makes the next quotient
word), so the four rounds leave `X` with `X 2²⁵⁶ = T + Q p` (`reduce_ok`).
-/

@[expose] public section

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
    WP isa (.block ((List.range 4).map (fun j => .load .d (rw j) .a3 (ACC + 8 * j)) ++ [.li .a2 0])) s
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
