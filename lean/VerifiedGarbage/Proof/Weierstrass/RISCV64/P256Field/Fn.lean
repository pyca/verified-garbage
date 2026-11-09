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
import VerifiedGarbage.Proof.X448.RISCV64.R64.Macc

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
and `t2` (`mulCore_ok`): `fused` leaves `X` with `X 2²⁵⁶ = [t5] [t4] + Q p`
(`fused_ok`), which `csub`
reduces and stores at `[t2]` (`csub_ok`): Montgomery's product modulo `p`.
-/

/-!
## Montgomery's reduction of a product at `ACC`

The invariant of the rounds of the reductions of the four-word moduli whose
product is at `ACC` (P-256's order's, `Proof/Weierstrass/RISCV64/P256Order/Fn.lean`,
and `Proof/Weierstrass/RISCV64/Gen4.lean`'s): after round `i`, the registers
`rw i`–`rw (i + 3)`, the carry `a2` and the words of the product `T` from
`i + 4` on, as a number `wv i`, are `(T + Q m) / 2^(64 i)` for some
`Q < 2^(64 i)`. The initial loads start it (`loads_ok`, here with `p`:
`RedInv`), which those modules restate with their moduli.
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

/-!
## P-256's field on RISC-V: the product reduced as it is computed

The terms of `fused` (`Impl/Weierstrass/RISCV64/P256Field.lean`): a product
of words (`prodW_ok`), `q 2³²` (`qShift_ok`) and `q (2⁶⁴ - 2³² + 1)`
(`qMul_ok`), each two words `x + 2⁶⁴ y` with `y < 2⁶⁴ - 1`, added into a
column's words (`acc3_ok`, `accF_ok`, `acc1_ok`); the columns (`col01_ok`
to `col56_ok`), whose sums make `X 2²⁵⁶ = [t5] [t4] + Q p` (`cols_sum`,
`fused_ok`).
-/

namespace VG.Proof.Weierstrass.RISCV64.P256Field

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Proof.X448.RISCV64.R64 (dw dw_lt al8)

variable {s : State}

/-- The two words `x + 2⁶⁴ y` in `s`. -/
abbrev val2 (s : State) (x y : Reg) : Nat := (s.gpr x).toNat + 2 ^ 64 * (s.gpr y).toNat

set_option linter.unusedSimpArgs false in
theorem prodW_ok {x y a b : Reg} (hya : y ≠ a := by decide) (hyb : y ≠ b := by decide)
    (hxy : x ≠ y := by decide) :
    WP isa (.block (prodW x y a b)) s fun s' =>
      val2 s' x y = (s.gpr a).toNat * (s.gpr b).toNat ∧ (s'.gpr y).toNat < 2 ^ 64 - 1 ∧
      Keeps [x, y] s s' := by
  apply WP.of_runBlock
  simp only [prodW, val2, runBlock_cons, runStep_some, runBlock_nil, exec_mul, exec_mulhu,
    RegUpd.gpr_write, Ne.symm hya, Ne.symm hyb, hxy, Ne.symm hxy, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨mul_words _ _, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := VG.Proof.X448.RISCV64.R64.mulhi_lt (s.gpr a) (s.gpr b); omega)]
    exact VG.Proof.X448.RISCV64.R64.mulhi_lt _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

set_option linter.unusedSimpArgs false in
theorem qShift_ok {x y q : Reg} (hxq : x ≠ q := by decide) (hxy : x ≠ y := by decide) :
    WP isa (.block (qShift x y q)) s fun s' =>
      val2 s' x y = (s.gpr q).toNat * 2 ^ 32 ∧ (s'.gpr y).toNat < 2 ^ 64 - 1 ∧
      Keeps [x, y] s s' := by
  apply WP.of_runBlock
  simp only [qShift, val2, runBlock_cons, runStep_some, runBlock_nil, exec_shift_d (show 32 < 64 by decide),
    RegUpd.gpr_write, Ne.symm hxq, hxq, hxy, Ne.symm hxy, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    have := (s.gpr q).isLt
    omega
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := (s.gpr q).isLt
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- `q (2⁶⁴ - 2³² + 1)` as `qMul` computes it. -/
theorem qMul_words (q : BitVec 64) :
    (q - q <<< 32).toNat + 2 ^ 64 * ((q - if q < q <<< 32 then (1 : BitVec 64) else 0) - q >>> 32).toNat =
      q.toNat * (2 ^ 64 - 2 ^ 32 + 1) ∧
    ((q - if q < q <<< 32 then (1 : BitVec 64) else 0) - q >>> 32).toNat < 2 ^ 64 - 1 := by
  have hq := q.isLt
  have hl : (q <<< 32).toNat = q.toNat * 2 ^ 32 % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hh : (q >>> 32).toNat = q.toNat / 2 ^ 32 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases hb : q < q <<< 32
  · have hb' : q.toNat < q.toNat * 2 ^ 32 % 2 ^ 64 := by rw [← hl]; exact hb
    simp only [hb, ↓reduceIte]
    rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_sub, hl, hh,
      show (1 : BitVec 64).toNat = 1 from rfl]
    have hd : q.toNat * 2 ^ 32 % 2 ^ 64 + 2 ^ 64 * (q.toNat / 2 ^ 32) = q.toNat * 2 ^ 32 := by omega
    have hh' : q.toNat / 2 ^ 32 < 2 ^ 32 := by omega
    generalize q.toNat * 2 ^ 32 % 2 ^ 64 = lo at *
    generalize q.toNat / 2 ^ 32 = hi at *
    generalize q.toNat = n at *
    have hn : hi + 1 ≤ n := by omega
    rw [show (2 ^ 64 - 1 + n) % 2 ^ 64 = n - 1 by omega,
      show (2 ^ 64 - lo + n) % 2 ^ 64 = 2 ^ 64 - lo + n by omega,
      show (2 ^ 64 - hi + (n - 1)) % 2 ^ 64 = n - 1 - hi by omega]
    constructor <;> omega
  · have hb' : ¬ q.toNat < q.toNat * 2 ^ 32 % 2 ^ 64 := by rw [← hl]; exact hb
    simp only [hb, ↓reduceIte]
    rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_sub, hl, hh,
      show (0 : BitVec 64).toNat = 0 from rfl]
    have hd : q.toNat * 2 ^ 32 % 2 ^ 64 + 2 ^ 64 * (q.toNat / 2 ^ 32) = q.toNat * 2 ^ 32 := by omega
    have hh' : q.toNat / 2 ^ 32 < 2 ^ 32 := by omega
    generalize q.toNat * 2 ^ 32 % 2 ^ 64 = lo at *
    generalize q.toNat / 2 ^ 32 = hi at *
    generalize q.toNat = n at *
    have hn : hi ≤ n := by omega
    rw [show (2 ^ 64 - 0 + n) % 2 ^ 64 = n by omega,
      show (2 ^ 64 - lo + n) % 2 ^ 64 = n - lo by omega,
      show (2 ^ 64 - hi + n) % 2 ^ 64 = n - hi by omega]
    constructor <;> omega

set_option linter.unusedSimpArgs false in
theorem qMul_ok {x y q : Reg} (hxq : x ≠ q := by decide) (hxy : x ≠ y := by decide)
    (hyq : y ≠ q := by decide) :
    WP isa (.block (qMul x y q)) s fun s' =>
      val2 s' x y = (s.gpr q).toNat * (2 ^ 64 - 2 ^ 32 + 1) ∧ (s'.gpr y).toNat < 2 ^ 64 - 1 ∧
      Keeps [x, y, q] s s' := by
  apply WP.of_runBlock
  simp only [qMul, val2, runBlock_cons, runStep_some, runBlock_nil, exec_shift_d (show 32 < 64 by decide),
    exec_sltu, exec_sub, RegUpd.gpr_write, Ne.symm hxq, hxq, hxy, Ne.symm hxy, hyq, Ne.symm hyq,
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have h := (qMul_words (s.gpr q)).1
    exact h
  · exact (qMul_words _).2
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

set_option linter.unusedSimpArgs false in
/-- `r₀ + 2⁶⁴ r₁ + 2¹²⁸ r₂ += x + 2⁶⁴ y`, for `y < 2⁶⁴ - 1`. -/
theorem acc3_ok {r0 r1 r2 x y : Reg} (h01 : r0 ≠ r1 := by decide) (h02 : r0 ≠ r2 := by decide)
    (h12 : r1 ≠ r2 := by decide) (h0x : r0 ≠ x := by decide) (h0y : r0 ≠ y := by decide)
    (h1x : r1 ≠ x := by decide) (h1y : r1 ≠ y := by decide) (h2x : r2 ≠ x := by decide)
    (h2y : r2 ≠ y := by decide) (hxy : x ≠ y := by decide) :
    WP isa (.block (acc3 r0 r1 r2 x y)) s fun s' =>
      ((s.gpr y).toNat < 2 ^ 64 - 1 →
        val3 s' r0 r1 r2 = (val3 s r0 r1 r2 + val2 s x y) % 2 ^ 192) ∧
      Keeps [r0, r1, r2, x, y] s s' := by
  apply WP.of_runBlock
  simp only [acc3, val3, val2, runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, h01, h02, h12, h0x, h0y, h1x, h1y, h2x, h2y, hxy, Ne.symm h01, Ne.symm h02,
    Ne.symm h12, Ne.symm h0x, Ne.symm h0y, Ne.symm h1x, Ne.symm h1y, Ne.symm h2x, Ne.symm h2y,
    Ne.symm hxy, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fun hb => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have c₀ := carry (s.gpr r0) (s.gpr x)
    have l₀ := carry_le (s.gpr r0 + s.gpr x < s.gpr x)
    generalize (if s.gpr r0 + s.gpr x < s.gpr x then (1 : BitVec 64) else 0) = k₀ at *
    have e₁ : (s.gpr y + k₀).toNat = (s.gpr y).toNat + k₀.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have c₁ := carry (s.gpr r1) (s.gpr y + k₀)
    have l₁ := carry_le (s.gpr r1 + (s.gpr y + k₀) < s.gpr y + k₀)
    generalize (if s.gpr r1 + (s.gpr y + k₀) < s.gpr y + k₀ then (1 : BitVec 64) else 0) = k₁ at *
    rw [BitVec.toNat_add (s.gpr r2)]
    rw [e₁] at c₁
    have := (s.gpr r2).isLt
    have := (s.gpr r0 + s.gpr x).isLt
    have := (s.gpr r1 + (s.gpr y + k₀)).isLt
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

set_option linter.unusedSimpArgs false in
/-- `r₀ + 2⁶⁴ r₁ += x + 2⁶⁴ y`, for `y < 2⁶⁴ - 1`, the carry out into `y`. -/
theorem accF_ok {r0 r1 x y : Reg} (h01 : r0 ≠ r1 := by decide) (h0x : r0 ≠ x := by decide)
    (h0y : r0 ≠ y := by decide) (h1x : r1 ≠ x := by decide) (h1y : r1 ≠ y := by decide)
    (hxy : x ≠ y := by decide) :
    WP isa (.block (accF r0 r1 x y)) s fun s' =>
      ((s.gpr y).toNat < 2 ^ 64 - 1 →
        val3 s' r0 r1 y = (s.gpr r0).toNat + 2 ^ 64 * (s.gpr r1).toNat + val2 s x y) ∧
      (s'.gpr y).toNat ≤ 1 ∧ Keeps [r0, r1, x, y] s s' := by
  apply WP.of_runBlock
  simp only [accF, val3, val2, runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, h01, h0x, h0y, h1x, h1y, hxy, Ne.symm h01, Ne.symm h0x, Ne.symm h0y,
    Ne.symm h1x, Ne.symm h1y, Ne.symm hxy, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fun hb => ?_, carry_le _, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have c₀ := carry (s.gpr r0) (s.gpr x)
    have l₀ := carry_le (s.gpr r0 + s.gpr x < s.gpr x)
    generalize (if s.gpr r0 + s.gpr x < s.gpr x then (1 : BitVec 64) else 0) = k₀ at *
    have e₁ : (s.gpr y + k₀).toNat = (s.gpr y).toNat + k₀.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have c₁ := carry (s.gpr r1) (s.gpr y + k₀)
    rw [e₁] at c₁
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

set_option linter.unusedSimpArgs false in
/-- `r₀ += x + 2⁶⁴ y`, for `y < 2⁶⁴ - 1`, the high word into `y`. -/
theorem acc1_ok {r0 x y : Reg} (h0x : r0 ≠ x := by decide) (h0y : r0 ≠ y := by decide)
    (hxy : x ≠ y := by decide) :
    WP isa (.block (acc1 r0 x y)) s fun s' =>
      ((s.gpr y).toNat < 2 ^ 64 - 1 → val2 s' r0 y = (s.gpr r0).toNat + val2 s x y) ∧
      Keeps [r0, x, y] s s' := by
  apply WP.of_runBlock
  simp only [acc1, val2, runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, h0x, h0y, hxy, Ne.symm h0x, Ne.symm h0y, Ne.symm hxy, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun hb => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have c₀ := carry (s.gpr r0) (s.gpr x)
    have l₀ := carry_le (s.gpr r0 + s.gpr x < s.gpr x)
    generalize (if s.gpr r0 + s.gpr x < s.gpr x then (1 : BitVec 64) else 0) = k₀ at *
    have e₁ : (s.gpr y + k₀).toNat = (s.gpr y).toNat + k₀.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    rw [e₁]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-! ## The steps of a column -/

theorem keeps_ne {rs : List Reg} {s s' : State} (k : Keeps rs s s') {r : Reg} (hr : r ∉ rs := by decide) :
    (s'.gpr r).toNat = (s.gpr r).toNat := by rw [k.1 r hr]

theorem pa3_ok {r0 r1 r2 x y a b : Reg} (h01 : r0 ≠ r1 := by decide) (h02 : r0 ≠ r2 := by decide)
    (h12 : r1 ≠ r2 := by decide) (h0x : r0 ≠ x := by decide) (h0y : r0 ≠ y := by decide)
    (h1x : r1 ≠ x := by decide) (h1y : r1 ≠ y := by decide) (h2x : r2 ≠ x := by decide)
    (h2y : r2 ≠ y := by decide) (hxy : x ≠ y := by decide) (hya : y ≠ a := by decide)
    (hyb : y ≠ b := by decide) :
    WP isa (.block (pa3 r0 r1 r2 x y a b)) s fun s' =>
      (val3 s r0 r1 r2 + (s.gpr a).toNat * (s.gpr b).toNat < 2 ^ 192 →
        val3 s' r0 r1 r2 = val3 s r0 r1 r2 + (s.gpr a).toNat * (s.gpr b).toNat) ∧
      Keeps [r0, r1, r2, x, y] s s' := by
  refine WP.block_append (WP.mono (prodW_ok hya hyb hxy) fun s1 ⟨e1, b1, k1⟩ => ?_)
  refine WP.mono (acc3_ok h01 h02 h12 h0x h0y h1x h1y h2x h2y hxy) fun s2 ⟨e2, k2⟩ =>
    ⟨fun hb => ?_, (k1.trans k2).mono fun r hr => ?_⟩
  · have hv : val3 s1 r0 r1 r2 = val3 s r0 r1 r2 := by
      simp only [val3, keeps_ne k1 (r := r0) (by simp [h0x, h0y]), keeps_ne k1 (r := r1) (by simp [h1x, h1y]),
        keeps_ne k1 (r := r2) (by simp [h2x, h2y])]
    rw [e2 b1, hv, e1, Nat.mod_eq_of_lt hb]
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (h | h) | (h | h | h | h | h) <;> simp only [h, true_or, or_true]

theorem paF_ok {r0 r1 x y a b : Reg} (h01 : r0 ≠ r1 := by decide) (h0x : r0 ≠ x := by decide)
    (h0y : r0 ≠ y := by decide) (h1x : r1 ≠ x := by decide) (h1y : r1 ≠ y := by decide)
    (hxy : x ≠ y := by decide) (hya : y ≠ a := by decide) (hyb : y ≠ b := by decide) :
    WP isa (.block (paF r0 r1 x y a b)) s fun s' =>
      val3 s' r0 r1 y = (s.gpr r0).toNat + 2 ^ 64 * (s.gpr r1).toNat + (s.gpr a).toNat * (s.gpr b).toNat ∧
      (s'.gpr y).toNat ≤ 1 ∧ Keeps [r0, r1, x, y] s s' := by
  refine WP.block_append (WP.mono (prodW_ok hya hyb hxy) fun s1 ⟨e1, b1, k1⟩ => ?_)
  refine WP.mono (accF_ok h01 h0x h0y h1x h1y hxy) fun s2 ⟨e2, c2, k2⟩ =>
    ⟨?_, c2, (k1.trans k2).mono fun r hr => ?_⟩
  · rw [e2 b1, e1, keeps_ne k1 (r := r0) (by simp [h0x, h0y]), keeps_ne k1 (r := r1) (by simp [h1x, h1y])]
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (h | h) | (h | h | h | h) <;> simp only [h, true_or, or_true]

theorem pa1_ok {r0 x y a b : Reg} (h0x : r0 ≠ x := by decide) (h0y : r0 ≠ y := by decide)
    (hxy : x ≠ y := by decide) (hya : y ≠ a := by decide) (hyb : y ≠ b := by decide) :
    WP isa (.block (pa1 r0 x y a b)) s fun s' =>
      val2 s' r0 y = (s.gpr r0).toNat + (s.gpr a).toNat * (s.gpr b).toNat ∧ Keeps [r0, x, y] s s' := by
  refine WP.block_append (WP.mono (prodW_ok hya hyb hxy) fun s1 ⟨e1, b1, k1⟩ => ?_)
  refine WP.mono (acc1_ok h0x h0y hxy) fun s2 ⟨e2, k2⟩ => ⟨?_, (k1.trans k2).mono fun r hr => ?_⟩
  · rw [e2 b1, e1, keeps_ne k1 (r := r0) (by simp [h0x, h0y])]
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (h | h) | (h | h | h) <;> simp only [h, true_or, or_true]

theorem qs3_ok {r0 r1 r2 x y q : Reg} (h01 : r0 ≠ r1 := by decide) (h02 : r0 ≠ r2 := by decide)
    (h12 : r1 ≠ r2 := by decide) (h0x : r0 ≠ x := by decide) (h0y : r0 ≠ y := by decide)
    (h1x : r1 ≠ x := by decide) (h1y : r1 ≠ y := by decide) (h2x : r2 ≠ x := by decide)
    (h2y : r2 ≠ y := by decide) (hxy : x ≠ y := by decide) (hxq : x ≠ q := by decide) :
    WP isa (.block (qs3 r0 r1 r2 x y q)) s fun s' =>
      (val3 s r0 r1 r2 + (s.gpr q).toNat * 2 ^ 32 < 2 ^ 192 →
        val3 s' r0 r1 r2 = val3 s r0 r1 r2 + (s.gpr q).toNat * 2 ^ 32) ∧
      Keeps [r0, r1, r2, x, y] s s' := by
  refine WP.block_append (WP.mono (qShift_ok hxq hxy) fun s1 ⟨e1, b1, k1⟩ => ?_)
  refine WP.mono (acc3_ok h01 h02 h12 h0x h0y h1x h1y h2x h2y hxy) fun s2 ⟨e2, k2⟩ =>
    ⟨fun hb => ?_, (k1.trans k2).mono fun r hr => ?_⟩
  · have hv : val3 s1 r0 r1 r2 = val3 s r0 r1 r2 := by
      simp only [val3, keeps_ne k1 (r := r0) (by simp [h0x, h0y]), keeps_ne k1 (r := r1) (by simp [h1x, h1y]),
        keeps_ne k1 (r := r2) (by simp [h2x, h2y])]
    rw [e2 b1, hv, e1, Nat.mod_eq_of_lt hb]
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (h | h) | (h | h | h | h | h) <;> simp only [h, true_or, or_true]

theorem qmF_ok {r0 r1 x y q : Reg} (h01 : r0 ≠ r1 := by decide) (h0x : r0 ≠ x := by decide)
    (h0y : r0 ≠ y := by decide) (h1x : r1 ≠ x := by decide) (h1y : r1 ≠ y := by decide)
    (hxy : x ≠ y := by decide) (hxq : x ≠ q := by decide) (hyq : y ≠ q := by decide)
    (h0q : r0 ≠ q := by decide) (h1q : r1 ≠ q := by decide) :
    WP isa (.block (qmF r0 r1 x y q)) s fun s' =>
      val3 s' r0 r1 y = (s.gpr r0).toNat + 2 ^ 64 * (s.gpr r1).toNat +
        (s.gpr q).toNat * (2 ^ 64 - 2 ^ 32 + 1) ∧
      (s'.gpr y).toNat ≤ 1 ∧ Keeps [r0, r1, x, y, q] s s' := by
  refine WP.block_append (WP.mono (qMul_ok hxq hxy hyq) fun s1 ⟨e1, b1, k1⟩ => ?_)
  refine WP.mono (accF_ok h01 h0x h0y h1x h1y hxy) fun s2 ⟨e2, c2, k2⟩ =>
    ⟨?_, c2, (k1.trans k2).mono fun r hr => ?_⟩
  · rw [e2 b1, e1, keeps_ne k1 (r := r0) (by simp [h0x, h0y, h0q]),
      keeps_ne k1 (r := r1) (by simp [h1x, h1y, h1q])]
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (h | h | h) | (h | h | h | h) <;> simp only [h, true_or, or_true]

/-- The four words at `A` can be read. -/
def RdW (A : Addr) (s : State) : Prop :=
  A.toNat % 8 = 0 ∧ ∀ j < 4, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * j)) 8

theorem RdW.keeps {A : Addr} {rs : List Reg} {s s' : State} (h : RdW A s) (k : Keeps rs s s') :
    RdW A s' := by
  unfold RdW; rw [k.2.2.1, k.2.2.2.1]; exact h

/-- `ld d, 8i(p)`. -/
theorem wp_ldw {d p : Reg} {A : Addr} {i : Nat} {is : List Instr} {Q : State → Prop} (hi : i < 4)
    (hp : s.gpr p = A) (hr : RdW A s)
    (k : ∀ s', (s'.gpr d).toNat = dw s.mem A (8 * i) → Keeps [d] s s' → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d d p (8 * i) :: is)) s Q :=
  VG.RISCV64.Steps.wp_ld (by omega) (by rw [hp]) (al8 hr.1 (by omega)) (hr.2 i hi) fun s' u =>
    k s' (by rw [u.gpr]; rfl) ⟨fun r hr => u.other r (by simpa using hr), u.mem, u.rd, u.wr, u.sp⟩

theorem term3_ok {r0 r1 r2 x y b : Reg} {i : Nat} {A : Addr} (hi : i < 4) (hp : s.gpr .t5 = A)
    (hr : RdW A s) (h01 : r0 ≠ r1 := by decide) (h02 : r0 ≠ r2 := by decide)
    (h12 : r1 ≠ r2 := by decide) (h0x : r0 ≠ x := by decide) (h0y : r0 ≠ y := by decide)
    (h1x : r1 ≠ x := by decide) (h1y : r1 ≠ y := by decide) (h2x : r2 ≠ x := by decide)
    (h2y : r2 ≠ y := by decide) (hxy : x ≠ y := by decide) (hyb : y ≠ b := by decide)
    (hxb : x ≠ b := by decide) :
    WP isa (.block (term3 r0 r1 r2 x y i b)) s fun s' =>
      (val3 s r0 r1 r2 + dw s.mem A (8 * i) * (s.gpr b).toNat < 2 ^ 192 →
        val3 s' r0 r1 r2 = val3 s r0 r1 r2 + dw s.mem A (8 * i) * (s.gpr b).toNat) ∧
      Keeps [r0, r1, r2, x, y] s s' := by
  refine wp_ldw hi hp hr fun s1 v1 k1 => ?_
  refine WP.mono (pa3_ok h01 h02 h12 h0x h0y h1x h1y h2x h2y hxy (Ne.symm hxy) hyb) fun s2 ⟨e2, k2⟩ =>
    ⟨fun hb => ?_, (k1.trans k2).mono fun r hr => ?_⟩
  · have hv : val3 s1 r0 r1 r2 = val3 s r0 r1 r2 := by
      simp only [val3, keeps_ne k1 (r := r0) (by simp [h0x]), keeps_ne k1 (r := r1) (by simp [h1x]),
        keeps_ne k1 (r := r2) (by simp [h2x])]
    have hb1 : (s1.gpr b).toNat = (s.gpr b).toNat := keeps_ne k1 (by simp [Ne.symm hxb])
    rw [hv, v1, hb1] at e2
    exact e2 hb
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | (h | h | h | h | h) <;> simp only [h, true_or, or_true]

/-! ## The columns -/

/-- The value of a register. -/
abbrev rv (s : State) (r : Reg) : Nat := (s.gpr r).toNat

theorem mul128 {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a * b < 2 ^ 128 :=
  Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt ha hb) (by decide)

theorem rv_lt (s : State) (r : Reg) : rv s r < 2 ^ 64 := (s.gpr r).isLt

/-- Columns 0 and 1. -/
theorem col01_ok {A B : Addr} (hA : s.gpr .t5 = A) (hB : s.gpr .t4 = B) (hrA : RdW A s)
    (hrB : RdW B s) :
    WP isa (.block col01) s fun s' =>
      rv s' .a0 = dw s.mem B 0 ∧ rv s' .a4 = dw s.mem B 8 ∧
      rv s' .a5 + 2 ^ 64 * val3 s' .a6 .t0 .t6 =
        dw s.mem A 0 * dw s.mem B 0 +
          2 ^ 64 * (dw s.mem A 8 * dw s.mem B 0 + dw s.mem A 0 * dw s.mem B 8 + rv s' .a5 * 2 ^ 32) ∧
      Keeps [.a0, .a4, .a5, .a6, .a7, .t0, .t6, .a1] s s' := by
  simp only [col01, List.cons_append, List.nil_append, List.append_assoc]
  refine wp_ldw (i := 0) (by decide) hB hrB fun s1 v1 k1 => ?_
  refine wp_ldw (i := 1) (by decide) (by rw [k1.1 _ (by decide), hB]) (hrB.keeps k1) fun s2 v2 k2 => ?_
  refine wp_ldw (i := 0) (by decide) (by rw [k2.1 _ (by decide), k1.1 _ (by decide), hA])
    ((hrA.keeps k1).keeps k2) fun s3 v3 k3 => ?_
  refine WP.block_append (WP.mono (prodW_ok (x := .a5) (y := .a6) (a := .a5) (b := .a0)) fun s4 ⟨e4, b4, k4⟩ => ?_)
  have K4 := ((k1.trans k2).trans k3).trans k4
  refine wp_ldw (i := 1) (by decide) (by rw [K4.1 _ (by decide), hA]) (hrA.keeps K4) fun s5 v5 k5 => ?_
  refine WP.block_append (WP.mono (pa1_ok (r0 := .a6) (x := .a7) (y := .t0) (a := .a7) (b := .a0))
    fun s6 ⟨e6, k6⟩ => ?_)
  have K6 := (K4.trans k5).trans k6
  refine wp_ldw (i := 0) (by decide) (by rw [K6.1 _ (by decide), hA]) (hrA.keeps K6) fun s7 v7 k7 => ?_
  refine WP.block_append (WP.mono (paF_ok (r0 := .a6) (r1 := .t0) (x := .a7) (y := .t6) (a := .a7) (b := .a4))
    fun s8 ⟨e8, c8, k8⟩ => ?_)
  have K8 := (K6.trans k7).trans k8
  refine WP.mono (qs3_ok (r0 := .a6) (r1 := .t0) (r2 := .t6) (x := .a7) (y := .a1) (q := .a5))
    fun s9 ⟨e9, k9⟩ => ?_
  have K9 := K8.trans k9
  have m1 : s1.mem = s.mem := k1.2.1
  have m2 : s2.mem = s.mem := (k1.trans k2).2.1
  have m4 : s4.mem = s.mem := K4.2.1
  have m6 : s6.mem = s.mem := K6.2.1
  simp only [m1, m2, m4, m6, Nat.mul_zero, Nat.mul_one] at v1 v2 v3 v5 v7
  -- The registers' values through the steps.
  have b0_4 : rv s4 .a0 = dw s.mem B 0 := by rw [rv, keeps_ne (k2.trans (k3.trans k4)) (r := .a0) (by decide)]; exact v1
  have b0_6 : rv s6 .a0 = dw s.mem B 0 := by rw [rv, keeps_ne (k5.trans k6) (r := .a0) (by decide)]; exact b0_4
  have b1_8 : rv s8 .a4 = dw s.mem B 8 := by
    rw [rv, keeps_ne (((k3.trans k4).trans (k5.trans k6)).trans (k7.trans k8)) (r := .a4) (by decide)]; exact v2
  have a5_9 : rv s9 .a5 = rv s4 .a5 := keeps_ne ((k5.trans k6).trans ((k7.trans k8).trans k9)) (by decide)
  have a3_4 : rv s3 .a0 = dw s.mem B 0 := by rw [rv, keeps_ne (k2.trans k3) (r := .a0) (by decide)]; exact v1
  have a0_5 : rv s5 .a0 = dw s.mem B 0 := by rw [rv, keeps_ne k5 (r := .a0) (by decide)]; exact b0_4
  have a6_5 : rv s5 .a6 = rv s4 .a6 := keeps_ne k5 (by decide)
  have a6_7 : rv s7 .a6 = rv s6 .a6 := keeps_ne k7 (by decide)
  have t0_7 : rv s7 .t0 = rv s6 .t0 := keeps_ne k7 (by decide)
  have b1_7 : rv s7 .a4 = dw s.mem B 8 := by
    rw [rv, keeps_ne (((k3.trans k4).trans (k5.trans k6)).trans k7) (r := .a4) (by decide)]; exact v2
  have a5_8 : rv s8 .a5 = rv s4 .a5 := keeps_ne ((k5.trans k6).trans (k7.trans k8)) (by decide)
  simp only [val2, val3, rv] at e4 e6 e8 e9 a0_5 a6_5 a6_7 t0_7 b1_7 a5_8 a5_9 a3_4 b0_6 b1_8 ⊢
  rw [v3, a3_4] at e4
  rw [v5, a0_5, a6_5] at e6
  rw [v7, b1_7, a6_7, t0_7] at e8
  rw [a5_8] at e9
  have p0 := mul128 (dw_lt s.mem A 0) (dw_lt s.mem B 0)
  have p1 := mul128 (dw_lt s.mem A 8) (dw_lt s.mem B 0)
  have p2 := mul128 (dw_lt s.mem A 0) (dw_lt s.mem B 8)
  have := rv_lt s4 .a5; have := rv_lt s4 .a6; have := rv_lt s6 .a6; have := rv_lt s6 .t0
  have := rv_lt s8 .a6; have := rv_lt s8 .t0; have := rv_lt s8 .t6
  simp only [rv] at *
  have e9' := e9 (by omega)
  refine ⟨?_, ?_, ?_, K9.mono⟩
  · rw [keeps_ne (k7.trans (k8.trans k9)) (r := .a0) (by decide)]; exact b0_6
  · rw [keeps_ne k9 (r := .a4) (by decide)]; exact b1_8
  · rw [a5_9]
    omega

/-- Column 2. -/
theorem col2_ok {A B : Addr} (hA : s.gpr .t5 = A) (hB : s.gpr .t4 = B) (hrA : RdW A s)
    (hrB : RdW B s) :
    WP isa (.block col2) s fun s' =>
      rv s' .a7 = dw s.mem B 16 ∧
      val3 s' .t0 .t6 .a1 = rv s .t0 + 2 ^ 64 * rv s .t6 + dw s.mem A 16 * rv s .a0 +
        dw s.mem A 8 * rv s .a4 + dw s.mem A 0 * dw s.mem B 16 + rv s .a6 * 2 ^ 32 ∧
      Keeps [.a7, .t3, .t0, .t6, .a1, .a2] s s' := by
  simp only [col2, List.cons_append, List.append_assoc]
  refine wp_ldw (i := 2) (by decide) hB hrB fun s1 v1 k1 => ?_
  refine wp_ldw (i := 2) (by decide) (by rw [k1.1 _ (by decide), hA]) (hrA.keeps k1) fun s2 v2 k2 => ?_
  refine WP.block_append (WP.mono (paF_ok (r0 := .t0) (r1 := .t6) (x := .t3) (y := .a1) (a := .t3) (b := .a0))
    fun s3 ⟨e3, c3, k3⟩ => ?_)
  have K3 := (k1.trans k2).trans k3
  refine WP.block_append (WP.mono (term3_ok (r0 := .t0) (r1 := .t6) (r2 := .a1) (x := .t3) (y := .a2) (b := .a4)
    (i := 1) (by decide) (by rw [K3.1 _ (by decide), hA]) (hrA.keeps K3)) fun s4 ⟨e4, k4⟩ => ?_)
  have K4 := K3.trans k4
  refine WP.block_append (WP.mono (term3_ok (r0 := .t0) (r1 := .t6) (r2 := .a1) (x := .t3) (y := .a2) (b := .a7)
    (i := 0) (by decide) (by rw [K4.1 _ (by decide), hA]) (hrA.keeps K4)) fun s5 ⟨e5, k5⟩ => ?_)
  have K5 := K4.trans k5
  refine WP.mono (qs3_ok (r0 := .t0) (r1 := .t6) (r2 := .a1) (x := .t3) (y := .a2) (q := .a6))
    fun s6 ⟨e6, k6⟩ => ?_
  have K6 := K5.trans k6
  have m1 : s1.mem = s.mem := k1.2.1
  have m3 : s3.mem = s.mem := K3.2.1
  have m4 : s4.mem = s.mem := K4.2.1
  simp only [m1, m3, m4, Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at v1 v2 e4 e5
  have t0_2 : rv s2 .t0 = rv s .t0 := keeps_ne (k1.trans k2) (by decide)
  have t6_2 : rv s2 .t6 = rv s .t6 := keeps_ne (k1.trans k2) (by decide)
  have a0_2 : rv s2 .a0 = rv s .a0 := keeps_ne (k1.trans k2) (by decide)
  have a4_3 : rv s3 .a4 = rv s .a4 := keeps_ne K3 (by decide)
  have a7_4 : rv s4 .a7 = dw s.mem B 16 := by
    rw [rv, keeps_ne ((k2.trans k3).trans k4) (r := .a7) (by decide)]; exact v1
  have a6_5 : rv s5 .a6 = rv s .a6 := keeps_ne K5 (by decide)
  simp only [val3, rv] at e3 e4 e5 e6 t0_2 t6_2 a0_2 a4_3 a7_4 a6_5 v2 ⊢
  rw [v2, t0_2, t6_2, a0_2] at e3
  rw [a4_3] at e4
  rw [a7_4] at e5
  rw [a6_5] at e6
  have p0 := mul128 (dw_lt s.mem A 16) (rv_lt s .a0)
  have p1 := mul128 (dw_lt s.mem A 8) (rv_lt s .a4)
  have p2 := mul128 (dw_lt s.mem A 0) (dw_lt s.mem B 16)
  have := rv_lt s .t0; have := rv_lt s .t6; have := rv_lt s .a6
  have := rv_lt s3 .t0; have := rv_lt s3 .t6; have := rv_lt s4 .t0; have := rv_lt s4 .t6
  have := rv_lt s5 .t0; have := rv_lt s5 .t6
  simp only [rv] at *
  have e4' := e4 (by omega)
  have e5' := e5 (by omega)
  have e6' := e6 (by omega)
  refine ⟨?_, by omega, K6.mono⟩
  rw [keeps_ne (k5.trans k6) (r := .a7) (by decide)]; exact a7_4

/-- Column 3. -/
theorem col3_ok {A B : Addr} (hA : s.gpr .t5 = A) (hB : s.gpr .t4 = B) (hrA : RdW A s)
    (hrB : RdW B s) :
    WP isa (.block col3) s fun s' =>
      rv s' .a0 = dw s.mem B 24 ∧
      val3 s' .t6 .a1 .t3 = rv s .t6 + 2 ^ 64 * rv s .a1 + rv s .a5 * (2 ^ 64 - 2 ^ 32 + 1) +
        dw s.mem A 24 * rv s .a0 + dw s.mem A 16 * rv s .a4 + dw s.mem A 8 * rv s .a7 +
        dw s.mem A 0 * dw s.mem B 24 + rv s .t0 * 2 ^ 32 ∧
      Keeps [.t6, .a1, .t3, .a5, .a2, .a0] s s' := by
  simp only [col3, List.cons_append, List.append_assoc]
  refine WP.block_append (WP.mono (qmF_ok (r0 := .t6) (r1 := .a1) (x := .a2) (y := .t3) (q := .a5))
    fun s1 ⟨e1, c1, k1⟩ => ?_)
  refine WP.block_append (WP.mono (term3_ok (r0 := .t6) (r1 := .a1) (r2 := .t3) (x := .a5) (y := .a2) (b := .a0)
    (i := 3) (by decide) (by rw [k1.1 _ (by decide), hA]) (hrA.keeps k1)) fun s2 ⟨e2, k2⟩ => ?_)
  have K2 := k1.trans k2
  refine wp_ldw (i := 3) (by decide) (by rw [K2.1 _ (by decide), hB]) (hrB.keeps K2) fun s3 v3 k3 => ?_
  have K3 := K2.trans k3
  refine WP.block_append (WP.mono (term3_ok (r0 := .t6) (r1 := .a1) (r2 := .t3) (x := .a5) (y := .a2) (b := .a4)
    (i := 2) (by decide) (by rw [K3.1 _ (by decide), hA]) (hrA.keeps K3)) fun s4 ⟨e4, k4⟩ => ?_)
  have K4 := K3.trans k4
  refine WP.block_append (WP.mono (term3_ok (r0 := .t6) (r1 := .a1) (r2 := .t3) (x := .a5) (y := .a2) (b := .a7)
    (i := 1) (by decide) (by rw [K4.1 _ (by decide), hA]) (hrA.keeps K4)) fun s5 ⟨e5, k5⟩ => ?_)
  have K5 := K4.trans k5
  refine WP.block_append (WP.mono (term3_ok (r0 := .t6) (r1 := .a1) (r2 := .t3) (x := .a5) (y := .a2) (b := .a0)
    (i := 0) (by decide) (by rw [K5.1 _ (by decide), hA]) (hrA.keeps K5)) fun s6 ⟨e6, k6⟩ => ?_)
  have K6 := K5.trans k6
  refine WP.mono (qs3_ok (r0 := .t6) (r1 := .a1) (r2 := .t3) (x := .a5) (y := .a2) (q := .t0))
    fun s7 ⟨e7, k7⟩ => ?_
  have K7 := K6.trans k7
  have m1 : s1.mem = s.mem := k1.2.1
  have m2 : s2.mem = s.mem := K2.2.1
  have m3 : s3.mem = s.mem := K3.2.1
  have m4 : s4.mem = s.mem := K4.2.1
  have m5 : s5.mem = s.mem := K5.2.1
  simp only [m1, m2, m3, m4, m5, Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at v3 e2 e4 e5 e6
  have a0_1 : rv s1 .a0 = rv s .a0 := keeps_ne k1 (by decide)
  have a4_3 : rv s3 .a4 = rv s .a4 := keeps_ne K3 (by decide)
  have a7_4 : rv s4 .a7 = rv s .a7 := keeps_ne K4 (by decide)
  have a0_5 : rv s5 .a0 = dw s.mem B 24 := by
    rw [rv, keeps_ne (k4.trans k5) (r := .a0) (by decide)]; exact v3
  have t0_6 : rv s6 .t0 = rv s .t0 := keeps_ne K6 (by decide)
  have f1 : rv s3 .t6 = rv s2 .t6 := keeps_ne k3 (by decide)
  have f2 : rv s3 .a1 = rv s2 .a1 := keeps_ne k3 (by decide)
  have f3 : rv s3 .t3 = rv s2 .t3 := keeps_ne k3 (by decide)
  simp only [val3, rv] at e1 e2 e4 e5 e6 e7 a0_1 a4_3 a7_4 a0_5 t0_6 v3 f1 f2 f3 ⊢
  rw [a0_1] at e2
  rw [a4_3, f1, f2, f3] at e4
  rw [a7_4] at e5
  rw [a0_5] at e6
  rw [t0_6] at e7
  have p0 := mul128 (dw_lt s.mem A 24) (rv_lt s .a0)
  have p1 := mul128 (dw_lt s.mem A 16) (rv_lt s .a4)
  have p2 := mul128 (dw_lt s.mem A 8) (rv_lt s .a7)
  have p3 := mul128 (dw_lt s.mem A 0) (dw_lt s.mem B 24)
  have := rv_lt s .t6; have := rv_lt s .a1; have := rv_lt s .a5; have := rv_lt s .t0
  have := rv_lt s1 .t6; have := rv_lt s1 .a1
  have := rv_lt s2 .t6; have := rv_lt s2 .a1; have := rv_lt s4 .t6; have := rv_lt s4 .a1
  have := rv_lt s5 .t6; have := rv_lt s5 .a1; have := rv_lt s6 .t6; have := rv_lt s6 .a1
  simp only [rv] at *
  have e2' := e2 (by omega)
  have e4' := e4 (by omega)
  have e5' := e5 (by omega)
  have e6' := e6 (by omega)
  have e7' := e7 (by omega)
  refine ⟨?_, by omega, K7.mono⟩
  rw [keeps_ne (k6.trans k7) (r := .a0) (by decide)]; exact a0_5

/-- Column 4. -/
theorem col4_ok {A : Addr} (hA : s.gpr .t5 = A) (hrA : RdW A s) :
    WP isa (.block col4) s fun s' =>
      rv s' .a6 = dw s.mem A 24 ∧
      val3 s' .a1 .t3 .t4 = rv s .a1 + 2 ^ 64 * rv s .t3 + rv s .a6 * (2 ^ 64 - 2 ^ 32 + 1) +
        dw s.mem A 24 * rv s .a4 + dw s.mem A 16 * rv s .a7 + dw s.mem A 8 * rv s .a0 +
        rv s .t6 * 2 ^ 32 ∧
      Keeps [.a1, .t3, .t4, .a5, .a6, .a2] s s' := by
  simp only [col4, List.cons_append, List.append_assoc]
  refine WP.block_append (WP.mono (qmF_ok (r0 := .a1) (r1 := .t3) (x := .a5) (y := .t4) (q := .a6))
    fun s1 ⟨e1, c1, k1⟩ => ?_)
  refine wp_ldw (i := 3) (by decide) (by rw [k1.1 _ (by decide), hA]) (hrA.keeps k1) fun s2 v2 k2 => ?_
  have K2 := k1.trans k2
  refine WP.block_append (WP.mono (pa3_ok (r0 := .a1) (r1 := .t3) (r2 := .t4) (x := .a5) (y := .a2) (a := .a6)
    (b := .a4)) fun s3 ⟨e3, k3⟩ => ?_)
  have K3 := K2.trans k3
  refine WP.block_append (WP.mono (term3_ok (r0 := .a1) (r1 := .t3) (r2 := .t4) (x := .a5) (y := .a2) (b := .a7)
    (i := 2) (by decide) (by rw [K3.1 _ (by decide), hA]) (hrA.keeps K3)) fun s4 ⟨e4, k4⟩ => ?_)
  have K4 := K3.trans k4
  refine WP.block_append (WP.mono (term3_ok (r0 := .a1) (r1 := .t3) (r2 := .t4) (x := .a5) (y := .a2) (b := .a0)
    (i := 1) (by decide) (by rw [K4.1 _ (by decide), hA]) (hrA.keeps K4)) fun s5 ⟨e5, k5⟩ => ?_)
  have K5 := K4.trans k5
  refine WP.mono (qs3_ok (r0 := .a1) (r1 := .t3) (r2 := .t4) (x := .a5) (y := .a2) (q := .t6))
    fun s6 ⟨e6, k6⟩ => ?_
  have K6 := K5.trans k6
  have m1 : s1.mem = s.mem := k1.2.1
  have m3 : s3.mem = s.mem := K3.2.1
  have m4 : s4.mem = s.mem := K4.2.1
  simp only [m1, m3, m4, Nat.mul_one, Nat.reduceMul] at v2 e4 e5
  have a4_2 : rv s2 .a4 = rv s .a4 := keeps_ne K2 (by decide)
  have a7_3 : rv s3 .a7 = rv s .a7 := keeps_ne K3 (by decide)
  have a0_4 : rv s4 .a0 = rv s .a0 := keeps_ne K4 (by decide)
  have t6_5 : rv s5 .t6 = rv s .t6 := keeps_ne K5 (by decide)
  have f1 : rv s2 .a1 = rv s1 .a1 := keeps_ne k2 (by decide)
  have f2 : rv s2 .t3 = rv s1 .t3 := keeps_ne k2 (by decide)
  have f3 : rv s2 .t4 = rv s1 .t4 := keeps_ne k2 (by decide)
  simp only [val3, rv] at e1 e3 e4 e5 e6 a4_2 a7_3 a0_4 t6_5 v2 f1 f2 f3 ⊢
  rw [v2, a4_2, f1, f2, f3] at e3
  rw [a7_3] at e4
  rw [a0_4] at e5
  rw [t6_5] at e6
  have p0 := mul128 (dw_lt s.mem A 24) (rv_lt s .a4)
  have p1 := mul128 (dw_lt s.mem A 16) (rv_lt s .a7)
  have p2 := mul128 (dw_lt s.mem A 8) (rv_lt s .a0)
  have := rv_lt s .a1; have := rv_lt s .t3; have := rv_lt s .a6; have := rv_lt s .t6
  have := rv_lt s1 .a1; have := rv_lt s1 .t3
  have := rv_lt s3 .a1; have := rv_lt s3 .t3; have := rv_lt s4 .a1; have := rv_lt s4 .t3
  have := rv_lt s5 .a1; have := rv_lt s5 .t3
  simp only [rv] at *
  have e3' := e3 (by omega)
  have e4' := e4 (by omega)
  have e5' := e5 (by omega)
  have e6' := e6 (by omega)
  refine ⟨?_, by omega, K6.mono⟩
  rw [keeps_ne (k3.trans (k4.trans (k5.trans k6))) (r := .a6) (by decide)]; exact v2

/-- Columns 5 and 6. -/
theorem col56_ok {A : Addr} (hA : s.gpr .t5 = A) (hrA : RdW A s) :
    WP isa (.block col56) s fun s' =>
      rv s' .t3 + 2 ^ 64 * val3 s' .t4 .t5 .a2 = rv s .t3 + 2 ^ 64 * rv s .t4 +
        rv s .t0 * (2 ^ 64 - 2 ^ 32 + 1) + dw s.mem A 16 * rv s .a0 + rv s .a6 * rv s .a7 +
        2 ^ 64 * (rv s .t6 * (2 ^ 64 - 2 ^ 32 + 1) + rv s .a6 * rv s .a0) ∧
      Keeps [.a5, .t3, .t4, .a4, .t5, .t0, .a2, .t6] s s' := by
  simp only [col56, List.cons_append, List.append_assoc]
  refine wp_ldw (i := 2) (by decide) hA hrA fun s1 v1 k1 => ?_
  refine WP.block_append (WP.mono (qmF_ok (r0 := .t3) (r1 := .t4) (x := .a4) (y := .t5) (q := .t0))
    fun s2 ⟨e2, c2, k2⟩ => ?_)
  refine WP.block_append (WP.mono (pa3_ok (r0 := .t3) (r1 := .t4) (r2 := .t5) (x := .a5) (y := .a2) (a := .a5)
    (b := .a0)) fun s3 ⟨e3, k3⟩ => ?_)
  refine WP.block_append (WP.mono (pa3_ok (r0 := .t3) (r1 := .t4) (r2 := .t5) (x := .a5) (y := .a2) (a := .a6)
    (b := .a7)) fun s4 ⟨e4, k4⟩ => ?_)
  refine WP.block_append (WP.mono (qmF_ok (r0 := .t4) (r1 := .t5) (x := .a4) (y := .a2) (q := .t6))
    fun s5 ⟨e5, c5, k5⟩ => ?_)
  refine WP.mono (pa3_ok (r0 := .t4) (r1 := .t5) (r2 := .a2) (x := .a4) (y := .a5) (a := .a6) (b := .a0))
    fun s6 ⟨e6, k6⟩ => ?_
  have K6 := ((((k1.trans k2).trans k3).trans k4).trans k5).trans k6
  have f1 : rv s1 .t3 = rv s .t3 := keeps_ne k1 (by decide)
  have f2 : rv s1 .t4 = rv s .t4 := keeps_ne k1 (by decide)
  have f3 : rv s1 .t0 = rv s .t0 := keeps_ne k1 (by decide)
  have a0_2 : rv s2 .a0 = rv s .a0 := keeps_ne (k1.trans k2) (by decide)
  have a5_2 : rv s2 .a5 = dw s.mem A 16 := by rw [rv, keeps_ne k2 (r := .a5) (by decide)]; exact v1
  have a6_3 : rv s3 .a6 = rv s .a6 := keeps_ne ((k1.trans k2).trans k3) (by decide)
  have a7_3 : rv s3 .a7 = rv s .a7 := keeps_ne ((k1.trans k2).trans k3) (by decide)
  have t6_4 : rv s4 .t6 = rv s .t6 := keeps_ne (((k1.trans k2).trans k3).trans k4) (by decide)
  have a6_5 : rv s5 .a6 = rv s .a6 := keeps_ne ((((k1.trans k2).trans k3).trans k4).trans k5) (by decide)
  have a0_5 : rv s5 .a0 = rv s .a0 := keeps_ne ((((k1.trans k2).trans k3).trans k4).trans k5) (by decide)
  have t3_6 : rv s6 .t3 = rv s4 .t3 := keeps_ne (k5.trans k6) (by decide)
  simp only [val3, rv] at e2 e3 e4 e5 e6 f1 f2 f3 a0_2 a5_2 a6_3 a7_3 t6_4 a6_5 a0_5 t3_6 ⊢
  rw [f1, f2, f3] at e2
  rw [a5_2, a0_2] at e3
  rw [a6_3, a7_3] at e4
  rw [t6_4] at e5
  rw [a6_5, a0_5] at e6
  have p0 := mul128 (dw_lt s.mem A 16) (rv_lt s .a0)
  have p1 := mul128 (rv_lt s .a6) (rv_lt s .a7)
  have p2 := mul128 (rv_lt s .a6) (rv_lt s .a0)
  have := rv_lt s .t3; have := rv_lt s .t4; have := rv_lt s .t0; have := rv_lt s .t6
  have := rv_lt s2 .t3; have := rv_lt s2 .t4; have := rv_lt s3 .t3; have := rv_lt s3 .t4
  have := rv_lt s4 .t3; have := rv_lt s4 .t4; have := rv_lt s4 .t5; have := rv_lt s5 .t4; have := rv_lt s5 .t5
  simp only [rv] at *
  have e3' := e3 (by omega)
  have e4' := e4 (by omega)
  have e6' := e6 (by omega)
  refine ⟨by omega, K6.mono⟩

/-! ## The product -/

/-- A product of four-word numbers by columns. -/
theorem prod4 (B a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    (a0 + B * (a1 + B * (a2 + B * a3))) * (b0 + B * (b1 + B * (b2 + B * b3))) =
      a0 * b0 + B * ((a1 * b0 + a0 * b1) + B * ((a2 * b0 + a1 * b1 + a0 * b2) +
        B * ((a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3) + B * ((a3 * b1 + a2 * b2 + a1 * b3) +
          B * ((a3 * b2 + a2 * b3) + B * (a3 * b3)))))) := by
  grind

/-- The columns' sums, weighted, are the product plus `Q p`: column `k` adds the
products `aᵢ bⱼ` with `i + j = k`, `q₍ₖ₋₁₎ 2³²` and `q₍ₖ₋₃₎ (2⁶⁴ - 2³² + 1)`, and
`p + 1 = 2⁹⁶ + 2¹⁹² (2⁶⁴ - 2³² + 1)`. -/
theorem cols_sum {p00 p10 p01 p20 p11 p02 p30 p21 p12 p03 p31 p22 p13 p32 p23 p33 : Nat}
    {q0 q1 q2 q3 x1 y1 x2 y2 x3 y3 x4 y4 r0 r1 r2 r3 c : Nat}
    (E1 : q0 + 2 ^ 64 * (q1 + 2 ^ 64 * x1 + 2 ^ 128 * y1) = p00 + 2 ^ 64 * (p10 + p01 + q0 * 2 ^ 32))
    (E2 : q2 + 2 ^ 64 * x2 + 2 ^ 128 * y2 = x1 + 2 ^ 64 * y1 + p20 + p11 + p02 + q1 * 2 ^ 32)
    (E3 : q3 + 2 ^ 64 * x3 + 2 ^ 128 * y3 =
      x2 + 2 ^ 64 * y2 + q0 * (2 ^ 64 - 2 ^ 32 + 1) + p30 + p21 + p12 + p03 + q2 * 2 ^ 32)
    (E4 : r0 + 2 ^ 64 * x4 + 2 ^ 128 * y4 =
      x3 + 2 ^ 64 * y3 + q1 * (2 ^ 64 - 2 ^ 32 + 1) + p31 + p22 + p13 + q3 * 2 ^ 32)
    (E5 : r1 + 2 ^ 64 * (r2 + 2 ^ 64 * r3 + 2 ^ 128 * c) = x4 + 2 ^ 64 * y4 +
      q2 * (2 ^ 64 - 2 ^ 32 + 1) + p23 + p32 + 2 ^ 64 * (q3 * (2 ^ 64 - 2 ^ 32 + 1) + p33)) :
    (r0 + 2 ^ 64 * r1 + 2 ^ 128 * r2 + 2 ^ 192 * r3 + 2 ^ 256 * c) * 2 ^ 256 =
      (p00 + 2 ^ 64 * ((p10 + p01) + 2 ^ 64 * ((p20 + p11 + p02) +
        2 ^ 64 * ((p30 + p21 + p12 + p03) + 2 ^ 64 * ((p31 + p22 + p13) +
          2 ^ 64 * ((p32 + p23) + 2 ^ 64 * p33)))))) +
      (q0 + 2 ^ 64 * (q1 + 2 ^ 64 * (q2 + 2 ^ 64 * q3))) * P := by
  unfold P
  grind

/-- The four words at `A`. -/
abbrev w4 (m : Mem) (A : Addr) : Nat :=
  dw m A 0 + 2 ^ 64 * (dw m A 8 + 2 ^ 64 * (dw m A 16 + 2 ^ 64 * dw m A 24))

/-- `fused`: `X 2²⁵⁶ = [t5] [t4] + Q p` for the result `X` in `a1`, `t3`, `t4`, `t5` and `a2`
and some `Q < 2²⁵⁶`. -/
theorem fused_ok {A B : Addr} (hA : s.gpr .t5 = A) (hB : s.gpr .t4 = B) (hrA : RdW A s)
    (hrB : RdW B s) :
    WP isa (.block fused) s fun s' =>
      (∃ Q, Q < 2 ^ 256 ∧
        (rv s' .a1 + 2 ^ 64 * rv s' .t3 + 2 ^ 128 * rv s' .t4 + 2 ^ 192 * rv s' .t5 +
          2 ^ 256 * rv s' .a2) * 2 ^ 256 = w4 s.mem A * w4 s.mem B + Q * P) ∧
      Keeps [.t0, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a4, .a5, .a6, .a7] s s' := by
  simp only [fused, List.append_assoc]
  refine WP.block_append (WP.mono (col01_ok hA hB hrA hrB) fun s1 ⟨b0, b1, E1, K1⟩ => ?_)
  refine WP.block_append (WP.mono (col2_ok (by rw [K1.1 _ (by decide), hA]) (by rw [K1.1 _ (by decide), hB])
    (hrA.keeps K1) (hrB.keeps K1)) fun s2 ⟨b2, E2, K2⟩ => ?_)
  have K12 := K1.trans K2
  refine WP.block_append (WP.mono (col3_ok (by rw [K12.1 _ (by decide), hA]) (by rw [K12.1 _ (by decide), hB])
    (hrA.keeps K12) (hrB.keeps K12)) fun s3 ⟨b3, E3, K3⟩ => ?_)
  have K13 := K12.trans K3
  refine WP.block_append (WP.mono (col4_ok (by rw [K13.1 _ (by decide), hA]) (hrA.keeps K13))
    fun s4 ⟨a3, E4, K4⟩ => ?_)
  have K14 := K13.trans K4
  refine WP.mono (col56_ok (by rw [K14.1 _ (by decide), hA]) (hrA.keeps K14)) fun s5 ⟨E5, K5⟩ => ?_
  have K15 := K14.trans K5
  refine ⟨?_, K15.mono⟩
  have m1 : s1.mem = s.mem := K1.2.1
  have m2 : s2.mem = s.mem := K12.2.1
  have m3 : s3.mem = s.mem := K13.2.1
  have m4 : s4.mem = s.mem := K14.2.1
  rw [m1] at E2 b2
  rw [m2] at E3 b3
  rw [m3] at E4 a3
  rw [m4] at E5
  -- The registers each column reads, from the columns before.
  have r2a0 : rv s1 .a0 = dw s.mem B 0 := b0
  have r2a4 : rv s1 .a4 = dw s.mem B 8 := b1
  have r3a5 : rv s2 .a5 = rv s1 .a5 := keeps_ne K2 (by decide)
  have r3a0 : rv s2 .a0 = dw s.mem B 0 := by rw [rv, keeps_ne K2 (r := .a0) (by decide)]; exact b0
  have r3a4 : rv s2 .a4 = dw s.mem B 8 := by rw [rv, keeps_ne K2 (r := .a4) (by decide)]; exact b1
  have r4a6 : rv s3 .a6 = rv s1 .a6 := keeps_ne (K2.trans K3) (by decide)
  have r4a4 : rv s3 .a4 = dw s.mem B 8 := by rw [rv, keeps_ne K3 (r := .a4) (by decide)]; exact r3a4
  have r4a7 : rv s3 .a7 = dw s.mem B 16 := by rw [rv, keeps_ne K3 (r := .a7) (by decide)]; exact b2
  have r5t0 : rv s4 .t0 = rv s2 .t0 := keeps_ne (K3.trans K4) (by decide)
  have r5t6 : rv s4 .t6 = rv s3 .t6 := keeps_ne K4 (by decide)
  have r5a0 : rv s4 .a0 = dw s.mem B 24 := by rw [rv, keeps_ne K4 (r := .a0) (by decide)]; exact b3
  have r5a7 : rv s4 .a7 = dw s.mem B 16 := by rw [rv, keeps_ne K4 (r := .a7) (by decide)]; exact r4a7
  have r6a1 : rv s5 .a1 = rv s4 .a1 := keeps_ne K5 (by decide)
  rw [r2a0, r2a4] at E2
  rw [r3a5, r3a0, r3a4, b2] at E3
  rw [r4a6, r4a4, r4a7, b3] at E4
  rw [r5t0, r5t6, r5a0, r5a7, a3] at E5
  have hp := prod4 (2 ^ 64) (dw s.mem A 0) (dw s.mem A 8) (dw s.mem A 16) (dw s.mem A 24)
    (dw s.mem B 0) (dw s.mem B 8) (dw s.mem B 16) (dw s.mem B 24)
  refine ⟨rv s1 .a5 + 2 ^ 64 * (rv s1 .a6 + 2 ^ 64 * (rv s2 .t0 + 2 ^ 64 * rv s3 .t6)), ?_, ?_⟩
  · have := rv_lt s1 .a5; have := rv_lt s1 .a6; have := rv_lt s2 .t0; have := rv_lt s3 .t6
    omega
  · rw [r6a1, hp]
    simp only [val3, rv] at E1 E2 E3 E4 E5 ⊢
    exact cols_sum E1 E2 E3 E4 E5

end VG.Proof.Weierstrass.RISCV64.P256Field

namespace VG.Proof.Weierstrass.RISCV64.P256Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Proof.X25519.RISCV64 (Ctx Rest V)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok clob64 dw_write_self dw_write_other al8 dw_frame)

/-- The registers the operations write. -/
abbrev clobM : List Reg := [.t0, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a4, .a5, .a6, .a7]

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

/-- The product's words, as a reduction reads them. -/
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

/-- `mulWith red sum`: `[t2] = [t4] [t5] 2⁻²⁵⁶ mod m`, for a reduction `red` of the
product at `ACC` that may write the copies `MA` and `MB` (as Gen4's `reduceR`,
which keeps registers there) and a `sum` as `csubWith_ok`'s. -/
theorem mulWithF_ok {red sum : List Instr} {M : Nat} (hM0 : 0 < M) (hM : M ≤ 2 ^ 256)
    (hred : ∀ {b : Addr} {s : State}, Ctx b s → WP isa (.block red) s fun s' =>
      Ctx b s' ∧ Rest clobM s s' ∧ Frame [⟨b + BitVec.ofNat 64 MA, 32⟩, ⟨b + BitVec.ofNat 64 MB, 32⟩] s.mem s'.mem ∧
      (s'.gpr XC).toNat ≤ 1 ∧
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
  rw [eMA, eMB] at m2
  refine ⟨by rw [v3]; exact Nat.mod_lt _ hM0, ?_, f1.trans ((m2.mono (by simp)).trans (f3.mono (by simp))),
    fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [v3, Nat.mod_mul_mod]
    simp only [v4] at hv2 ⊢
    rw [hv2, Nat.add_mul_mod_self_right, v1]
  · have sC : ∀ x ∈ clobC, x ∈ clobM := by decide
    have s6 : ∀ x ∈ clob64, x ∈ clobM := by decide
    rw [g3 r (fun h => hr (sC r h)), ((r1.mono (by decide) : Rest clobM _ _).trans r2).gpr r hr]
  · rw [rd3, r2.rd, r1.rd]
  · rw [wr3, r2.wr, r1.wr]
  · rw [sp3, r2.sp, r1.sp]

/-- `mulWith red sum` for a reduction `red` that writes no memory (P-256's
order's `reduce_ok`). -/
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
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  mulWithF_ok hM0 hM (fun hc => WP.mono (hred hc) fun s' ⟨c, r, m, x, v⟩ =>
    ⟨c, r, by rw [m]; exact Frame.refl _ _, x, v⟩) hs hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB

/-- `mulCore`: `[t2] = [t4] [t5] 2⁻²⁵⁶ mod p`: `fused` (`fused_ok`), then `csub`. -/
theorem mulCore_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 32 ≤ 8192) (hb : bb + 32 ≤ 8192) (ho : o + 32 ≤ 8192) (_hdb : Apart bb)
    (hB : d4 s.mem (W + BitVec.ofNat 64 bb) < P) :
    WP isa mulCore s fun s' =>
      d4 s'.mem (W + BitVec.ofNat 64 o) < P ∧
      d4 s'.mem (W + BitVec.ofNat 64 o) * 2 ^ 256 % P =
        d4 s.mem (W + BitVec.ofNat 64 a) * d4 s.mem (W + BitVec.ofNat 64 bb) % P ∧
      Frame (mulW W o) s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e4 : ∀ x, w4 s.mem (W + BitVec.ofNat 64 x) = d4 s.mem (W + BitVec.ofNat 64 x) := fun x => by
    simp only [w4, d4]; omega
  refine WP.block_append (WP.mono (fused_ok h5 h4 ⟨al8 hw.al hb8, hw.inR hb⟩ ⟨al8 hw.al ha8, hw.inR ha⟩)
    fun s1 ⟨⟨Q, hQ, hv⟩, k1⟩ => ?_)
  rw [e4, e4] at hv
  have hw1 : WsAt W s1 := hw.of_rest (VG.Proof.X448.RISCV64.R64.Keeps.rest k1) (by decide)
  have hlt : d4 s.mem (W + BitVec.ofNat 64 bb) * d4 s.mem (W + BitVec.ofNat 64 a) < 2 ^ 256 * P :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hB (Nat.le_of_lt (d4_lt _ _)) (by decide))
      (by rw [Nat.mul_comm])
  have hx : v4 s1 X0 X1 X2 X3 + 2 ^ 256 * (s1.gpr XC).toNat < 2 * P := by
    simp only [v4, X0, X1, X2, X3, XC]
    simp only [rv] at hv
    generalize (s1.gpr .a1).toNat + 2 ^ 64 * (s1.gpr .t3).toNat + 2 ^ 128 * (s1.gpr .t4).toNat +
      2 ^ 192 * (s1.gpr .t5).toNat + 2 ^ 256 * (s1.gpr .a2).toNat = x at hv ⊢
    have h1 : Q * P < 2 ^ 256 * P := Nat.mul_lt_mul_of_pos_right hQ P_pos
    have h2 : x * 2 ^ 256 < 2 * P * 2 ^ 256 := by
      rw [hv]
      calc _ < 2 ^ 256 * P + 2 ^ 256 * P := Nat.add_lt_add hlt h1
        _ = 2 * P * 2 ^ 256 := by rw [← Nat.two_mul, Nat.mul_comm (2 ^ 256) P, Nat.mul_assoc]
    exact Nat.lt_of_mul_lt_mul_right h2
  have hc : (s1.gpr XC).toNat ≤ 1 := by
    simp only [v4] at hx
    unfold P at hx
    omega
  refine WP.mono (csub_ok (O := W + BitVec.ofNat 64 o) (by rw [k1.1 _ (by decide), h2])
    (al8 hw.al ho8) (hw1.inW ho) hc hx) fun s2 ⟨v2, f2, g2, rd2, wr2, sp2⟩ => ?_
  have hm1 : s1.mem = s.mem := k1.2.1
  rw [hm1] at f2
  refine ⟨by rw [v2]; exact Nat.mod_lt _ P_pos, ?_, f2.mono (by simp), fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [v2, Nat.mod_mul_mod]
    simp only [v4, X0, X1, X2, X3, XC]
    simp only [rv] at hv
    rw [hv, Nat.add_mul_mod_self_right, Nat.mul_comm]
  · have sC : ∀ x ∈ clobC, x ∈ clobM := by decide
    have sK : ∀ x ∈ [Reg.t0, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a4, .a5, .a6, .a7], x ∈ clobM := by decide
    rw [g2 r (fun h => hr (sC r h)), k1.1 r (fun h => hr (sK r h))]
  · rw [rd2, k1.2.2.1]
  · rw [wr2, k1.2.2.2.1]
  · rw [sp2, k1.2.2.2.2]

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

theorem lo_eq {s : State} {r : Reg} (h : (s.gpr r).toNat < 2 ^ 32) : lo s r = (s.gpr r).toNat := by
  show ((s.gpr r).setWidth 32).toNat = _
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]

/-- A register below `2³²` is its low word. -/
theorem gpr_lo {s : State} {r : Reg} (h : (s.gpr r).toNat < 2 ^ 32) : s.gpr r = BitVec.ofNat 64 (lo s r) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, lo_eq h, Nat.mod_eq_of_lt (by omega)]

/-- `t2`, `t4`, `t5` and `a3` from offsets below `2³²` (`ptrsA`). -/
theorem ptrsA_ok {W : Addr} {s : State} (h0 : s.gpr .a0 = W) (h1 : (s.gpr .a1).toNat < 2 ^ 32)
    (h2 : (s.gpr .a2).toNat < 2 ^ 32) (h3 : (s.gpr .a3).toNat < 2 ^ 32) :
    WP isa (.block ptrsA) s fun t =>
      t.gpr .t2 = W + BitVec.ofNat 64 (lo s .a1) ∧ t.gpr .t4 = W + BitVec.ofNat 64 (lo s .a2) ∧
      t.gpr .t5 = W + BitVec.ofNat 64 (lo s .a3) ∧ t.gpr .a3 = W + BitVec.ofNat 64 2048 ∧
      Rest [.a3, .t2, .t4, .t5] s t ∧ t.mem = s.mem := by
  simp only [ptrsA]
  refine wp_add fun s7 u7 => wp_add fun s8 u8 => wp_add fun s9 u9 => wp_addi (by decide) fun s10 u10 =>
    wp_addi (by decide) fun s11 u11 => WP.block_nil ?_
  have g : ∀ r, r ≠ .a3 → s11.gpr r = s9.gpr r := fun r h => by rw [u11.other _ h, u10.other _ h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.gpr, h0, ← gpr_lo h1]
  · rw [g _ (by decide), u9.other _ (by decide), u8.gpr, u7.other _ (by decide), u7.other .a2 (by decide), h0,
      ← gpr_lo h2]
  · rw [g _ (by decide), u9.gpr, u8.other _ (by decide), u8.other .a3 (by decide), u7.other _ (by decide),
      u7.other .a3 (by decide), h0, ← gpr_lo h3]
  · rw [u11.gpr, u10.gpr, u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), h0,
      BitVec.add_assoc]
    rfl
  · exact (u7.rest (by decide)).trans ((u8.rest (by decide)).trans ((u9.rest (by decide)).trans
      ((u10.rest (by decide)).trans (u11.rest (by decide)))))
  · rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem]

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

/-- `fnA core`, from the working space at `W` and offsets below its own
working space that are zero-extended multiples of 8. -/
theorem fnA_ok {core : Prog isa} {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop}
    (hcore : CoreOk core pre res) {W : Addr} {s : State} (h0 : s.gpr .a0 = W) (hal : W.toNat % 8 = 0)
    (hwr : (⟨W, 8192⟩ : Region) ∈ s.wr) (hfit : W.toNat + 8192 ≤ 2 ^ 64)
    (ho : lo s .a1 + 32 ≤ 3840) (ha : lo s .a2 + 32 ≤ 3840) (hb : lo s .a3 + 32 ≤ 3840)
    (h1 : (s.gpr .a1).toNat < 2 ^ 32 ∧ (s.gpr .a1).toNat % 8 = 0)
    (h2 : (s.gpr .a2).toNat < 2 ^ 32 ∧ (s.gpr .a2).toNat % 8 = 0)
    (h3 : (s.gpr .a3).toNat < 2 ^ 32 ∧ (s.gpr .a3).toNat % 8 = 0)
    (hpre : pre (d4 s.mem (W + BitVec.ofNat 64 (lo s .a2))) (d4 s.mem (W + BitVec.ofNat 64 (lo s .a3)))) :
    WP isa (fnA core) s fun s' =>
      res (d4 s.mem (W + BitVec.ofNat 64 (lo s .a2))) (d4 s.mem (W + BitVec.ofNat 64 (lo s .a3)))
        (d4 s'.mem (W + BitVec.ofNat 64 (lo s .a1))) ∧
      Frame (fnW W (lo s .a1)) s.mem s'.mem ∧ (∀ r, r ∉ clobF → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold fnA
  refine WP.seq (WP.mono (ptrsA_ok h0 h1.1 h2.1 h3.1) fun s1 ⟨p2, p4, p5, p3, r1, m1⟩ => ?_)
  have hw1 : WsAt W s1 := ⟨hal, by rw [r1.wr]; exact hwr, hfit, p3⟩
  have sub1 : ∀ x ∈ [Reg.a3, .t2, .t4, .t5], x ∈ clobF := by decide
  have subM : ∀ x ∈ clobM, x ∈ clobF := by decide
  have al : ∀ r, (s.gpr r).toNat < 2 ^ 32 ∧ (s.gpr r).toNat % 8 = 0 → lo s r % 8 = 0 := fun r hr => by
    rw [lo_eq hr.1]; exact hr.2
  refine WP.mono (hcore hw1 p4 p5 p2 (al _ h2) (al _ h3) (al _ h1) (by omega) (by omega) (by omega)
    (.inl (by omega)) (by rw [m1]; exact hpre)) fun s2 ⟨v2, f2, g2, rd2, wr2, sp2⟩ =>
      ⟨by rw [← m1]; exact v2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← m1]; exact mulW_fnW W _ f2
  · intro r hr
    rw [g2 r (fun h => hr (subM r h)), r1.gpr r (fun h => hr (sub1 r h))]
  · rw [rd2, r1.rd]
  · rw [wr2, r1.wr]
  · rw [sp2, r1.sp]

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
