module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P384Field
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Spec.P384
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Mul
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Fn
public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words

/-!
# P-384's field on RISC-V: the functions

`fn core` (`Impl/Weierstrass/RISCV64/P384Field.lean`) from a state with the
working space at `W` in `a0` and the offsets' low words in `a1`–`a3`
(`fn_ok`), as P-256's (`Proof/Weierstrass/RISCV64/P256Field/Fn.lean`).
-/

@[expose] public section

/-!
## P-384's field on RISC-V: the words of a round of the reduction

The blocks of a round of `reduce` (`Impl/Weierstrass/RISCV64/P384Field.lean`),
as sums of numbers (`toNat`) that change only the registers they write
(`Keeps`):

* `qq_ok`: the quotient word `q = w + (w << 32) mod 2⁶⁴` of `w`, for which
  `q m ≡ w (mod 2⁶⁴)` (`q_low`, `m = 2³⁸⁴ - p`);
* `qm_ok`: the three words of `q m / 2⁶⁴` (`qm_nat`);
* `chain_ok`: those three words and the borrow of the round before taken out
  of the next three words, with the borrow out.
-/

namespace VG.Proof.Weierstrass.RISCV64.P384Field

open VG VG.RISCV64 VG.RISCV64.Wide
open VG.Proof.Weierstrass.RISCV64.P256Field (sltu_toNat upd_keeps)

/-- P-384's prime. -/
abbrev P : Nat := Spec.P384.p

/-- `2³⁸⁴ - p`. -/
abbrev Mc : Nat := 2 ^ 128 + 2 ^ 96 - 2 ^ 32 + 1

theorem P_add_Mc : P + Mc = 2 ^ 384 := by unfold P Spec.P384.p Mc; omega

/-- The quotient word of `w`: `q m ≡ w (mod 2⁶⁴)`. -/
theorem q_low {r : Nat} (hr : r < 2 ^ 64) : (r + r * 2 ^ 32 % 2 ^ 64) % 2 ^ 64 * Mc % 2 ^ 64 = r := by
  simp only [Mc]; omega

/-- The words of `qm`: with `q 2³² = l + 2⁶⁴ h`, `c₀ = [q < l]` and the borrow
`b` of `l - (h + c₀)`, `q m` is its low word plus `2⁶⁴` times
`(l - h - c₀ mod 2⁶⁴) + 2⁶⁴ (h - b + q)`. -/
theorem qm_nat {q lo hi c0 b d0 d1 d2 : Nat} (hq : q < 2 ^ 64) (hl : lo + 2 ^ 64 * hi = q * 2 ^ 32)
    (hlo : lo < 2 ^ 64)
    (hc0 : c0 = if q < lo then 1 else 0) (hb : b = if lo < hi + c0 then 1 else 0)
    (hd0 : d0 = (lo + 2 ^ 64 - (hi + c0)) % 2 ^ 64) (hd1 : d1 = ((hi + 2 ^ 64 - b) % 2 ^ 64 + q) % 2 ^ 64)
    (hd2 : d2 = if d1 < q then 1 else 0) :
    (q + 2 ^ 64 * c0 - lo) + 2 ^ 64 * (d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2) = q * Mc ∧
      q + 2 ^ 64 * c0 - lo < 2 ^ 64 ∧ d2 ≤ 1 := by
  have hh : hi < 2 ^ 32 := by omega
  have f0 : (c0 = 1 ∧ q < lo) ∨ (c0 = 0 ∧ lo ≤ q) := by subst hc0; split <;> omega
  have f1 : (b = 1 ∧ lo < hi + c0) ∨ (b = 0 ∧ hi + c0 ≤ lo) := by subst hb; split <;> omega
  have hbh : b ≤ hi := by omega
  have g0 : d0 + hi + c0 = lo + 2 ^ 64 * b := by subst hd0; omega
  have g1 : d1 + 2 ^ 64 * d2 = hi - b + q ∧ d2 ≤ 1 := by
    have : (hi + 2 ^ 64 - b) % 2 ^ 64 = hi - b := by omega
    subst hd2 hd1; rw [this]; split <;> omega
  clear hc0 hb hd0 hd1 hd2 f1
  simp only [Mc]
  omega

variable {s : State}

set_option linter.unusedSimpArgs false in
/-- `q = w + (w << 32)` in `r`, through `t0`. -/
theorem qq_ok {r : Reg} (h0 : r ≠ .t0 := by decide) :
    WP isa (.block [.shift .sll .d .t0 r 32, .add r r .t0]) s fun s' =>
      (s'.gpr r).toNat = ((s.gpr r).toNat + (s.gpr r).toNat * 2 ^ 32 % 2 ^ 64) % 2 ^ 64 ∧
      Keeps [.t0, r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add,
    exec_shift_d (show 32 < 64 by decide), RegUpd.gpr_write, h0, Ne.symm h0, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r' hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- `qm r`: `a4 + 2⁶⁴ a5 + 2¹²⁸ a6 = q m / 2⁶⁴` for `q` in `r`, with `a6 ≤ 1`. -/
theorem qm_ok {r : Reg} (h4 : r ≠ .a4 := by decide) (h5 : r ≠ .a5 := by decide)
    (h6 : r ≠ .a6 := by decide) (h7 : r ≠ .a7 := by decide) :
    WP isa (.block (Impl.Weierstrass.RISCV64.P384Field.qm r)) s fun s' =>
      (s'.gpr .a4).toNat + 2 ^ 64 * (s'.gpr .a5).toNat + 2 ^ 128 * (s'.gpr .a6).toNat =
        (s.gpr r).toNat * Mc / 2 ^ 64 ∧ (s'.gpr .a6).toNat ≤ 1 ∧
      Keeps [.a4, .a5, .a6, .a7] s s' := by
  unfold Impl.Weierstrass.RISCV64.P384Field.qm
  refine Steps.wp_sll (by decide) fun s1 u1 => Steps.wp_srl (by decide) fun s2 u2 =>
    Steps.wp_sltu fun s3 u3 => Steps.wp_add fun s4 u4 => Steps.wp_sltu fun s5 u5 =>
    Steps.wp_sub fun s6 u6 => Steps.wp_sub fun s7 u7 => Steps.wp_add fun s8 u8 =>
    Steps.wp_sltu fun s9 u9 => WP.block_nil ?_
  -- `q` through the steps.
  have q1 : s1.gpr r = s.gpr r := u1.other _ h4
  have q2 : s2.gpr r = s.gpr r := by rw [u2.other _ h5, q1]
  have q3 : s3.gpr r = s.gpr r := by rw [u3.other _ h6, q2]
  have q4 : s4.gpr r = s.gpr r := by rw [u4.other _ h6, q3]
  have q5 : s5.gpr r = s.gpr r := by rw [u5.other _ h7, q4]
  have q6 : s6.gpr r = s.gpr r := by rw [u6.other _ h4, q5]
  have q7 : s7.gpr r = s.gpr r := by rw [u7.other _ h5, q6]
  -- The values of the steps.
  have lo2 : s2.gpr .a4 = s.gpr r <<< 32 := by rw [u2.other _ (by decide), u1.gpr]
  have lo4 : s4.gpr .a4 = s.gpr r <<< 32 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), lo2]
  have hi3 : s3.gpr .a5 = s.gpr r >>> 32 := by rw [u3.other _ (by decide), u2.gpr, q1]
  have c3 : s3.gpr .a6 = if s.gpr r < s.gpr r <<< 32 then (1 : BitVec 64) else 0 := by rw [u3.gpr, q2, lo2]
  have hc4 : s4.gpr .a6 = (if s.gpr r < s.gpr r <<< 32 then (1 : BitVec 64) else 0) + s.gpr r >>> 32 := by
    rw [u4.gpr, c3, hi3]
  have b5 : s5.gpr .a7 = if s.gpr r <<< 32 < s4.gpr .a6 then (1 : BitVec 64) else 0 := by rw [u5.gpr, lo4]
  have d6 : s6.gpr .a4 = s.gpr r <<< 32 - s4.gpr .a6 := by
    rw [u6.gpr, u5.other _ (by decide), lo4, u5.other _ (by decide)]
  have hi5 : s5.gpr .a5 = s.gpr r >>> 32 := by
    rw [u5.other _ (by decide), u4.other _ (by decide), hi3]
  have e7 : s7.gpr .a5 = s.gpr r >>> 32 - s5.gpr .a7 := by
    rw [u7.gpr, u6.other _ (by decide), hi5, u6.other _ (by decide)]
  have e8 : s8.gpr .a5 = (s.gpr r >>> 32 - s5.gpr .a7) + s.gpr r := by rw [u8.gpr, e7, q7]
  have e9 : s9.gpr .a6 = if s8.gpr .a5 < s.gpr r then (1 : BitVec 64) else 0 := by
    rw [u9.gpr, u8.other _ h5, q7]
  have f4 : s9.gpr .a4 = s6.gpr .a4 := by
    rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide)]
  have f5 : s9.gpr .a5 = s8.gpr .a5 := u9.other _ (by decide)
  have hq := (s.gpr r).isLt
  have hsr : (s.gpr r >>> 32).toNat = (s.gpr r).toNat * 2 ^ 32 / 2 ^ 64 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  have hsl : (s.gpr r <<< 32).toNat = (s.gpr r).toNat * 2 ^ 32 % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hc0 := sltu_toNat (s.gpr r) (s.gpr r <<< 32)
  have hcl : (if s.gpr r < s.gpr r <<< 32 then (1 : BitVec 64) else 0).toNat ≤ 1 := by
    rw [hc0]; split <;> omega
  have hHC : (s4.gpr .a6).toNat =
      (if s.gpr r < s.gpr r <<< 32 then (1 : BitVec 64) else 0).toNat + (s.gpr r >>> 32).toNat := by
    rw [hc4, BitVec.toNat_add]; omega
  have hb := sltu_toNat (s.gpr r <<< 32) (s4.gpr .a6)
  rw [← b5] at hb
  have hd2 := sltu_toNat (s8.gpr .a5) (s.gpr r)
  rw [← e9] at hd2
  have k := qm_nat (q := (s.gpr r).toNat) (lo := (s.gpr r <<< 32).toNat) (hi := (s.gpr r >>> 32).toNat)
    (c0 := (if s.gpr r < s.gpr r <<< 32 then (1 : BitVec 64) else 0).toNat) (b := (s5.gpr .a7).toNat)
    (d0 := (s6.gpr .a4).toNat) (d1 := (s8.gpr .a5).toNat) (d2 := (s9.gpr .a6).toNat) hq
    (by rw [hsl, hsr]; omega) (BitVec.isLt _) hc0 (by rw [hb, hHC, Nat.add_comm (BitVec.toNat _)])
    (by rw [d6, BitVec.toNat_sub, hHC]; omega)
    (by rw [e8, BitVec.toNat_add, BitVec.toNat_sub]; omega) hd2
  refine ⟨?_, k.2.2, ?_⟩
  · rw [f4, f5]
    rw [← k.1]
    have := k.2.1
    omega
  · have := (((((((((upd_keeps u1).trans (upd_keeps u2)).trans (upd_keeps u3)).trans (upd_keeps u4)).trans
      (upd_keeps u5)).trans (upd_keeps u6)).trans (upd_keeps u7)).trans (upd_keeps u8)).trans (upd_keeps u9))
    refine this.mono fun r' hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h | h | h | h | h <;> simp [h]

set_option linter.unusedSimpArgs false in
/-- `d := d - y` and its borrow into `c` (`d' + y = d + 2⁶⁴ c`). -/
theorem sbb0_ok {d y c : Reg} (hdc : d ≠ c := by decide) (hcy : c ≠ y := by decide) :
    WP isa (.block [.sltu c d y, .sub d d y]) s fun s' =>
      (s'.gpr d).toNat + (s.gpr y).toNat = (s.gpr d).toNat + 2 ^ 64 * (s'.gpr c).toNat ∧
      (s'.gpr c).toNat ≤ 1 ∧ Keeps [d, c] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_sub, exec_sltu,
    RegUpd.gpr_write, hdc, hcy, Ne.symm hdc, Ne.symm hcy, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have := VG.Proof.Weierstrass.RISCV64.P256Field.sub_borrow (s.gpr d) (s.gpr y)
    rw [sltu_toNat]; exact this
  · rw [sltu_toNat]; split <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

set_option linter.unusedSimpArgs false in
/-- `x := x - (y + c + k)` and its borrow into `c`, through `y`, for `y + c + k`
below `2⁶⁴`. -/
theorem subTop_ok {x y c k : Reg} (hxy : x ≠ y := by decide) (hxc : x ≠ c := by decide)
    (hyc : y ≠ c := by decide) (hyk : y ≠ k := by decide) :
    WP isa (.block [.add y y c, .add y y k, .sltu c x y, .sub x x y]) s fun s' =>
      ((s.gpr y).toNat + (s.gpr c).toNat + (s.gpr k).toNat < 2 ^ 64 →
        (s'.gpr x).toNat + ((s.gpr y).toNat + (s.gpr c).toNat + (s.gpr k).toNat) =
          (s.gpr x).toNat + 2 ^ 64 * (s'.gpr c).toNat) ∧
      (s'.gpr c).toNat ≤ 1 ∧ Keeps [y, c, x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sub, exec_sltu,
    RegUpd.gpr_write, hxy, hxc, hyc, hyk, Ne.symm hxy, Ne.symm hxc, Ne.symm hyc,
    Ne.symm hyk, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun hb => ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have e : (s.gpr y + s.gpr c + s.gpr k).toNat = (s.gpr y).toNat + (s.gpr c).toNat + (s.gpr k).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_add]; omega
    have := VG.Proof.Weierstrass.RISCV64.P256Field.sub_borrow (s.gpr x) (s.gpr y + s.gpr c + s.gpr k)
    rw [sltu_toNat, ← e]; exact this
  · rw [sltu_toNat]; split <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.Weierstrass.RISCV64.P384Field

/-!
## P-384's field on RISC-V: Montgomery's reduction

`reduce` reduces the twelve words `T` at `ACC`: after round `i`, the
registers `rw i`–`rw (i + 2)` and the words of `T` from `i + 3` on, as a
number `wv i`, less the borrow `a2` at word `i + 3`, plus `Q m` for the
quotient words `Q` stored below `ACC + 8i`, are `T / 2^(64 i)` (`RedInv`):
a round subtracts `q m` for the quotient word `q` of the low word, whose low
word that is (`round_ok`). After six rounds `finish` takes the borrow out of
the top words and adds `Q`, which leaves `X` with `X 2³⁸⁴ = T + Q p`
(`reduce_ok`).
-/

namespace VG.Proof.Weierstrass.RISCV64.P384Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P384Field
open VG.Proof.X25519.RISCV64 (Ctx Rest)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok clob64 Keeps.rest dw_write_self dw_write_other colsV
  colsV_add)
open VG.Proof.X25519.RISCV64.R64 (accW accW_lt accW_congr accW_eq)
open VG.Proof.Weierstrass.RISCV64.P256Field (adc_ok sbb_ok sltu_le upd_keeps)

/-- Word `j` of the product at `ACC`. -/
abbrev T (m : Mem) (b : Addr) (j : Nat) : Nat := dw m b (ACC + 8 * j)

/-- The `n` words of the product from word `j`. -/
def upW (m : Mem) (b : Addr) (j : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => T m b j + 2 ^ 64 * upW m b (j + 1) n

/-- The product's twelve words. -/
abbrev prodV (m : Mem) (b : Addr) : Nat := upW m b 0 12

/-- The number after round `i - 1`: the registers and the words of the
product not yet loaded. -/
def wv (m : Mem) (b : Addr) (i : Nat) (s : State) : Nat :=
  (s.gpr (rw i)).toNat + 2 ^ 64 * (s.gpr (rw (i + 1))).toNat + 2 ^ 128 * (s.gpr (rw (i + 2))).toNat +
    2 ^ 192 * upW m b (i + 3) (9 - i)

/-- After `i` rounds, from `s0`. -/
structure RedInv (b : Addr) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob64 s0 s
  frame : Frame [AR ACC b] s0.mem s.mem
  hi : ∀ j, i + 3 ≤ j → j < 12 → dw s.mem b (ACC + 8 * j) = T s0.mem b j
  cy : (s.gpr .a2).toNat ≤ 1
  val : wv s0.mem b i s * 2 ^ (64 * i) + accW ACC s.mem b i * Mc =
    prodV s0.mem b + 2 ^ 192 * (s.gpr .a2).toNat * 2 ^ (64 * i)

/-- The registers of a round. -/
theorem rw_facts : ∀ i < 6,
    rw i ≠ rw (i + 1) ∧ rw i ≠ rw (i + 2) ∧ rw i ≠ rw (i + 3) ∧
    rw (i + 1) ≠ rw (i + 2) ∧ rw (i + 1) ≠ rw (i + 3) ∧ rw (i + 2) ≠ rw (i + 3) ∧
    (∀ k < 4, rw (i + k) ≠ .a2 ∧ rw (i + k) ≠ .a4 ∧ rw (i + k) ≠ .a5 ∧ rw (i + k) ≠ .a6 ∧
      rw (i + k) ≠ .a7 ∧ rw (i + k) ≠ .t0 ∧ rw (i + k) ≠ .a3 ∧ rw (i + k) ∈ clob64) := by
  intro i hi
  obtain rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  all_goals decide

/-- Round `i`. -/
theorem round_ok {b : Addr} {s0 : State} {i : Nat} (hi : i < 6) {s : State} (h : RedInv b s0 i s) :
    WP isa (.block (round i)) s (RedInv b s0 (i + 1)) := by
  obtain ⟨d01, d02, d03, d12, d13, d23, dk⟩ := rw_facts i hi
  obtain ⟨n02, n04, n05, n06, n07, n0t, n03, c0⟩ := dk 0 (by decide)
  obtain ⟨n12, n14, n15, n16, n17, n1t, n13, c1⟩ := dk 1 (by decide)
  obtain ⟨n22, n24, n25, n26, n27, n2t, n23, c2⟩ := dk 2 (by decide)
  obtain ⟨n32, n34, n35, n36, n37, n3t, n33, c3⟩ := dk 3 (by decide)
  simp only [Nat.add_zero] at n02 n04 n05 n06 n07 n0t n03 c0
  have hc := h.ctx
  have e : round i = .load .d (rw (i + 3)) .a3 (ACC + 8 * (i + 3)) ::
      ([.shift .sll .d .t0 (rw i) 32, .add (rw i) (rw i) .t0] ++
      (.store .d (rw i) .a3 (ACC + 8 * i) :: (qm (rw i) ++
      ([.sltu .a7 (rw (i + 1)) .a4, .sub (rw (i + 1)) (rw (i + 1)) .a4] ++
      ([.sltu .t0 (rw (i + 2)) .a5, .sub (rw (i + 2)) (rw (i + 2)) .a5, .sltu .a4 (rw (i + 2)) .a7,
        .sub (rw (i + 2)) (rw (i + 2)) .a7, .add .a7 .t0 .a4] ++
      [.add .a6 .a6 .a2, .add .a6 .a6 .a7, .sltu .a2 (rw (i + 3)) .a6,
        .sub (rw (i + 3)) (rw (i + 3)) .a6]))))) := by
    simp only [round, List.cons_append, List.nil_append]
  rw [e]
  refine ld_ok hc (by simp only [ACC]; omega) (by simp only [ACC]; omega) fun s1 u1 => ?_
  have hT3 : (s1.gpr (rw (i + 3))).toNat = T s0.mem b (i + 3) := by
    rw [u1.gpr]; exact h.hi (i + 3) (by omega) (by omega)
  refine WP.block_append (WP.mono (qq_ok (r := rw i) n0t) fun s2 ⟨e2, k2⟩ => ?_)
  have hc2 : Ctx b s2 := hc.of_rest ((u1.rest (ws := clob64) c3).trans ((Keeps.rest k2).mono
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl; exacts [by decide, c0]))) (by decide)
  refine sd_ok hc2 (by simp only [ACC]; omega) (by simp only [ACC]; omega) fun s3 u3 => ?_
  refine WP.block_append (WP.mono (qm_ok (r := rw i) n04 n05 n06 n07) fun s4 ⟨e4, l4, k4⟩ => ?_)
  refine WP.block_append (WP.mono (sbb0_ok (d := rw (i + 1)) (y := .a4) (c := .a7) n17 (by decide))
    fun s5 ⟨e5, l5, k5⟩ => ?_)
  refine WP.block_append (WP.mono (sbb_ok (d := rw (i + 2)) (x := rw (i + 2)) (y := .a5) (c := .a7)
    (u := .t0) (v := .a4) n27 (Ne.symm n2t) (by decide) (Ne.symm n24) (by decide) (by decide)
    (Ne.symm n2t) (by decide)) fun s6 ⟨e6, k6⟩ => ?_)
  refine WP.mono (subTop_ok (x := rw (i + 3)) (y := .a6) (c := .a2) (k := .a7) n36 n32 (by decide)
    (by decide)) fun s7 ⟨e7, l7, k7⟩ => ?_
  -- Registers read by each step, through the steps before it.
  have r0 : s1.gpr (rw i) = s.gpr (rw i) := u1.other _ d03
  have q3 : s3.gpr (rw i) = s2.gpr (rw i) := by rw [u3.gpr]
  have r1 : s4.gpr (rw (i + 1)) = s.gpr (rw (i + 1)) := by
    rw [k4.1 _ (by simp [n14, n15, n16, n17]), u3.gpr, k2.1 _ (by simp [n1t, Ne.symm d01]),
      u1.other _ d13]
  have a44 : s5.gpr .a4 = s4.gpr .a4 := k5.1 _ (by simp [Ne.symm n14])
  have r2 : s5.gpr (rw (i + 2)) = s.gpr (rw (i + 2)) := by
    rw [k5.1 _ (by simp [Ne.symm d12, n27]), k4.1 _ (by simp [n24, n25, n26, n27]), u3.gpr,
      k2.1 _ (by simp [n2t, Ne.symm d02]), u1.other _ d23]
  have a55 : s5.gpr .a5 = s4.gpr .a5 := k5.1 _ (by simp [Ne.symm n15])
  have r3 : s6.gpr (rw (i + 3)) = s1.gpr (rw (i + 3)) := by
    rw [k6.1 _ (by simp [Ne.symm d23, n3t, n34, n37]), k5.1 _ (by simp [Ne.symm d13, n37]),
      k4.1 _ (by simp [n34, n35, n36, n37]), u3.gpr, k2.1 _ (by simp [n3t, Ne.symm d03])]
  have a66 : s6.gpr .a6 = s4.gpr .a6 := by
    rw [k6.1 _ (by simp [Ne.symm n26]), k5.1 _ (by simp [Ne.symm n16])]
  have a22 : s6.gpr .a2 = s.gpr .a2 := by
    rw [k6.1 _ (by simp [Ne.symm n22]), k5.1 _ (by simp [Ne.symm n12]),
      k4.1 _ (by decide), u3.gpr, k2.1 _ (by simp [Ne.symm n02]), u1.other _ (Ne.symm n32)]
  -- The new registers, read from the last state.
  have o1 : s7.gpr (rw (i + 1)) = s5.gpr (rw (i + 1)) := by
    rw [k7.1 _ (by simp [n16, n12, d13]), k6.1 _ (by simp [d12, n1t, n14, n17])]
  have o2 : s7.gpr (rw (i + 2)) = s6.gpr (rw (i + 2)) := k7.1 _ (by simp [n26, n22, d23])
  rw [r1] at e5
  rw [r2, a55] at e6
  rw [r3, hT3, a66, a22] at e7
  have hcy := h.cy
  have e6' := e6 l5
  -- The quotient word.
  have hq : (s2.gpr (rw i)).toNat * Mc =
      (s.gpr (rw i)).toNat + 2 ^ 64 * ((s4.gpr .a4).toNat + 2 ^ 64 * (s4.gpr .a5).toNat +
        2 ^ 128 * (s4.gpr .a6).toNat) := by
    rw [q3] at e4
    have hl : (s2.gpr (rw i)).toNat * Mc % 2 ^ 64 = (s.gpr (rw i)).toNat := by
      rw [e2, r0]; exact q_low (s.gpr (rw i)).isLt
    have := Nat.mod_add_div ((s2.gpr (rw i)).toNat * Mc) (2 ^ 64)
    rw [e4]
    omega
  have b4 := (s4.gpr .a4).isLt
  have b5 := (s4.gpr .a5).isLt
  have e7' := e7 (by omega)
  -- The memory.
  have hm7 : s7.mem = s.mem.writeW (b + BitVec.ofNat 64 (ACC + 8 * i)) (s2.gpr (rw i)) := by
    rw [k7.2.1, k6.2.1, k5.2.1, k4.2.1, u3.mem, k2.2.1, u1.mem]
  have hrest : Rest clob64 s s7 :=
    (u1.rest c3).trans ((Keeps.rest k2).mono (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl; exacts [by decide, c0]) |>.trans ((u3.rest _).trans
      ((Keeps.rest k4).mono (by decide) |>.trans ((Keeps.rest k5).mono (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl; exacts [c1, by decide]) |>.trans ((Keeps.rest k6).mono (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl; exacts [c2, by decide, by decide, by decide]) |>.trans
        ((Keeps.rest k7).mono (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl; exacts [by decide, by decide, c3])))))))
  have hup : upW s0.mem b (i + 3) (9 - i) = T s0.mem b (i + 3) + 2 ^ 64 * upW s0.mem b (i + 4) (8 - i) := by
    rw [show 9 - i = (8 - i) + 1 by omega]; rfl
  have hacc : accW ACC s7.mem b (i + 1) = accW ACC s.mem b i + (2 ^ 64) ^ i * (s2.gpr (rw i)).toNat := by
    have ha : accW ACC (s.mem.writeW (b + BitVec.ofNat 64 (ACC + 8 * i)) (s2.gpr (rw i))) b i =
        accW ACC s.mem b i := accW_congr fun c hc' => by
      rw [dw_write_other _ _ _ (by omega) (by simp only [ACC]; omega) (by simp only [ACC]; omega)]
    rw [accW, hm7, ha, dw_write_self]
  have key : 2 ^ 64 * wv s0.mem b (i + 1) s7 + (s2.gpr (rw i)).toNat * Mc + 2 ^ 192 * (s.gpr .a2).toNat =
      wv s0.mem b i s + 2 ^ 256 * (s7.gpr .a2).toNat := by
    simp only [wv, show i + 1 + 1 = i + 2 by omega, show i + 1 + 2 = i + 3 by omega,
      show i + 1 + 3 = i + 4 by omega, show 9 - (i + 1) = 8 - i by omega, hup, o1, o2, hq]
    omega
  refine ⟨hc.of_rest hrest (by decide), h.rest.trans hrest, ?_, fun j hj hj' => ?_, l7, ?_⟩
  · rw [hm7]
    exact h.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains b (by simp only [ACC]; omega) (by simp only [ACC]; omega) (by simp only [ACC]; omega))
  · rw [hm7, dw_write_other _ _ _ (by omega) (by simp only [ACC]; omega) (by simp only [ACC]; omega)]
    exact h.hi j (by omega) hj'
  · have hv := h.val
    rw [hacc, show 64 * (i + 1) = 64 * i + 64 by omega, Nat.pow_add, Nat.pow_mul]
    rw [Nat.pow_mul] at hv
    generalize (2 ^ 64) ^ i = E at *
    generalize wv s0.mem b (i + 1) s7 = W' at *
    generalize wv s0.mem b i s = W at *
    generalize (s2.gpr (rw i)).toNat = q at *
    generalize prodV s0.mem b = Pr at *
    generalize accW ACC s.mem b i = A at *
    generalize (s7.gpr .a2).toNat = β' at *
    generalize (s.gpr .a2).toNat = β at *
    generalize Mc = M at *
    grind

/-- The rounds, by induction. -/
theorem rounds_ok {b : Addr} {s0 : State} : ∀ n ≤ 6, ∀ s, RedInv b s0 0 s →
    WP isa (.block ((List.range n).flatMap round)) s (RedInv b s0 n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (rounds_ok n (by omega) s h) fun s1 h1 => round_ok (by omega) h1)

/-- The initial loads. -/
theorem loads_ok {b : Addr} {s : State} (hc : Ctx b s) :
    WP isa (.block ((List.range 3).map (fun j => .load .d (rw j) .a3 (ACC + 8 * j)) ++ ([.li .a2 0] : List Instr))) s
      (RedInv b s 0) := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  refine ld_ok hc (by unfold ACC; omega) (by unfold ACC; omega) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := clob64) (by decide)) (by decide)
  refine ld_ok hc1 (by unfold ACC; omega) (by unfold ACC; omega) fun s2 u2 => ?_
  have hc2 : Ctx b s2 := hc1.of_rest (u2.rest (ws := clob64) (by decide)) (by decide)
  refine ld_ok hc2 (by unfold ACC; omega) (by unfold ACC; omega) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := hc2.of_rest (u3.rest (ws := clob64) (by decide)) (by decide)
  refine wp_li (by decide) fun s4 u4 => WP.block_nil ?_
  have hr : Rest clob64 s s4 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    ((u3.rest (by decide)).trans (u4.rest (by decide))))
  have hm : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have w0 : (s4.gpr (rw 0)).toNat = T s.mem b 0 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; rfl
  have w1 : (s4.gpr (rw 1)).toNat = T s.mem b 1 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.mem]; rfl
  have w2 : (s4.gpr (rw 2)).toNat = T s.mem b 2 := by
    rw [u4.other _ (by decide), u3.gpr, u2.mem, u1.mem]; rfl
  have wc : (s4.gpr .a2).toNat = 0 := by rw [u4.gpr]; rfl
  refine ⟨hc3.of_rest (u4.rest (ws := clob64) (by decide)) (by decide), hr, by rw [hm]; exact Frame.refl _ _,
    fun j _ _ => by rw [hm], by rw [wc]; omega, ?_⟩
  have hp : prodV s.mem b = T s.mem b 0 + 2 ^ 64 * (T s.mem b 1 + 2 ^ 64 * (T s.mem b 2 +
      2 ^ 64 * upW s.mem b 3 9)) := rfl
  have hw : wv s.mem b 0 s4 = (s4.gpr (rw 0)).toNat + 2 ^ 64 * (s4.gpr (rw 1)).toNat +
      2 ^ 128 * (s4.gpr (rw 2)).toNat + 2 ^ 192 * upW s.mem b 3 9 := rfl
  rw [hw, hp, w0, w1, w2, wc, show accW ACC s4.mem b 0 = 0 from rfl]
  generalize upW s.mem b 3 9 = U
  omega

/-- The registers of the result. -/
theorem X_facts : ∀ j < 6, X j ≠ .a2 ∧ X j ≠ .a5 ∧ X j ≠ .a6 ∧ X j ≠ .a7 ∧ X j ≠ .t0 ∧ X j ≠ .a0 ∧
    X j ≠ .a3 ∧ X j ≠ .t2 ∧ X j ≠ .t1 ∧ X j ∈ clob64 ∧ ∀ k < 6, k ≠ j → X k ≠ X j := by decide

/-- After `j` words of the sum of the quotient words, from `s0`: the words
below `j` and the carry `a2` are the sum of `X`'s and `Q`'s below `j`. -/
structure AddQInv (b : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob64 s0 s
  mem : s.mem = s0.mem
  hi : ∀ k, j ≤ k → k < 6 → s.gpr (X k) = s0.gpr (X k)
  a5 : s.gpr .a5 = s0.gpr .a5
  cy : (s.gpr .a2).toNat ≤ 1
  val : colsV (fun k => (s.gpr (X k)).toNat) j + (2 ^ 64) ^ j * (s.gpr .a2).toNat =
    colsV (fun k => (s0.gpr (X k)).toNat + dw s0.mem b (ACC + 8 * k)) j

theorem colsV_congr {f g : Nat → Nat} : ∀ {n}, (∀ k < n, f k = g k) → colsV f n = colsV g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [colsV]; rw [colsV_congr (fun k hk => h k (by omega)), h n (by omega)]

/-- Word `j` of the sum of the quotient words. -/
theorem addQ_ok {b : Addr} {s0 : State} {j : Nat} (hj : j < 6) {s : State} (h : AddQInv b s0 j s) :
    WP isa (.block (.load .d .a7 .a3 (ACC + 8 * j) :: adcWord (X j) .a7)) s (AddQInv b s0 (j + 1)) := by
  obtain ⟨x2, x5, x6, x7, -, -, x3, -, -, xc, xne⟩ := X_facts j hj
  refine ld_ok h.ctx (by unfold ACC; omega) (by unfold ACC; omega) fun s1 u1 => ?_
  refine WP.mono (adc_ok (d := X j) (x := X j) (y := .a7) (c := .a2) (u := .a6) x7 x2 (Ne.symm x6) (by decide))
    fun s2 ⟨e2, k2⟩ => ?_
  have hr : Rest clob64 s s2 := (u1.rest (by decide)).trans ((Keeps.rest k2).mono (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl; exacts [xc, by decide, by decide]))
  have hm : s2.mem = s0.mem := by rw [k2.2.1, u1.mem, h.mem]
  have ex : s1.gpr (X j) = s0.gpr (X j) := by rw [u1.other _ x7, h.hi j (Nat.le_refl _) hj]
  have ey : (s1.gpr .a7).toNat = dw s0.mem b (ACC + 8 * j) := by rw [u1.gpr, ← h.mem]; rfl
  have ec : s1.gpr .a2 = s.gpr .a2 := u1.other _ (by decide)
  have g : ∀ k < 6, k ≠ j → s2.gpr (X k) = s.gpr (X k) := fun k hk hkj => by
    obtain ⟨y2, -, y6, y7, -⟩ := X_facts k hk
    rw [k2.1 _ (by simp [xne k hk hkj, y6, y2]), u1.other _ y7]
  have e2' := e2 (by rw [ec]; exact h.cy)
  rw [ex, ey, ec] at e2'
  refine ⟨h.ctx.of_rest hr (by decide), h.rest.trans hr, hm, fun k hk hk' => ?_, ?_, ?_, ?_⟩
  · rw [g k hk' (by omega)]; exact h.hi k (by omega) hk'
  · rw [k2.1 _ (by simp [Ne.symm x5]), u1.other _ (by decide), h.a5]
  · have := (s2.gpr (X j)).isLt
    have := (s0.gpr (X j)).isLt
    have := dw_lt s0.mem b (ACC + 8 * j)
    have := h.cy
    omega
  · have hv := h.val
    have hc : colsV (fun k => (s2.gpr (X k)).toNat) j = colsV (fun k => (s.gpr (X k)).toNat) j :=
      colsV_congr fun k hk => by rw [g k (by omega) (by omega)]
    show colsV (fun k => (s2.gpr (X k)).toNat) j + (2 ^ 64) ^ j * (s2.gpr (X j)).toNat +
        (2 ^ 64) ^ (j + 1) * (s2.gpr .a2).toNat =
      colsV (fun k => (s0.gpr (X k)).toNat + dw s0.mem b (ACC + 8 * k)) j +
        (2 ^ 64) ^ j * ((s0.gpr (X j)).toNat + dw s0.mem b (ACC + 8 * j))
    rw [hc, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ .., ← hv]
    generalize (2 ^ 64) ^ j = E at *
    generalize colsV (fun k => (s.gpr (X k)).toNat) j = C at *
    generalize (s2.gpr (X j)).toNat = x at *
    generalize (s2.gpr .a2).toNat = c' at *
    generalize (s.gpr .a2).toNat = c at *
    generalize (s0.gpr (X j)).toNat = y at *
    generalize dw s0.mem b (ACC + 8 * j) = z at *
    have key : E * x + E * 2 ^ 64 * c' = E * c + E * (y + z) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, e2', Nat.add_comm c]
    omega

theorem two384 : (2 : Nat) ^ 384 = (2 ^ 64) ^ 6 := by omega

theorem colsV_lt_of (f : Nat → Nat) (hf : ∀ k, f k < 2 ^ 64) : ∀ n, colsV f n < (2 ^ 64) ^ n
  | 0 => by simp [colsV]
  | n + 1 => by
    have := colsV_lt_of f hf n
    have := hf n
    simp only [colsV, Nat.pow_succ]
    calc colsV f n + (2 ^ 64) ^ n * f n < (2 ^ 64) ^ n + (2 ^ 64) ^ n * f n := by omega
      _ = (2 ^ 64) ^ n * (f n + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ (2 ^ 64) ^ n * 2 ^ 64 := Nat.mul_le_mul_left _ (by omega)

/-- The number of the reduction, from its carry `c` and the borrow `B`. -/
theorem fin_eq {C c B Pr QP : Nat} (hB : B ≤ c)
    (h : (C + 2 ^ 384 * c) * 2 ^ 384 = Pr + QP + 2 ^ 768 * B) :
    (C + 2 ^ 384 * (c - B)) * 2 ^ 384 = Pr + QP := by
  omega

/-- The sum of the quotient words, by induction. -/
theorem addQs_ok {b : Addr} {s0 : State} : ∀ n ≤ 6, ∀ s, AddQInv b s0 0 s →
    WP isa (.block ((List.range n).flatMap fun j => .load .d .a7 .a3 (ACC + 8 * j) :: adcWord (X j) .a7)) s
      (AddQInv b s0 n) :=
  wp_range_flatMap (M := isa) (AddQInv b s0) fun _ _ hj h => addQ_ok hj h

/-- The number of the words `X 0`–`X 5`. -/
abbrev xv (s : State) : Nat := colsV (fun k => (s.gpr (X k)).toNat) 6

/-- `reduce`: `X + 2³⁸⁴ XC` (`X 0`–`X 5` and `XC`), with `(X + 2³⁸⁴ XC) 2³⁸⁴ = T + Q p`
for some `Q < 2³⁸⁴`. -/
theorem reduce_ok {b : Addr} {s : State} (hc : Ctx b s) :
    WP isa (.block reduce) s fun s' =>
      Ctx b s' ∧ Rest clob64 s s' ∧ Frame [AR ACC b] s.mem s'.mem ∧ (s'.gpr XC).toNat ≤ 1 ∧
      ∃ Q, Q < 2 ^ 384 ∧ (xv s' + 2 ^ 384 * (s'.gpr XC).toNat) * 2 ^ 384 = prodV s.mem b + Q * P := by
  have e : reduce = ((List.range 3).map (fun j => .load .d (rw j) .a3 (ACC + 8 * j)) ++
      ([.li .a2 0] : List Instr)) ++ ((List.range 6).flatMap round ++
      (.load .d .t4 .a3 (ACC + 72) :: .load .d .a1 .a3 (ACC + 80) :: .load .d .a4 .a3 (ACC + 88) ::
      ([.sltu .a5 .t4 .a2, .sub .t4 .t4 .a2] ++ ([.sltu .a2 .a1 .a5, .sub .a1 .a1 .a5] ++
      ([.sltu .a5 .a4 .a2, .sub .a4 .a4 .a2] ++ (.li .a2 0 ::
      (((List.range 6).flatMap fun j => .load .d .a7 .a3 (ACC + 8 * j) :: adcWord (X j) .a7) ++
      [.sub XC XC .a5]))))))) := by
    unfold reduce finish
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl
  rw [e]
  refine WP.block_append (WP.mono (loads_ok hc) fun s1 h1 => ?_)
  refine WP.block_append (WP.mono (rounds_ok 6 (Nat.le_refl _) s1 h1) fun s6 h6 => ?_)
  have hc6 := h6.ctx
  refine ld_ok hc6 (by unfold ACC; omega) (by unfold ACC; omega) fun s7 u7 => ?_
  have hc7 : Ctx b s7 := hc6.of_rest (u7.rest (ws := clob64) (by decide)) (by decide)
  refine ld_ok hc7 (by unfold ACC; omega) (by unfold ACC; omega) fun s8 u8 => ?_
  have hc8 : Ctx b s8 := hc7.of_rest (u8.rest (ws := clob64) (by decide)) (by decide)
  refine ld_ok hc8 (by unfold ACC; omega) (by unfold ACC; omega) fun s9 u9 => ?_
  refine WP.block_append (WP.mono (sbb0_ok (d := .t4) (y := .a2) (c := .a5)) fun t1 ⟨f1, l1, k1⟩ => ?_)
  refine WP.block_append (WP.mono (sbb0_ok (d := .a1) (y := .a5) (c := .a2)) fun t2 ⟨f2, l2, k2⟩ => ?_)
  refine WP.block_append (WP.mono (sbb0_ok (d := .a4) (y := .a2) (c := .a5)) fun t3 ⟨f3, l3, k3⟩ => ?_)
  refine wp_li (by decide) fun t4 u4 => ?_
  have r4 : Rest clob64 s9 t4 := (Keeps.rest k1).mono (by decide) |>.trans ((Keeps.rest k2).mono (by decide)
    |>.trans ((Keeps.rest k3).mono (by decide) |>.trans (u4.rest (by decide))))
  have r94 : Rest clob64 s6 s9 := (u7.rest (by decide)).trans ((u8.rest (by decide)).trans (u9.rest (by decide)))
  have hc4 : Ctx b t4 := hc6.of_rest (r94.trans r4) (by decide)
  have hm4 : t4.mem = s6.mem := by rw [u4.mem, k3.2.1, k2.2.1, k1.2.1, u9.mem, u8.mem, u7.mem]
  refine WP.block_append (WP.mono (addQs_ok (s0 := t4) 6 (Nat.le_refl _) t4
    ⟨hc4, Rest.refl _ _, rfl, fun _ _ _ => rfl, rfl, by rw [u4.gpr]; decide, by
      simp only [colsV, u4.gpr]; rfl⟩) fun t5 h5 => ?_)
  refine wp_sub fun t6 u6 => WP.block_nil ?_
  -- The words loaded.
  have L9 : (s9.gpr .t4).toNat = T s.mem b 9 := by
    rw [u9.other _ (by decide), u8.other _ (by decide), u7.gpr]; exact h6.hi 9 (by omega) (by omega)
  have L10 : (s9.gpr .a1).toNat = T s.mem b 10 := by
    rw [u9.other _ (by decide), u8.gpr, u7.mem]; exact h6.hi 10 (by omega) (by omega)
  have L11 : (s9.gpr .a4).toNat = T s.mem b 11 := by
    rw [u9.gpr, u8.mem, u7.mem]; exact h6.hi 11 (by omega) (by omega)
  have hβ : s9.gpr .a2 = s6.gpr .a2 := by
    rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide)]
  rw [L9, hβ] at f1
  rw [k1.1 .a1 (by decide), L10] at f2
  rw [k2.1 .a4 (by decide), k1.1 .a4 (by decide), L11] at f3
  -- The registers before the sum of the quotient words.
  have g9 : ∀ r, r ≠ .t4 → r ≠ .a1 → r ≠ .a4 → s9.gpr r = s6.gpr r := fun r h1 h2 h3 => by
    rw [u9.other _ h3, u8.other _ h2, u7.other _ h1]
  have x0 : (t4.gpr (X 0)) = s6.gpr (rw 6) := by
    show t4.gpr .t5 = s6.gpr .t5
    rw [u4.other _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide),
      g9 _ (by decide) (by decide) (by decide)]
  have x1 : (t4.gpr (X 1)) = s6.gpr (rw 7) := by
    show t4.gpr .t6 = s6.gpr .t6
    rw [u4.other _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide),
      g9 _ (by decide) (by decide) (by decide)]
  have x2 : (t4.gpr (X 2)) = s6.gpr (rw 8) := by
    show t4.gpr .t3 = s6.gpr .t3
    rw [u4.other _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide),
      g9 _ (by decide) (by decide) (by decide)]
  have x3 : (t4.gpr (X 3)) = t1.gpr .t4 := by
    show t4.gpr .t4 = _
    rw [u4.other _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide)]
  have x4 : (t4.gpr (X 4)) = t2.gpr .a1 := by
    show t4.gpr .a1 = _
    rw [u4.other _ (by decide), k3.1 _ (by decide)]
  have x5 : (t4.gpr (X 5)) = t3.gpr .a4 := by
    show t4.gpr .a4 = _
    rw [u4.other _ (by decide)]
  have hB : t5.gpr .a5 = t3.gpr .a5 := by rw [h5.a5, u4.other _ (by decide)]
  have hm5 : t5.mem = s6.mem := by rw [h5.mem, hm4]
  have hx : ∀ k < 6, t6.gpr (X k) = t5.gpr (X k) := fun k hk => u6.other _ (X_facts k hk).1
  have ha2 : t6.gpr XC = t5.gpr .a2 - t5.gpr .a5 := by rw [u6.gpr]; rfl
  -- The numbers.
  have hv5 := h5.val
  rw [colsV_add] at hv5
  have hQ : colsV (fun k => dw t4.mem b (ACC + 8 * k)) 6 = accW ACC s6.mem b 6 := by
    rw [accW_eq, hm4]
  rw [hQ] at hv5
  have hv6 := h6.val
  have hup : upW s.mem b (6 + 3) (9 - 6) = T s.mem b 9 + 2 ^ 64 * (T s.mem b 10 + 2 ^ 64 * T s.mem b 11) := by
    simp only [upW, Nat.reduceAdd, Nat.reduceSub, Nat.mul_zero, Nat.add_zero]
  have hw6 : wv s.mem b 6 s6 = (s6.gpr (rw 6)).toNat + 2 ^ 64 * (s6.gpr (rw 7)).toNat +
      2 ^ 128 * (s6.gpr (rw 8)).toNat +
      2 ^ 192 * (T s.mem b 9 + 2 ^ 64 * (T s.mem b 10 + 2 ^ 64 * T s.mem b 11)) := by
    rw [wv, hup]
  rw [hw6] at hv6
  have hX4 : colsV (fun k => (t4.gpr (X k)).toNat) 6 = (s6.gpr (rw 6)).toNat + 2 ^ 64 * (s6.gpr (rw 7)).toNat +
      2 ^ 128 * (s6.gpr (rw 8)).toNat + 2 ^ 192 * (t1.gpr .t4).toNat + 2 ^ 256 * (t2.gpr .a1).toNat +
      2 ^ 320 * (t3.gpr .a4).toNat := by
    simp only [colsV, x0, x1, x2, x3, x4, x5]; omega
  rw [hX4] at hv5
  have hX6 : colsV (fun k => (t6.gpr (X k)).toNat) 6 = colsV (fun k => (t5.gpr (X k)).toNat) 6 :=
    colsV_congr fun k hk => by rw [hx k hk]
  have hQlt := accW_lt (acc := ACC) s6.mem b 6
  have hc5 := h5.cy
  have hcol := colsV_lt_of (fun k => (t5.gpr (X k)).toNat) (fun k => (BitVec.isLt _)) 6
  rw [← hB] at l3 f3
  have hsub : (t5.gpr .a5).toNat ≤ (t5.gpr .a2).toNat →
      (t6.gpr XC).toNat = (t5.gpr .a2).toNat - (t5.gpr .a5).toNat := fun h => by
    rw [ha2, BitVec.toNat_sub]
    have := (t5.gpr .a2).isLt
    omega
  -- The borrow out of the top words, and the number before the quotient words.
  have ha : (s6.gpr (rw 6)).toNat + 2 ^ 64 * (s6.gpr (rw 7)).toNat + 2 ^ 128 * (s6.gpr (rw 8)).toNat +
      2 ^ 192 * (t1.gpr .t4).toNat + 2 ^ 256 * (t2.gpr .a1).toNat + 2 ^ 320 * (t3.gpr .a4).toNat +
      2 ^ 192 * (s6.gpr .a2).toNat =
      ((s6.gpr (rw 6)).toNat + 2 ^ 64 * (s6.gpr (rw 7)).toNat + 2 ^ 128 * (s6.gpr (rw 8)).toNat +
      2 ^ 192 * (T s.mem b 9 + 2 ^ 64 * (T s.mem b 10 + 2 ^ 64 * T s.mem b 11))) +
      2 ^ 384 * (t5.gpr .a5).toNat := by
    omega
  generalize (s6.gpr (rw 6)).toNat + 2 ^ 64 * (s6.gpr (rw 7)).toNat + 2 ^ 128 * (s6.gpr (rw 8)).toNat +
      2 ^ 192 * (t1.gpr .t4).toNat + 2 ^ 256 * (t2.gpr .a1).toNat + 2 ^ 320 * (t3.gpr .a4).toNat = Xf at ha hv5
  generalize (s6.gpr (rw 6)).toNat + 2 ^ 64 * (s6.gpr (rw 7)).toNat + 2 ^ 128 * (s6.gpr (rw 8)).toNat +
      2 ^ 192 * (T s.mem b 9 + 2 ^ 64 * (T s.mem b 10 + 2 ^ 64 * T s.mem b 11)) = W6 at ha hv6
  generalize colsV (fun k => (t5.gpr (X k)).toNat) 6 = C at *
  generalize accW ACC s6.mem b 6 = Q at *
  generalize prodV s.mem b = Pr at *
  generalize (s6.gpr .a2).toNat = β at *
  generalize (t5.gpr .a5).toNat = B at *
  generalize (t5.gpr .a2).toNat = c at *
  have key : (C + 2 ^ 384 * c) * 2 ^ 384 = Pr + Q * P + 2 ^ 768 * B := by
    unfold P Spec.P384.p Mc at *
    omega
  have hge : B ≤ c := by
    rcases Nat.lt_or_ge c B with h | h
    · have h0 : c = 0 := by omega
      have h1 : B = 1 := by omega
      rw [h0, h1] at key
      have hC : C < 2 ^ 384 := by rw [two384]; exact hcol
      have := Nat.mul_lt_mul_of_pos_right hC (Nat.two_pow_pos 384)
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at key
      omega
    · exact h
  have hxc : (t6.gpr XC).toNat = c - B := hsub hge
  refine ⟨hc4.of_rest (h5.rest.trans (u6.rest (by decide))) (by decide),
    h6.rest.trans (r94.trans (r4.trans (h5.rest.trans (u6.rest (by decide))))), ?_, by rw [hxc]; omega, Q,
    by rw [two384]; exact hQlt, ?_⟩
  · rw [u6.mem, hm5]; exact h6.frame
  · rw [xv, hX6, hxc]
    -- The arguments explicit: unifying them evaluates the powers.
    exact @fin_eq C c B Pr (Q * P) hge key

end VG.Proof.Weierstrass.RISCV64.P384Field

/-!
## P-384's field on RISC-V: the final subtraction

`sumWith ks ++ csubTail` stores `x mod m` at `[t2]` for the number
`x = X + 2³⁸⁴ XC` below `2m` (`csubWith_ok`): the words of `x + (2³⁸⁴ - m)`
with carries, stored at `[t2]` (`sumWith_ok`), whose carry out of 384 bits or
`XC` is `x ≥ m`, then the stored words or `x`'s by that mask (`sels_ok`).
-/

namespace VG.Proof.Weierstrass.RISCV64.P384Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P384Field
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt dw_write_self dw_write_other al8 colsV colsV_add)
open VG.Proof.Weierstrass.RISCV64.P256Field (adc_ok upd_keeps)

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

/-- The registers `csub` writes. -/
abbrev clobC : List Reg := [.t0, .a0, .a5, .a7]

/-- The six doublewords at `O`. -/
abbrev d6 (m : Mem) (O : Addr) : Nat := colsV (fun k => dw m O (8 * k)) 6

theorem out_contains (O : Addr) {j : Nat} (hj : j < 6) :
    (⟨O, 48⟩ : Region).Contains (O + BitVec.ofNat 64 (8 * j)) 8 := by
  have := Offset.contains O (d := 8 * j) (n := 8) (e := 0) (k := 48) (by omega) (by omega) (by omega)
  simpa using this

/-- A block that puts `N j` into `t0`, from `N (j - 1)` there for `j > 0`. -/
def KOk (k : List Instr) (j : Nat) (N : Nat → Nat) : Prop :=
  ∀ s : State, (j = 0 ∨ (s.gpr .t0).toNat = N (j - 1)) →
    WP isa (.block k) s fun s' => (s'.gpr .t0).toNat = N j ∧ Keeps [.t0] s s'

/-- After `j` words of `x + N` from `s0`, with `O` in `t2`. -/
structure SumInv (O : Addr) (N : Nat → Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobC → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨O, 48⟩] s0.mem s.mem
  t0 : 0 < j → (s.gpr .t0).toNat = N (j - 1)
  cy : (s.gpr .a7).toNat ≤ 1
  val : colsV (fun k => dw s.mem O (8 * k)) j + (2 ^ 64) ^ j * (s.gpr .a7).toNat =
    colsV (fun k => (s0.gpr (X k)).toNat + N k) j

theorem colsV_congr' {f g : Nat → Nat} : ∀ {n}, (∀ k < n, f k = g k) → colsV f n = colsV g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [colsV]; rw [colsV_congr' (fun k hk => h k (by omega)), h n (by omega)]

/-- Word `j` of `x + N`. -/
theorem sumStep_ok {O : Addr} {N : Nat → Nat} (hN : ∀ j, N j < 2 ^ 64) {k : List Instr} {j : Nat}
    (hj : j < 6) (hk : KOk k j N) (hal : O.toNat % 8 = 0) {s0 s : State} (h2 : s0.gpr .t2 = O)
    (hw : ∀ j < 6, InRegions s0.wr (O + BitVec.ofNat 64 (8 * j)) 8) (h : SumInv O N s0 j s) :
    WP isa (.block (k ++ sumWord j)) s (SumInv O N s0 (j + 1)) := by
  obtain ⟨-, x5, -, x7, x0, xa, -, -, -, -, -⟩ := X_facts j hj
  have hpre : j = 0 ∨ (s.gpr .t0).toNat = N (j - 1) := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exact .inl h0
    · exact .inr (h.t0 h0)
  refine WP.block_append (WP.mono (hk s hpre) fun s1 ⟨e1, k1⟩ => ?_)
  unfold sumWord
  refine WP.block_append (WP.mono (adc_ok (d := .a5) (x := X j) (y := .t0) (c := .a7) (u := .a0))
    fun s2 ⟨e2, k2⟩ => ?_)
  have g2 : ∀ r, r ∉ clobC → s2.gpr r = s0.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k2.1 _ (by simp [hr.2.1, hr.2.2.1, hr.2.2.2]), k1.1 _ (by simp [hr.1]), h.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
  have p2 : s2.gpr .t2 + BitVec.ofNat 64 (8 * j) = O + BitVec.ofNat 64 (8 * j) := by
    rw [g2 _ (by decide), h2]
  refine wp_sd (by omega) p2 (al8 hal (by omega)) (by rw [k2.2.2.2.1, k1.2.2.2.1, h.wr]; exact hw j hj)
    fun s3 u3 => WP.block_nil ?_
  have ex : s1.gpr (X j) = s0.gpr (X j) := by rw [k1.1 _ (by simp [x0]), h.gpr _ (by simp [x0, xa, x5, x7])]
  have ec : s1.gpr .a7 = s.gpr .a7 := k1.1 _ (by decide)
  have e2' := e2 (by rw [ec]; exact h.cy)
  rw [ex, ec, e1] at e2'
  have hm3 : s3.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j)) (s2.gpr .a5) := by
    rw [u3.mem, k2.2.1, k1.2.1]
  refine ⟨fun r hr => by rw [u3.gpr]; exact g2 r hr, by rw [u3.rd, k2.2.2.1, k1.2.2.1, h.rd],
    by rw [u3.wr, k2.2.2.2.1, k1.2.2.2.1, h.wr], by rw [u3.sp, k2.2.2.2.2, k1.2.2.2.2, h.sp], ?_,
    fun _ => by rw [u3.gpr, k2.1 _ (by decide), e1]; rfl, ?_, ?_⟩
  · rw [hm3]; exact h.frame.writeW (List.mem_singleton_self _) _ (out_contains O hj)
  · rw [u3.gpr]
    have := (s2.gpr .a5).isLt; have := (s0.gpr (X j)).isLt; have := hN j; have := h.cy
    omega
  · have hv := h.val
    have hc : colsV (fun k => dw s3.mem O (8 * k)) j = colsV (fun k => dw s.mem O (8 * k)) j :=
      colsV_congr' fun k hk => by rw [hm3, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    show colsV (fun k => dw s3.mem O (8 * k)) j + (2 ^ 64) ^ j * dw s3.mem O (8 * j) +
        (2 ^ 64) ^ (j + 1) * (s3.gpr .a7).toNat =
      colsV (fun k => (s0.gpr (X k)).toNat + N k) j + (2 ^ 64) ^ j * ((s0.gpr (X j)).toNat + N j)
    rw [hc, hm3, dw_write_self, u3.gpr, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..,
      ← hv]
    generalize (2 ^ 64) ^ j = E at *
    generalize colsV (fun k => dw s.mem O (8 * k)) j = C at *
    have key : E * (s2.gpr .a5).toNat + E * 2 ^ 64 * (s2.gpr .a7).toNat =
        E * (s.gpr .a7).toNat + E * ((s0.gpr (X j)).toNat + N j) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, e2']; congr 1; omega
    omega

/-- The words of `x + N`, by induction. -/
theorem sums_ok {O : Addr} {N : Nat → Nat} (hN : ∀ j, N j < 2 ^ 64) {ks : List (List Instr)}
    (hk : ∀ j < 6, KOk (ks.getD j []) j N) (hal : O.toNat % 8 = 0) {s0 : State} (h2 : s0.gpr .t2 = O)
    (hw : ∀ j < 6, InRegions s0.wr (O + BitVec.ofNat 64 (8 * j)) 8) :
    ∀ n ≤ 6, ∀ s, SumInv O N s0 0 s →
      WP isa (.block ((List.range n).flatMap fun j => ks.getD j [] ++ sumWord j)) s (SumInv O N s0 n) :=
  wp_range_flatMap (M := isa) (SumInv O N s0) fun j _ hj h => sumStep_ok hN hj (hk j hj) hal h2 hw h

/-- After `j` words of the selection from `s0`, by the mask `t0`. -/
structure SelInv (O : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .a5 → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨O, 48⟩] s0.mem s.mem
  lo : ∀ k < j, dw s.mem O (8 * k) =
    if s0.gpr .t0 = BitVec.allOnes 64 then dw s0.mem O (8 * k) else (s0.gpr (X k)).toNat
  hi : ∀ k, j ≤ k → k < 6 → dw s.mem O (8 * k) = dw s0.mem O (8 * k)

/-- Word `j` of the selection. -/
theorem selStep_ok {O : Addr} (hal : O.toNat % 8 = 0) {s0 s : State} (h2 : s0.gpr .t2 = O)
    (hw : ∀ j < 6, InRegions s0.wr (O + BitVec.ofNat 64 (8 * j)) 8) (hm : IsMask (s0.gpr .t0))
    {j : Nat} (hj : j < 6) (h : SelInv O s0 j s) :
    WP isa (.block (selWord j)) s (SelInv O s0 (j + 1)) := by
  obtain ⟨-, x5, -, -, x0, -, -, x2, -, -, -⟩ := X_facts j hj
  unfold selWord
  have p : s.gpr .t2 + BitVec.ofNat 64 (8 * j) = O + BitVec.ofNat 64 (8 * j) := by
    rw [h.gpr _ (by decide), h2]
  have hr : InRegions (s.rd ++ s.wr) (O + BitVec.ofNat 64 (8 * j)) 8 := by
    obtain ⟨r, hr, hc⟩ := hw j hj
    exact ⟨r, List.mem_append_right _ (by rw [h.wr]; exact hr), hc⟩
  refine wp_ld (by omega) p (al8 hal (by omega)) hr fun s1 u1 => wp_xor fun s2 u2 =>
    VG.Proof.X25519.RISCV64.wp_and fun s3 u3 => wp_xor fun s4 u4 => ?_
  have g4 : ∀ r, r ≠ .a5 → s4.gpr r = s.gpr r := fun r hr => by
    rw [u4.other _ hr, u3.other _ hr, u2.other _ hr, u1.other _ hr]
  have v4 : s4.gpr .a5 = if s0.gpr .t0 = BitVec.allOnes 64 then s.mem.readW (O + BitVec.ofNat 64 (8 * j)) 64
      else s0.gpr (X j) := by
    rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr, u3.other _ x5, u2.other _ x5, u1.other _ x5,
      u2.other .t0 (by decide), u1.other .t0 (by decide), h.gpr _ x5, h.gpr .t0 (by decide)]
    exact sel_mask hm
  refine wp_sd (by omega) (by rw [g4 _ (by decide), p]) (al8 hal (by omega))
    (by rw [u4.wr, u3.wr, u2.wr, u1.wr, h.wr]; exact hw j hj) fun s5 u5 => WP.block_nil ?_
  have hm5 : s5.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j)) (s4.gpr .a5) := by
    rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨fun r hr => by rw [u5.gpr, g4 r hr, h.gpr r hr], by rw [u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, h.rd],
    by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, h.wr], by rw [u5.sp, u4.sp, u3.sp, u2.sp, u1.sp, h.sp], ?_,
    fun k hk => ?_, fun k hk hk' => ?_⟩
  · rw [hm5]; exact h.frame.writeW (List.mem_singleton_self _) _ (out_contains O hj)
  · rw [hm5]
    rcases Nat.lt_or_ge k j with hkj | hkj
    · rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.lo k hkj
    · have : k = j := by omega
      subst this
      rw [dw_write_self, v4]
      split
      · exact h.hi k (Nat.le_refl _) hj
      · rfl
  · rw [hm5, dw_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.hi k (by omega) hk'

theorem sels_ok {O : Addr} (hal : O.toNat % 8 = 0) {s0 : State} (h2 : s0.gpr .t2 = O)
    (hw : ∀ j < 6, InRegions s0.wr (O + BitVec.ofNat 64 (8 * j)) 8) (hm : IsMask (s0.gpr .t0)) :
    ∀ n ≤ 6, ∀ s, SelInv O s0 0 s →
      WP isa (.block ((List.range n).flatMap selWord)) s (SelInv O s0 n) :=
  wp_range_flatMap (M := isa) (SelInv O s0) fun _ _ hj h => selStep_ok hal h2 hw hm hj h

theorem colsV_lt' (f : Nat → Nat) (hf : ∀ k, f k < 2 ^ 64) (n : Nat) : colsV f n < (2 ^ 64) ^ n :=
  colsV_lt_of f hf n

/-- `sumWith ks ++ csubTail`: `x mod m` at `[t2]`, for `x = X + 2³⁸⁴ XC` below
`2m`, where `ks[j]` puts the words `N j` of `2³⁸⁴ - m` into `t0`. -/
theorem csubWith_ok {ks : List (List Instr)} {N : Nat → Nat} {M : Nat} (hN : ∀ j, N j < 2 ^ 64)
    (hk : ∀ j < 6, KOk (ks.getD j []) j N) (hNv : colsV N 6 + M = 2 ^ 384) {s : State}
    {O : Addr} (ht2 : s.gpr .t2 = O) (hal : O.toNat % 8 = 0)
    (hw : ∀ j < 6, InRegions s.wr (O + BitVec.ofNat 64 (8 * j)) 8) (hc : (s.gpr XC).toNat ≤ 1)
    (hx : xv s + 2 ^ 384 * (s.gpr XC).toNat < 2 * M) :
    WP isa (.block (sumWith ks ++ csubTail)) s fun s' =>
      d6 s'.mem O = (xv s + 2 ^ 384 * (s.gpr XC).toNat) % M ∧
      Frame [⟨O, 48⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobC → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold sumWith csubTail
  rw [List.cons_append]
  refine wp_li (by decide) fun s1 u1 => ?_
  have h0 : SumInv O N s 0 s1 :=
    ⟨fun r hr => u1.other _ (fun h => hr (by simp [h])), u1.rd, u1.wr, u1.sp, by rw [u1.mem]; exact Frame.refl _ _,
      fun h => absurd h (Nat.lt_irrefl _), by rw [u1.gpr]; decide, by simp only [colsV, u1.gpr]; rfl⟩
  refine WP.block_append (WP.mono (sums_ok hN hk hal ht2 hw 6 (Nat.le_refl _) s1 h0) fun s2 h2 => ?_)
  rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_or fun s3 u3 => wp_li (imm := 0) (by decide) fun s4 u4 => wp_sub fun s5 u5 => ?_
  have hxc : s2.gpr XC = s.gpr XC := h2.gpr _ (by decide)
  have hm : IsMask (s5.gpr .t0) ∧ (s5.gpr .t0 = BitVec.allOnes 64 ↔
      (s2.gpr .a7).toNat = 1 ∨ (s.gpr XC).toNat = 1) := by
    rw [u5.gpr, u4.gpr, u4.other _ (by decide), u3.gpr, ← hxc]
    exact mask_of_bits h2.cy (by rw [hxc]; exact hc)
  have g5 : ∀ r, r ≠ .t0 → r ≠ .a7 → s5.gpr r = s2.gpr r := fun r h0 h7 => by
    rw [u5.other _ h0, u4.other _ h0, u3.other _ h7]
  have m5 : s5.mem = s2.mem := by rw [u5.mem, u4.mem, u3.mem]
  have p5 : s5.gpr .t2 = O := by rw [g5 _ (by decide) (by decide), h2.gpr _ (by decide), ht2]
  have w5 : s5.wr = s.wr := by rw [u5.wr, u4.wr, u3.wr, h2.wr]
  refine WP.mono (sels_ok hal p5 (by rw [w5]; exact hw) hm.1 6 (Nat.le_refl _) s5
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ => rfl⟩) fun s6 h6 => ?_
  have rt : ∀ r, r ∉ clobC → s6.gpr r = s.gpr r := fun r hr => by
    have h0 : r ≠ .t0 := fun h => hr (by simp [h])
    have h5 : r ≠ .a5 := fun h => hr (by simp [h])
    have h7 : r ≠ .a7 := fun h => hr (by simp [h])
    rw [h6.gpr r h5, g5 r h0 h7, h2.gpr r hr]
  have hxk : ∀ k < 6, (s5.gpr (X k)).toNat = (s.gpr (X k)).toNat := fun k hk => by
    obtain ⟨-, x5, -, x7, x0, xa, -⟩ := X_facts k hk
    rw [g5 _ x0 x7, h2.gpr _ (by simp [x0, xa, x5, x7])]
  have hd : d6 s6.mem O = if s5.gpr .t0 = BitVec.allOnes 64 then d6 s2.mem O else xv s := by
    split
    · exact colsV_congr' fun k hk => by rw [h6.lo k hk, ite_eq_left ‹_›, m5]
    · exact colsV_congr' fun k hk => by rw [h6.lo k hk, ite_eq_right ‹_›, hxk k hk]
  have hv := h2.val
  rw [colsV_add] at hv
  have hs : d6 s2.mem O + 2 ^ 384 * (s2.gpr .a7).toNat + M = xv s + 2 ^ 384 := by
    rw [two384]; simp only [d6, xv] at hv ⊢; omega
  have hd6 := colsV_lt_of (fun k => dw s2.mem O (8 * k)) (fun k => dw_lt _ _ _) 6
  rw [← two384] at hd6
  have hc7 := h2.cy
  refine ⟨?_, ?_, rt, ?_, ?_, ?_⟩
  · rw [hd]
    have hge := hm.2
    simp only [d6, xv] at hd6 hs hx ⊢
    generalize colsV (fun k => dw s2.mem O (8 * k)) 6 = D at *
    generalize colsV (fun k => (s.gpr (X k)).toNat) 6 = Y at *
    split
    · rename_i h
      have hg := hge.mp h
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · rename_i h
      have hg : ¬ ((s2.gpr .a7).toNat = 1 ∨ (s.gpr XC).toNat = 1) := fun h' => h (hge.mpr h')
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
  · exact h2.frame.trans (by rw [← m5]; exact h6.frame)
  · rw [h6.rd, u5.rd, u4.rd, u3.rd, h2.rd]
  · rw [h6.wr, w5]
  · rw [h6.sp, u5.sp, u4.sp, u3.sp, h2.sp]

/-- The words of `2³⁸⁴ - p`. -/
def NP (j : Nat) : Nat := [2 ^ 64 - 2 ^ 32 + 1, 2 ^ 32 - 1, 1, 0, 0, 0].getD j 0

theorem NP_lt (j : Nat) : NP j < 2 ^ 64 := by
  unfold NP
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp

theorem NP_val : colsV NP 6 + P = 2 ^ 384 := by
  simp only [colsV, NP, List.getD_cons_zero, List.getD_cons_succ]
  unfold P Spec.P384.p
  omega

open VG.Proof.Weierstrass.RISCV64.P256Field (wp_lim1) in
theorem kP_ok : ∀ j < 6, KOk (sumPKs.getD j []) j NP := by
  intro j hj s _
  obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  · refine wp_lim1 fun s1 u1 => wp_sll (by decide) fun s2 u2 => wp_addi (imm := 1) (by decide) fun s3 u3 =>
      WP.block_nil ⟨by rw [u3.gpr, u2.gpr, u1.gpr]; decide, ((upd_keeps u1).trans ((upd_keeps u2).trans
        (upd_keeps u3))).mono⟩
  · refine wp_lim1 fun s1 u1 => wp_srl (by decide) fun s2 u2 =>
      WP.block_nil ⟨by rw [u2.gpr, u1.gpr]; decide, ((upd_keeps u1).trans (upd_keeps u2)).mono⟩
  · exact wp_li (imm := 1) (by decide) fun s1 u1 => WP.block_nil ⟨by rw [u1.gpr]; decide, upd_keeps u1⟩
  · exact wp_li (imm := 0) (by decide) fun s1 u1 => WP.block_nil ⟨by rw [u1.gpr]; decide, upd_keeps u1⟩
  · rename_i h
    have h' : (s.gpr .t0).toNat = 0 := by
      rcases h with h | h
      · omega
      · exact h
    exact WP.block_nil ⟨h', ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
  · rename_i h
    have h' : (s.gpr .t0).toNat = 0 := by
      rcases h with h | h
      · omega
      · exact h
    exact WP.block_nil ⟨h', ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩

/-- `csub`: `x mod p` at `[t2]`, for `x = X + 2³⁸⁴ XC` below `2p`. -/
theorem csub_ok {s : State} {O : Addr} (ht2 : s.gpr .t2 = O) (hal : O.toNat % 8 = 0)
    (hw : ∀ j < 6, InRegions s.wr (O + BitVec.ofNat 64 (8 * j)) 8) (hc : (s.gpr XC).toNat ≤ 1)
    (hx : xv s + 2 ^ 384 * (s.gpr XC).toNat < 2 * P) :
    WP isa (.block csub) s fun s' =>
      d6 s'.mem O = (xv s + 2 ^ 384 * (s.gpr XC).toNat) % P ∧
      Frame [⟨O, 48⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobC → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  csubWith_ok NP_lt kP_ok NP_val ht2 hal hw hc hx

end VG.Proof.Weierstrass.RISCV64.P384Field

/-!
## P-384's field on RISC-V: the product

`mulCore` on pointers `t4`, `t5` and `t2` (`mulCore_ok`): the operands copied
to `MA` and `MB` (`copyIn_ok`), their product (or the square of the first, if
the pointers are equal) at `ACC` (`product_ok`, `square_ok`), reduced
(`reduce_ok`) and stored at `[t2]` (`csub_ok`): Montgomery's product modulo `p`.
-/

namespace VG.Proof.Weierstrass.RISCV64.P384Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P384Field
open VG.Proof.X25519.RISCV64 (Ctx Rest)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok clob64 dw_write_self dw_write_other al8 dw_frame colsV)
open VG.Proof.X25519.RISCV64.R64 (accW accW_eq)

/-- The registers the operations write. -/
abbrev clobM : List Reg := [.t0, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a4, .a5, .a6, .a7]

/-- The registers of the copies. -/
abbrev clobI : List Reg := [.t3, .t6, .a1, .a2, .a4, .a5]

/-- The six doublewords at `b + o`, as offsets from `b`. -/
theorem d6_add (m : Mem) (b : Addr) (o : Nat) : d6 m (b + BitVec.ofNat 64 o) = E6 m b o := by
  have e : ∀ k, (b + BitVec.ofNat 64 o) + BitVec.ofNat 64 k = b + BitVec.ofNat 64 (o + k) := fun k => by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  simp only [d6, E6, val6, colsV, dw, e, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul,
    Nat.pow_zero, Nat.zero_add, Nat.reducePow]
  omega

theorem d6_lt (m : Mem) (O : Addr) : d6 m O < 2 ^ 384 := by
  rw [two384]; exact colsV_lt_of _ (fun _ => dw_lt _ _ _) 6

/-- The words of the operand at `p` copied to `b + o`. -/
theorem copyIn_ok {b A : Addr} {s : State} (hc : Ctx b s) {p : Reg} (hp : s.gpr p = A)
    (hpr : p ∉ clobI) (hal : A.toNat % 8 = 0)
    (hr : ∀ j < 6, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * j)) 8)
    {o : Nat} (ho : o + 48 ≤ 2048) (ho8 : o % 8 = 0) :
    WP isa (.block (copyIn p o)) s fun s' =>
      Ctx b s' ∧ Rest clobI s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 48⟩] s.mem s'.mem ∧
      d6 s'.mem (b + BitVec.ofNat 64 o) = d6 s.mem A := by
  unfold copyIn
  have hp' : ∀ r ∈ clobI, r ≠ p := fun r hr h => hpr (h ▸ hr)
  have h0 := hr 0 (by decide)
  have h1 := hr 1 (by decide)
  have h2 := hr 2 (by decide)
  have h3 := hr 3 (by decide)
  have h4 := hr 4 (by decide)
  have h5 := hr 5 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at h0 h1 h2 h3 h4 h5
  refine wp_ld (off := 0) (a := A + BitVec.ofNat 64 0) (by decide) (by rw [hp]) (al8 hal (by decide))
    (by exact h0) fun s1 u1 => ?_
  refine wp_ld (off := 8) (a := A + BitVec.ofNat 64 8) (by decide) (by rw [u1.other _ (hp' .t3 (by decide)).symm, hp]) (al8 hal (by decide))
    (by rw [u1.rd, u1.wr]; exact h1) fun s2 u2 => ?_
  refine wp_ld (off := 16) (a := A + BitVec.ofNat 64 16) (by decide) (by rw [u2.other _ (hp' .t6 (by decide)).symm, u1.other _ (hp' .t3 (by decide)).symm, hp]) (al8 hal (by decide))
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact h2) fun s3 u3 => ?_
  refine wp_ld (off := 24) (a := A + BitVec.ofNat 64 24) (by decide) (by rw [u3.other _ (hp' .a1 (by decide)).symm, u2.other _ (hp' .t6 (by decide)).symm, u1.other _ (hp' .t3 (by decide)).symm, hp]) (al8 hal (by decide))
    (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact h3) fun s4 u4 => ?_
  refine wp_ld (off := 32) (a := A + BitVec.ofNat 64 32) (by decide) (by rw [u4.other _ (hp' .a2 (by decide)).symm, u3.other _ (hp' .a1 (by decide)).symm, u2.other _ (hp' .t6 (by decide)).symm, u1.other _ (hp' .t3 (by decide)).symm, hp]) (al8 hal (by decide))
    (by rw [u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact h4) fun s5 u5 => ?_
  refine wp_ld (off := 40) (a := A + BitVec.ofNat 64 40) (by decide) (by rw [u5.other _ (hp' .a4 (by decide)).symm, u4.other _ (hp' .a2 (by decide)).symm, u3.other _ (hp' .a1 (by decide)).symm, u2.other _ (hp' .t6 (by decide)).symm, u1.other _ (hp' .t3 (by decide)).symm, hp]) (al8 hal (by decide))
    (by rw [u5.rd, u5.wr, u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact h5) fun s6 u6 => ?_
  have r6 : Rest clobI s s6 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
    ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  have hc6 : Ctx b s6 := hc.of_rest r6 (by decide)
  have m6 : s6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have v0 : s6.gpr .t3 = s.mem.readW (A + BitVec.ofNat 64 0) 64 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
  have v1 : s6.gpr .t6 = s.mem.readW (A + BitVec.ofNat 64 8) 64 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.mem]
  have v2 : s6.gpr .a1 = s.mem.readW (A + BitVec.ofNat 64 16) 64 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.mem, u1.mem]
  have v3 : s6.gpr .a2 = s.mem.readW (A + BitVec.ofNat 64 24) 64 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.mem, u2.mem, u1.mem]
  have v4 : s6.gpr .a4 = s.mem.readW (A + BitVec.ofNat 64 32) 64 := by
    rw [u6.other _ (by decide), u5.gpr, u4.mem, u3.mem, u2.mem, u1.mem]
  have v5 : s6.gpr .a5 = s.mem.readW (A + BitVec.ofNat 64 40) 64 := by
    rw [u6.gpr, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine sd_ok hc6 (d := o + 0) (by omega) (by omega) fun s7 u7 => ?_
  have hc7 : Ctx b s7 := hc6.of_rest (u7.rest []) (by decide)
  refine sd_ok hc7 (d := o + 8) (by omega) (by omega) fun s8 u8 => ?_
  have hc8 : Ctx b s8 := hc7.of_rest (u8.rest []) (by decide)
  refine sd_ok hc8 (d := o + 16) (by omega) (by omega) fun s9 u9 => ?_
  have hc9 : Ctx b s9 := hc8.of_rest (u9.rest []) (by decide)
  refine sd_ok hc9 (d := o + 24) (by omega) (by omega) fun s10 u10 => ?_
  have hc10 : Ctx b s10 := hc9.of_rest (u10.rest []) (by decide)
  refine sd_ok hc10 (d := o + 32) (by omega) (by omega) fun s11 u11 => ?_
  have hc11 : Ctx b s11 := hc10.of_rest (u11.rest []) (by decide)
  refine sd_ok hc11 (d := o + 40) (by omega) (by omega) fun s12 u12 => ?_
  refine WP.block_nil ?_
  have g12 : s12.gpr = s6.gpr := by rw [u12.gpr, u11.gpr, u10.gpr, u9.gpr, u8.gpr, u7.gpr]
  have hm : s12.mem = ((((((s.mem.writeW (b + BitVec.ofNat 64 (o + 0)) (s6.gpr .t3)).writeW
      (b + BitVec.ofNat 64 (o + 8)) (s6.gpr .t6)).writeW (b + BitVec.ofNat 64 (o + 16)) (s6.gpr .a1)).writeW
      (b + BitVec.ofNat 64 (o + 24)) (s6.gpr .a2)).writeW (b + BitVec.ofNat 64 (o + 32)) (s6.gpr .a4)).writeW
      (b + BitVec.ofNat 64 (o + 40)) (s6.gpr .a5)) := by
    rw [u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, m6, u11.gpr, u10.gpr, u9.gpr, u8.gpr, u7.gpr]
  have r612 : Rest [] s6 s12 := ⟨fun r _ => by rw [g12], by rw [u12.rd, u11.rd, u10.rd, u9.rd, u8.rd, u7.rd],
    by rw [u12.wr, u11.wr, u10.wr, u9.wr, u8.wr, u7.wr], by rw [u12.sp, u11.sp, u10.sp, u9.sp, u8.sp, u7.sp]⟩
  refine ⟨hc6.of_rest r612 (by decide), r6.trans (r612.mono (by decide)), ?_, ?_⟩
  · rw [hm]
    have c : ∀ k < 6, (⟨b + BitVec.ofNat 64 o, 48⟩ : Region).Contains (b + BitVec.ofNat 64 (o + 8 * k)) 8 :=
      fun k hk => Offset.contains b (by omega) (by omega) (by omega)
    have c0 := c 0 (by decide)
    have c1 := c 1 (by decide)
    have c2 := c 2 (by decide)
    have c3 := c 3 (by decide)
    have c4 := c 4 (by decide)
    have c5 := c 5 (by decide)
    simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at c0 c1 c2 c3 c4 c5
    exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW
      (List.mem_singleton_self _) _ c1).writeW (List.mem_singleton_self _) _ c2).writeW
      (List.mem_singleton_self _) _ c3).writeW (List.mem_singleton_self _) _ c4).writeW
      (List.mem_singleton_self _) _ c5
  · rw [d6_add]
    have w : ∀ k < 6, dw s12.mem b (o + 8 * k) = dw s.mem A (8 * k) := by
      intro k hk
      rw [hm]
      obtain rfl | rfl | rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
      all_goals simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul]
      all_goals (repeat rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)])
      all_goals rw [dw_write_self]
      all_goals (try rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)])
      exacts [by rw [v0]; rfl, by rw [v1]; rfl, by rw [v2]; rfl, by rw [v3]; rfl, by rw [v4]; rfl,
        by rw [v5]; rfl]
    simp only [E6, d6, val6, colsV, w 0 (by decide), w 1 (by decide), w 2 (by decide), w 3 (by decide),
      w 4 (by decide), w 5 (by decide)]
    omega

/-- The product's words, as `reduce` reads them. -/
theorem accW_prodV (m : Mem) (b : Addr) : accW ACC m b 12 = prodV m b := by
  rw [accW_eq]
  simp only [colsV, prodV, upW, T, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.zero_add,
    Nat.reducePow, Nat.one_mul]
  omega

/-- `b + o` from `W`, for `b = W + e`. -/
theorem off_add (W : Addr) (e o : Nat) :
    W + BitVec.ofNat 64 e + BitVec.ofNat 64 o = W + BitVec.ofNat 64 (e + o) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- The six doublewords at `W + x`, through a frame of a region apart from them. -/
theorem d6_frame {m m' : Mem} {W : Addr} {e k x : Nat} (hf : Frame [⟨W + BitVec.ofNat 64 e, k⟩] m m')
    (hd : x + 48 ≤ e ∨ e + k ≤ x) (hx : x + 48 ≤ 2 ^ 64) (he : e + k ≤ 2 ^ 64) :
    d6 m' (W + BitVec.ofNat 64 x) = d6 m (W + BitVec.ofNat 64 x) := by
  rw [d6_add, d6_add]
  exact val6_congr fun i hi => dw_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint W (by omega) (by omega) he

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

/-- A pointer to the `48` bytes at `W + x` of the working space. -/
theorem WsAt.inR {W : Addr} {s : State} (h : WsAt W s) {x : Nat} (hx : x + 48 ≤ 8192) :
    ∀ j < 6, InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 x + BitVec.ofNat 64 (8 * j)) 8 := fun j hj => by
  rw [off_add]
  obtain ⟨r, hr, hc⟩ := VG.Proof.X25519.RISCV64.in_base (n := 8) h.wr (d := x + 8 * j) (by omega) (by omega)
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem WsAt.inW {W : Addr} {s : State} (h : WsAt W s) {x : Nat} (hx : x + 48 ≤ 8192) :
    ∀ j < 6, InRegions s.wr (W + BitVec.ofNat 64 x + BitVec.ofNat 64 (8 * j)) 8 := fun j hj => by
  rw [off_add]
  exact VG.Proof.X25519.RISCV64.in_base h.wr (by omega) (by omega)

/-- The regions `mulCore` writes, from `W`: the copies, the product and the result. -/
abbrev mulW (W : Addr) (o : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 3712, 48⟩, ⟨W + BitVec.ofNat 64 3760, 48⟩, ⟨W + BitVec.ofNat 64 3808, 96⟩,
    ⟨W + BitVec.ofNat 64 o, 48⟩]

/-- An operand apart from the copies and the product. -/
abbrev Apart (x : Nat) : Prop := x + 48 ≤ 3712 ∨ 3904 ≤ x

theorem P_pos : 0 < P := by unfold P Spec.P384.p; omega

/-- `mulWith red (sumWith ks)`: `[t2] = [t4] [t5] 2⁻³⁸⁴ mod m`, for a reduction
`red` as `reduce_ok`'s and the words of `2³⁸⁴ - m` put into `t0` by `ks`. -/
theorem mulWith_ok {red : List Instr} {ks : List (List Instr)} {N : Nat → Nat} {M : Nat} (hM0 : 0 < M)
    (hN : ∀ j, N j < 2 ^ 64) (hk : ∀ j < 6, KOk (ks.getD j []) j N) (hNv : colsV N 6 + M = 2 ^ 384)
    (hred : ∀ {b : Addr} {s : State}, Ctx b s → WP isa (.block red) s fun s' =>
      Ctx b s' ∧ Rest clobM s s' ∧ Frame [AR ACC b] s.mem s'.mem ∧ (s'.gpr XC).toNat ≤ 1 ∧
      ∃ Q, Q < 2 ^ 384 ∧ (xv s' + 2 ^ 384 * (s'.gpr XC).toNat) * 2 ^ 384 = prodV s.mem b + Q * M)
    {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 48 ≤ 8192) (hb : bb + 48 ≤ 8192) (ho : o + 48 ≤ 8192) (hdb : Apart bb)
    (hB : d6 s.mem (W + BitVec.ofNat 64 bb) < M) :
    WP isa (mulWith red (sumWith ks)) s fun s' =>
      d6 s'.mem (W + BitVec.ofNat 64 o) < M ∧
      d6 s'.mem (W + BitVec.ofNat 64 o) * 2 ^ 384 % M =
        d6 s.mem (W + BitVec.ofNat 64 a) * d6 s.mem (W + BitVec.ofNat 64 bb) % M ∧
      Frame (mulW W o) s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hc := hw.ctx
  have alA : (W + BitVec.ofNat 64 a).toNat % 8 = 0 := al8 hw.al ha8
  have alB : (W + BitVec.ofNat 64 bb).toNat % 8 = 0 := al8 hw.al hb8
  have eMA : W + BitVec.ofNat 64 2048 + BitVec.ofNat 64 MA = W + BitVec.ofNat 64 3712 := off_add _ _ _
  have eMB : W + BitVec.ofNat 64 2048 + BitVec.ofNat 64 MB = W + BitVec.ofNat 64 3760 := off_add _ _ _
  have eAC : W + BitVec.ofNat 64 2048 + BitVec.ofNat 64 ACC = W + BitVec.ofNat 64 3808 := off_add _ _ _
  -- The product at `ACC`, by either branch.
  have hprod : WP isa prodCode s fun s' =>
      Ctx (W + BitVec.ofNat 64 2048) s' ∧ Rest clob64 s s' ∧ Frame (mulW W o) s.mem s'.mem ∧
      prodV s'.mem (W + BitVec.ofNat 64 2048) =
        d6 s.mem (W + BitVec.ofNat 64 a) * d6 s.mem (W + BitVec.ofNat 64 bb) := by
    refine WP.ite (s.gpr .t4 == s.gpr .t5) rfl (fun heq => ?_) (fun _ => ?_)
    · have hab : W + BitVec.ofNat 64 a = W + BitVec.ofNat 64 bb := by
        rw [← h4, ← h5]; exact beq_iff_eq.mp heq
      refine WP.block_append (WP.mono (copyIn_ok hc (p := .t4) h4 (by decide) alA (hw.inR ha)
        (o := MA) (by decide) (by decide)) fun s1 ⟨c1, r1, f1, v1⟩ => ?_)
      refine WP.mono (square_ok (acc := ACC) (x := MA) (by decide) (by decide) (by decide) (by decide) c1)
        fun s2 ⟨c2, r2, f2, v2⟩ => ⟨c2, (r1.mono (by decide)).trans r2, ?_, ?_⟩
      · rw [eMA] at f1
        simp only [AR, eAC] at f2
        exact (f1.mono (by simp)).trans (f2.mono (by simp))
      · rw [← accW_prodV, v2, ← d6_add, v1, ← hab]
    · refine WP.block_append (WP.block_append (WP.mono
        (copyIn_ok hc (p := .t4) h4 (by decide) alA (hw.inR ha) (o := MA) (by decide) (by decide))
        fun s1 ⟨c1, r1, f1, v1⟩ => WP.mono (copyIn_ok c1 (p := .t5) (by rw [r1.gpr _ (by decide), h5])
          (by decide) alB ((hw.of_rest r1 (by decide)).inR hb) (o := MB) (by decide) (by decide))
        fun s2 ⟨c2, r2, f2, v2⟩ => ?_))
      refine WP.mono (product_ok (acc := ACC) (x := MA) (y := MB) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) c2) fun s3 ⟨c3, r3, f3, v3⟩ => ⟨c3, ((r1.trans r2).mono (by decide)).trans r3, ?_, ?_⟩
      · rw [eMA] at f1
        rw [eMB] at f2
        simp only [AR, eAC] at f3
        exact ((f1.mono (by simp)).trans (f2.mono (by simp))).trans (f3.mono (by simp))
      · rw [eMA] at f1 v1
        rw [eMB] at f2 v2
        rw [← accW_prodV, v3, ← d6_add, ← d6_add, eMA, eMB, v2, d6_frame f1 (by unfold Apart at hdb; omega)
          (by omega) (by omega), d6_frame f2 (x := 3712) (by omega) (by omega) (by omega), v1]
  refine WP.seq (WP.mono hprod fun s1 ⟨c1, r1, f1, v1⟩ => ?_)
  refine WP.block_append (WP.mono (hred c1) fun s2 ⟨c2, r2, f2, x2, Q, hQ, hv2⟩ => ?_)
  have r12 : Rest clobM s s2 := (r1.mono (by decide) : Rest clobM _ _).trans r2
  have hw2 : WsAt W s2 := hw.of_rest r12 (by decide)
  have hlt : prodV s1.mem (W + BitVec.ofNat 64 2048) < 2 ^ 384 * M := by
    rw [v1]
    exact @Nat.mul_lt_mul_of_lt_of_le (d6 s.mem (W + BitVec.ofNat 64 a)) (2 ^ 384)
      (d6 s.mem (W + BitVec.ofNat 64 bb)) M (d6_lt _ _) (Nat.le_of_lt hB) hM0
  have hx : xv s2 + 2 ^ 384 * (s2.gpr XC).toNat < 2 * M := by
    generalize xv s2 + 2 ^ 384 * (s2.gpr XC).toNat = x at hv2 ⊢
    generalize (2 : Nat) ^ 384 = R at hQ hv2 hlt ⊢
    have h1 : Q * M < R * M := Nat.mul_lt_mul_of_pos_right hQ hM0
    have h2 : x * R < 2 * M * R := by
      rw [hv2]
      calc _ < R * M + R * M := Nat.add_lt_add hlt h1
        _ = 2 * M * R := by rw [← Nat.two_mul, Nat.mul_comm R M, Nat.mul_assoc]
    exact Nat.lt_of_mul_lt_mul_right h2
  refine WP.mono (csubWith_ok hN hk hNv (O := W + BitVec.ofNat 64 o) (by rw [r12.gpr _ (by decide), h2])
    (al8 hw.al ho8) (hw2.inW ho) x2 hx) fun s3 ⟨v3, f3, g3, rd3, wr3, sp3⟩ => ?_
  refine ⟨by rw [v3]; exact Nat.mod_lt _ hM0, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [v3, Nat.mod_mul_mod, hv2, Nat.add_mul_mod_self_right, v1]
  · simp only [AR, eAC] at f2
    exact f1.trans ((f2.mono (by simp)).trans (f3.mono (by simp)))
  · have sC : ∀ x ∈ clobC, x ∈ clobM := by decide
    rw [g3 r (fun h => hr (sC r h)), r12.gpr r hr]
  · rw [rd3, r2.rd, r1.rd]
  · rw [wr3, r2.wr, r1.wr]
  · rw [sp3, r2.sp, r1.sp]

/-- `mulCore`: `[t2] = [t4] [t5] 2⁻³⁸⁴ mod p`. -/
theorem mulCore_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 48 ≤ 8192) (hb : bb + 48 ≤ 8192) (ho : o + 48 ≤ 8192) (hdb : Apart bb)
    (hB : d6 s.mem (W + BitVec.ofNat 64 bb) < P) :
    WP isa mulCore s fun s' =>
      d6 s'.mem (W + BitVec.ofNat 64 o) < P ∧
      d6 s'.mem (W + BitVec.ofNat 64 o) * 2 ^ 384 % P =
        d6 s.mem (W + BitVec.ofNat 64 a) * d6 s.mem (W + BitVec.ofNat 64 bb) % P ∧
      Frame (mulW W o) s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  mulWith_ok (red := reduce) (ks := sumPKs) (N := NP) (M := P) P_pos NP_lt kP_ok NP_val
    (fun hc => WP.mono (reduce_ok hc) fun _ ⟨c, r, f, x, q⟩ => ⟨c, r.mono (by decide), f, x, q⟩)
    hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB

end VG.Proof.Weierstrass.RISCV64.P384Field

/-!
## P-384's field on RISC-V: sums and differences

`addCore` (`addCore_ok`): the operands' words loaded a word at a time and
summed with carries (`addSum_ok`, below `2p`), reduced by `csub`. `subCore`
(`subCore_ok`): their difference with borrows (`subDiff_ok`), and `p` added
back under the mask of the borrow, a word at a time, each stored at `[t2]`
(`addMs_ok`).
-/

namespace VG.Proof.Weierstrass.RISCV64.P384Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P384Field
open VG.Proof.X25519.RISCV64 (Ctx Rest)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt clob64 al8 colsV dw_write_self dw_write_other)
open VG.Proof.Weierstrass.RISCV64.P256Field (adc_ok sbb_ok upd_keeps)

/-- The registers of a sum or a difference. -/
abbrev clobS : List Reg := [.t5, .t6, .t3, .t4, .a1, .a4, .a2, .a5, .a6, .t0]

/-- Word `j` of both operands, at `a0` and `a7`, into `X j` and `a5`. -/
theorem ld2_ok {A B : Addr} {s : State} (hA : s.gpr .a0 = A) (hB : s.gpr .a7 = B) {j : Nat} (hj : j < 6)
    (halA : A.toNat % 8 = 0) (halB : B.toNat % 8 = 0)
    (hrA : ∀ j < 6, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * j)) 8)
    (hrB : ∀ j < 6, InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (8 * j)) 8)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', (s'.gpr (X j)).toNat = dw s.mem A (8 * j) → (s'.gpr .a5).toNat = dw s.mem B (8 * j) →
      Keeps [X j, .a5] s s' → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d (X j) .a0 (8 * j) :: .load .d .a5 .a7 (8 * j) :: is)) s Q := by
  obtain ⟨-, x5, -, x7, -, xa, -⟩ := X_facts j hj
  refine wp_ld (by omega) (by rw [hA]) (al8 halA (by omega)) (hrA j hj) fun s1 u1 => ?_
  refine wp_ld (by omega) (by rw [u1.other _ (Ne.symm x7), hB]) (al8 halB (by omega))
    (by rw [u1.rd, u1.wr]; exact hrB j hj) fun s2 u2 => ?_
  exact k s2 (by rw [u2.other _ x5, u1.gpr]; rfl) (by rw [u2.gpr, u1.mem]; rfl)
    ((upd_keeps u1).trans (upd_keeps u2))

/-- After `j` words of the sum of `[A]` and `[B]`, from `s0`. -/
structure AddInv (A B : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobS → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  cy : (s.gpr .a2).toNat ≤ 1
  val : colsV (fun k => (s.gpr (X k)).toNat) j + (2 ^ 64) ^ j * (s.gpr .a2).toNat =
    colsV (fun k => dw s0.mem A (8 * k) + dw s0.mem B (8 * k)) j

theorem X_clobS : ∀ j < 6, X j ∈ clobS := by decide

/-- Word `j` of the sum. -/
theorem addStep_ok {A B : Addr} {s0 : State} (hA : s0.gpr .a0 = A) (hB : s0.gpr .a7 = B)
    (halA : A.toNat % 8 = 0) (halB : B.toNat % 8 = 0)
    (hrA : ∀ j < 6, InRegions (s0.rd ++ s0.wr) (A + BitVec.ofNat 64 (8 * j)) 8)
    (hrB : ∀ j < 6, InRegions (s0.rd ++ s0.wr) (B + BitVec.ofNat 64 (8 * j)) 8)
    {j : Nat} (hj : j < 6) {s : State} (h : AddInv A B s0 j s) :
    WP isa (.block (([.load .d (X j) .a0 (8 * j), .load .d .a5 .a7 (8 * j)] : List Instr) ++ adcWord (X j) .a5)) s
      (AddInv A B s0 (j + 1)) := by
  obtain ⟨x2, x5, x6, -, -, -, -, -, -, -, xne⟩ := X_facts j hj
  have rd : s.rd ++ s.wr = s0.rd ++ s0.wr := by rw [h.rd, h.wr]
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine ld2_ok (by rw [h.gpr _ (by decide), hA]) (by rw [h.gpr _ (by decide), hB]) hj halA halB
    (by rw [rd]; exact hrA) (by rw [rd]; exact hrB) fun s1 ex ey k1 => ?_
  refine WP.mono (adc_ok (d := X j) (x := X j) (y := .a5) (c := .a2) (u := .a6) x5 x2 (Ne.symm x6) (by decide))
    fun s2 ⟨e2, k2⟩ => ?_
  have ec : s1.gpr .a2 = s.gpr .a2 := k1.1 _ (by simp [Ne.symm x2])
  have e2' := e2 (by rw [ec]; exact h.cy)
  rw [ex, ey, ec, h.mem] at e2'
  have g : ∀ k < 6, k ≠ j → s2.gpr (X k) = s.gpr (X k) := fun k hk hkj => by
    obtain ⟨y2, y5, y6, -⟩ := X_facts k hk
    rw [k2.1 _ (by simp [xne k hk hkj, y6, y2]), k1.1 _ (by simp [xne k hk hkj, y5])]
  have kk := k1.trans k2
  refine ⟨fun r hr => ?_, by rw [kk.2.1, h.mem], by rw [kk.2.2.1, h.rd], by rw [kk.2.2.2.1, h.wr],
    by rw [kk.2.2.2.2, h.sp], ?_, ?_⟩
  · have n1 : r ≠ X j := fun e => hr (e ▸ X_clobS j hj)
    have n5 : r ≠ .a5 := fun e => hr (by rw [e]; decide)
    have n6 : r ≠ .a6 := fun e => hr (by rw [e]; decide)
    have n2 : r ≠ .a2 := fun e => hr (by rw [e]; decide)
    rw [k2.1 r (by simp [n1, n6, n2]), k1.1 r (by simp [n1, n5]), h.gpr r hr]
  · have := (s2.gpr (X j)).isLt
    have := dw_lt s0.mem A (8 * j); have := dw_lt s0.mem B (8 * j); have := h.cy
    omega
  · have hv := h.val
    have hc : colsV (fun k => (s2.gpr (X k)).toNat) j = colsV (fun k => (s.gpr (X k)).toNat) j :=
      colsV_congr' fun k hk => by rw [g k (by omega) (by omega)]
    show colsV (fun k => (s2.gpr (X k)).toNat) j + (2 ^ 64) ^ j * (s2.gpr (X j)).toNat +
        (2 ^ 64) ^ (j + 1) * (s2.gpr .a2).toNat =
      colsV (fun k => dw s0.mem A (8 * k) + dw s0.mem B (8 * k)) j +
        (2 ^ 64) ^ j * (dw s0.mem A (8 * j) + dw s0.mem B (8 * j))
    rw [hc, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ .., ← hv]
    generalize (2 ^ 64) ^ j = E at *
    generalize colsV (fun k => (s.gpr (X k)).toNat) j = C at *
    have key : E * (s2.gpr (X j)).toNat + E * 2 ^ 64 * (s2.gpr .a2).toNat =
        E * (s.gpr .a2).toNat + E * (dw s0.mem A (8 * j) + dw s0.mem B (8 * j)) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, e2']; congr 1; omega
    omega

/-- `movAB` and the carry or borrow zeroed: from `s`, with `a0 = [t4]`, `a7 = [t5]`. -/
theorem movAB_ok {s : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .a0 = s.gpr .t4 → s'.gpr .a7 = s.gpr .t5 → (s'.gpr .a2).toNat = 0 →
      Rest [.a0, .a7, .a2] s s' → s'.mem = s.mem → WP isa (.block is) s' Q) :
    WP isa (.block (movAB ++ .li .a2 0 :: is)) s Q := by
  unfold movAB
  refine wp_addi (imm := 0) (by decide) fun s1 u1 => wp_addi (imm := 0) (by decide) fun s2 u2 =>
    wp_li (imm := 0) (by decide) fun s3 u3 => k s3 ?_ ?_ (by rw [u3.gpr]; rfl)
      ((u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))))
      (by rw [u3.mem, u2.mem, u1.mem])
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; simp
  · rw [u3.other _ (by decide), u2.gpr, u1.other _ (by decide)]; simp

/-- The sum of `[t4]` and `[t5]` into `X` and `XC`. -/
theorem addSum_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ha : a + 48 ≤ 8192) (hb : bb + 48 ≤ 8192) :
    WP isa (.block addSum) s fun s' =>
      xv s' + 2 ^ 384 * (s'.gpr XC).toNat = d6 s.mem (W + BitVec.ofNat 64 a) + d6 s.mem (W + BitVec.ofNat 64 bb) ∧
      (s'.gpr XC).toNat ≤ 1 ∧ Rest clobM s s' ∧ s'.mem = s.mem := by
  unfold addSum
  refine movAB_ok fun s1 e0 e7 e2 r1 m1 => ?_
  have hw1 : WsAt W s1 := hw.of_rest r1 (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (AddInv (W + BitVec.ofNat 64 a) (W + BitVec.ofNat 64 bb) s1)
    (fun j s hj h => addStep_ok (by rw [e0, h4]) (by rw [e7, h5]) (al8 hw.al ha8) (al8 hw.al hb8)
      (hw1.inR ha) (hw1.inR hb) hj h) 6 (Nat.le_refl _) s1
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, by rw [e2]; omega, by simp only [colsV, e2]⟩) fun s2 h2 => ?_
  have hv := h2.val
  rw [VG.Proof.X448.RISCV64.R64.colsV_add, m1] at hv
  refine ⟨by rw [two384]; exact hv, h2.cy, r1.mono (by decide) |>.trans ⟨fun r hr => h2.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h | h | h | h | h | h | h | h | h <;> simp [h])), h2.rd, h2.wr, h2.sp⟩,
    by rw [h2.mem, m1]⟩

/-- `addCore`: `[t2] = ([t4] + [t5]) mod p`, for a sum below `2p`. -/
theorem addCore_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 48 ≤ 8192) (hb : bb + 48 ≤ 8192) (ho : o + 48 ≤ 8192)
    (hab : d6 s.mem (W + BitVec.ofNat 64 a) + d6 s.mem (W + BitVec.ofNat 64 bb) < 2 * P) :
    WP isa (.block addCore) s fun s' =>
      d6 s'.mem (W + BitVec.ofNat 64 o) =
        (d6 s.mem (W + BitVec.ofNat 64 a) + d6 s.mem (W + BitVec.ofNat 64 bb)) % P ∧
      Frame [⟨W + BitVec.ofNat 64 o, 48⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold addCore
  refine WP.block_append (WP.mono (addSum_ok hw h4 h5 ha8 hb8 ha hb) fun s1 ⟨v1, c1, r1, m1⟩ => ?_)
  have hw1 : WsAt W s1 := hw.of_rest r1 (by decide)
  refine WP.mono (csub_ok (O := W + BitVec.ofNat 64 o) (by rw [r1.gpr _ (by decide), h2]) (al8 hw.al ho8)
    (hw1.inW ho) c1 (by rw [v1]; exact hab)) fun s2 ⟨v2, f2, g2, rd2, wr2, sp2⟩ => ?_
  refine ⟨by rw [v2, v1], by rw [← m1]; exact f2, fun r hr => ?_, by rw [rd2, r1.rd], by rw [wr2, r1.wr],
    by rw [sp2, r1.sp]⟩
  have hC : r ∉ clobC := fun h => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h | h | h <;> simp [h])
  rw [g2 r hC, r1.gpr r hr]

/-- After `j` words of the difference of `[A]` and `[B]`, from `s0`. -/
structure SubInv (A B : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobS → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  cy : (s.gpr .a2).toNat ≤ 1
  val : colsV (fun k => (s.gpr (X k)).toNat) j + colsV (fun k => dw s0.mem B (8 * k)) j =
    colsV (fun k => dw s0.mem A (8 * k)) j + (2 ^ 64) ^ j * (s.gpr .a2).toNat

/-- Word `j` of the difference. -/
theorem subStep_ok {A B : Addr} {s0 : State} (hA : s0.gpr .a0 = A) (hB : s0.gpr .a7 = B)
    (halA : A.toNat % 8 = 0) (halB : B.toNat % 8 = 0)
    (hrA : ∀ j < 6, InRegions (s0.rd ++ s0.wr) (A + BitVec.ofNat 64 (8 * j)) 8)
    (hrB : ∀ j < 6, InRegions (s0.rd ++ s0.wr) (B + BitVec.ofNat 64 (8 * j)) 8)
    {j : Nat} (hj : j < 6) {s : State} (h : SubInv A B s0 j s) :
    WP isa (.block (([.load .d (X j) .a0 (8 * j), .load .d .a5 .a7 (8 * j)] : List Instr) ++ sbbWord (X j) .a5)) s
      (SubInv A B s0 (j + 1)) := by
  obtain ⟨x2, x5, x6, -, x0, -, -, -, -, -, xne⟩ := X_facts j hj
  have rd : s.rd ++ s.wr = s0.rd ++ s0.wr := by rw [h.rd, h.wr]
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine ld2_ok (by rw [h.gpr _ (by decide), hA]) (by rw [h.gpr _ (by decide), hB]) hj halA halB
    (by rw [rd]; exact hrA) (by rw [rd]; exact hrB) fun s1 ex ey k1 => ?_
  refine WP.mono (sbb_ok (d := X j) (x := X j) (y := .a5) (c := .a2) (u := .a6) (v := .t0) x2 (Ne.symm x6)
    (by decide) (Ne.symm x0) (by decide) (by decide) (Ne.symm x6) (by decide)) fun s2 ⟨e2, k2⟩ => ?_
  have ec : s1.gpr .a2 = s.gpr .a2 := k1.1 _ (by simp [Ne.symm x2])
  have e2' := e2 (by rw [ec]; exact h.cy)
  rw [ex, ey, ec, h.mem] at e2'
  have g : ∀ k < 6, k ≠ j → s2.gpr (X k) = s.gpr (X k) := fun k hk hkj => by
    obtain ⟨y2, y5, y6, -, y0, -⟩ := X_facts k hk
    rw [k2.1 _ (by simp [xne k hk hkj, y6, y2, y0]), k1.1 _ (by simp [xne k hk hkj, y5])]
  have kk := k1.trans k2
  refine ⟨fun r hr => ?_, by rw [kk.2.1, h.mem], by rw [kk.2.2.1, h.rd], by rw [kk.2.2.2.1, h.wr],
    by rw [kk.2.2.2.2, h.sp], e2'.2, ?_⟩
  · have n1 : r ≠ X j := fun e => hr (e ▸ X_clobS j hj)
    have n5 : r ≠ .a5 := fun e => hr (by rw [e]; decide)
    have n6 : r ≠ .a6 := fun e => hr (by rw [e]; decide)
    have n2 : r ≠ .a2 := fun e => hr (by rw [e]; decide)
    have n0 : r ≠ .t0 := fun e => hr (by rw [e]; decide)
    rw [k2.1 r (by simp [n1, n6, n2, n0]), k1.1 r (by simp [n1, n5]), h.gpr r hr]
  · have hv := h.val
    have hc : colsV (fun k => (s2.gpr (X k)).toNat) j = colsV (fun k => (s.gpr (X k)).toNat) j :=
      colsV_congr' fun k hk => by rw [g k (by omega) (by omega)]
    show colsV (fun k => (s2.gpr (X k)).toNat) j + (2 ^ 64) ^ j * (s2.gpr (X j)).toNat +
        (colsV (fun k => dw s0.mem B (8 * k)) j + (2 ^ 64) ^ j * dw s0.mem B (8 * j)) =
      colsV (fun k => dw s0.mem A (8 * k)) j + (2 ^ 64) ^ j * dw s0.mem A (8 * j) +
        (2 ^ 64) ^ (j + 1) * (s2.gpr .a2).toNat
    rw [hc, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..]
    generalize (2 ^ 64) ^ j = E at *
    generalize colsV (fun k => (s.gpr (X k)).toNat) j = C at *
    have key : E * (s2.gpr (X j)).toNat + E * dw s0.mem B (8 * j) + E * (s.gpr .a2).toNat =
        E * dw s0.mem A (8 * j) + E * 2 ^ 64 * (s2.gpr .a2).toNat := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add, e2'.1]
    omega

/-- The difference of `[t4]` and `[t5]` into `X`, with its borrow in `a2`. -/
theorem subDiff_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ha : a + 48 ≤ 8192) (hb : bb + 48 ≤ 8192) :
    WP isa (.block subDiff) s fun s' =>
      xv s' + d6 s.mem (W + BitVec.ofNat 64 bb) = d6 s.mem (W + BitVec.ofNat 64 a) + 2 ^ 384 * (s'.gpr .a2).toNat ∧
      (s'.gpr .a2).toNat ≤ 1 ∧ Rest clobM s s' ∧ s'.mem = s.mem := by
  unfold subDiff
  refine movAB_ok fun s1 e0 e7 e2 r1 m1 => ?_
  have hw1 : WsAt W s1 := hw.of_rest r1 (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (SubInv (W + BitVec.ofNat 64 a) (W + BitVec.ofNat 64 bb) s1)
    (fun j s hj h => subStep_ok (by rw [e0, h4]) (by rw [e7, h5]) (al8 hw.al ha8) (al8 hw.al hb8)
      (hw1.inR ha) (hw1.inR hb) hj h) 6 (Nat.le_refl _) s1
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, by rw [e2]; omega, by simp only [colsV, e2]⟩) fun s2 h2 => ?_
  have hv := h2.val
  rw [m1] at hv
  refine ⟨by rw [two384]; exact hv, h2.cy, r1.mono (by decide) |>.trans ⟨fun r hr => h2.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h | h | h | h | h | h | h | h | h <;> simp [h])), h2.rd, h2.wr, h2.sp⟩,
    by rw [h2.mem, m1]⟩

/-- A block that puts word `j` of `m` under the mask `t0` into `a6`. -/
def KMOk (k : List Instr) (j : Nat) (PW : Nat → Nat) : Prop :=
  ∀ s : State, IsMask (s.gpr .t0) →
    WP isa (.block k) s fun s' =>
      (s'.gpr .a6).toNat = (if s.gpr .t0 = BitVec.allOnes 64 then PW j else 0) ∧ Keeps [.a6] s s'

/-- The registers of the sum of `m` under the mask. -/
abbrev clobA : List Reg := [.t5, .t6, .t3, .t4, .a1, .a4, .a0, .a6, .a7]

/-- After `j` words of `x + (m ∧ M)` from `s0`, stored at `O` (in `t2`). -/
structure AddMInv (O : Addr) (PW : Nat → Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobA → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨O, 48⟩] s0.mem s.mem
  hi : ∀ k, j ≤ k → k < 6 → s.gpr (X k) = s0.gpr (X k)
  cy : (s.gpr .a7).toNat ≤ 1
  val : colsV (fun k => dw s.mem O (8 * k)) j + (2 ^ 64) ^ j * (s.gpr .a7).toNat =
    colsV (fun k => (s0.gpr (X k)).toNat + if s0.gpr .t0 = BitVec.allOnes 64 then PW k else 0) j

theorem X_clobA : ∀ j < 6, X j ∈ clobA := by decide

/-- Word `j` of `x + (m ∧ M)`. -/
theorem addMStep_ok {O : Addr} {PW : Nat → Nat} (hP : ∀ j, PW j < 2 ^ 64) {k : List Instr} {j : Nat}
    (hj : j < 6) (hk : KMOk k j PW) (hal : O.toNat % 8 = 0) {s0 s : State} (h2 : s0.gpr .t2 = O)
    (hm : IsMask (s0.gpr .t0))
    (hw : ∀ j < 6, InRegions s0.wr (O + BitVec.ofNat 64 (8 * j)) 8) (h : AddMInv O PW s0 j s) :
    WP isa (.block (k ++ addMWord j)) s (AddMInv O PW s0 (j + 1)) := by
  obtain ⟨-, -, x6, x7, x0, xa, -, x2, -, -, xne⟩ := X_facts j hj
  have ht0 : s.gpr .t0 = s0.gpr .t0 := h.gpr _ (by decide)
  refine WP.block_append (WP.mono (hk s (by rw [ht0]; exact hm)) fun s1 ⟨e1, k1⟩ => ?_)
  rw [ht0] at e1
  unfold addMWord
  refine WP.block_append (WP.mono (adc_ok (d := X j) (x := X j) (y := .a6) (c := .a7) (u := .a0) x6 x7
    (Ne.symm xa) (by decide)) fun s2 ⟨e2, k2⟩ => ?_)
  have g2 : ∀ r, r ∉ clobA → s2.gpr r = s0.gpr r := fun r hr => by
    have n1 : r ≠ X j := fun e => hr (e ▸ X_clobA j hj)
    have n6 : r ≠ .a6 := fun e => hr (by rw [e]; decide)
    have n7 : r ≠ .a7 := fun e => hr (by rw [e]; decide)
    have n0 : r ≠ .a0 := fun e => hr (by rw [e]; decide)
    rw [k2.1 _ (by simp [n1, n0, n7]), k1.1 _ (by simp [n6]), h.gpr r hr]
  have p2 : s2.gpr .t2 + BitVec.ofNat 64 (8 * j) = O + BitVec.ofNat 64 (8 * j) := by
    rw [g2 _ (by decide), h2]
  refine wp_sd (by omega) p2 (al8 hal (by omega)) (by rw [k2.2.2.2.1, k1.2.2.2.1, h.wr]; exact hw j hj)
    fun s3 u3 => WP.block_nil ?_
  have ex : s1.gpr (X j) = s0.gpr (X j) := by
    rw [k1.1 _ (by simp [x6]), h.hi j (Nat.le_refl _) hj]
  have ec : s1.gpr .a7 = s.gpr .a7 := k1.1 _ (by decide)
  have e2' := e2 (by rw [ec]; exact h.cy)
  rw [ex, ec, e1] at e2'
  have hm3 : s3.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j)) (s2.gpr (X j)) := by
    rw [u3.mem, k2.2.1, k1.2.1]
  have hPm : (if s0.gpr .t0 = BitVec.allOnes 64 then PW j else 0) < 2 ^ 64 := by
    split
    · exact hP j
    · omega
  refine ⟨fun r hr => by rw [u3.gpr]; exact g2 r hr, by rw [u3.rd, k2.2.2.1, k1.2.2.1, h.rd],
    by rw [u3.wr, k2.2.2.2.1, k1.2.2.2.1, h.wr], by rw [u3.sp, k2.2.2.2.2, k1.2.2.2.2, h.sp], ?_,
    fun k hk hk' => ?_, ?_, ?_⟩
  · rw [hm3]; exact h.frame.writeW (List.mem_singleton_self _) _ (out_contains O hj)
  · obtain ⟨-, -, y6, y7, -, ya, -⟩ := X_facts k hk'
    rw [u3.gpr, k2.1 _ (by simp [xne k hk' (by omega), ya, y7]), k1.1 _ (by simp [y6])]
    exact h.hi k (by omega) hk'
  · rw [u3.gpr]
    have := (s2.gpr (X j)).isLt; have := (s0.gpr (X j)).isLt; have := h.cy
    omega
  · have hv := h.val
    have hc : colsV (fun k => dw s3.mem O (8 * k)) j = colsV (fun k => dw s.mem O (8 * k)) j :=
      colsV_congr' fun k hk => by rw [hm3, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    show colsV (fun k => dw s3.mem O (8 * k)) j + (2 ^ 64) ^ j * dw s3.mem O (8 * j) +
        (2 ^ 64) ^ (j + 1) * (s3.gpr .a7).toNat =
      colsV (fun k => (s0.gpr (X k)).toNat + if s0.gpr .t0 = BitVec.allOnes 64 then PW k else 0) j +
        (2 ^ 64) ^ j * ((s0.gpr (X j)).toNat + if s0.gpr .t0 = BitVec.allOnes 64 then PW j else 0)
    rw [hc, hm3, dw_write_self, u3.gpr, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..,
      ← hv]
    generalize (if s0.gpr .t0 = BitVec.allOnes 64 then PW j else 0) = y at *
    generalize (2 ^ 64) ^ j = E at *
    generalize colsV (fun k => dw s.mem O (8 * k)) j = C at *
    have key : E * (s2.gpr (X j)).toNat + E * 2 ^ 64 * (s2.gpr .a7).toNat =
        E * (s.gpr .a7).toNat + E * ((s0.gpr (X j)).toNat + y) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, e2']; congr 1; omega
    omega

/-- The mask of a borrow. -/
theorem neg_mask {c : BitVec 64} (hc : c.toNat ≤ 1) :
    IsMask (0 - c) ∧ (0 - c = BitVec.allOnes 64 ↔ c.toNat = 1) := by
  have hc' : c = 0 ∨ c = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  rcases hc' with rfl | rfl <;> (unfold IsMask; decide)

theorem colsV_ite (c : Prop) [Decidable c] (f : Nat → Nat) (n : Nat) :
    colsV (fun k => if c then f k else 0) n = if c then colsV f n else 0 := by
  split
  · rfl
  · induction n with
    | zero => rfl
    | succ n ih => simp only [colsV, ih]; simp [*]

/-- `subWith ks`: `[t2] = ([t4] - [t5]) mod m`, for operands below `m`, where
`ks[j]` puts word `j` of `m` under the mask `t0` into `a6`. -/
theorem subWith_ok {ks : List (List Instr)} {PW : Nat → Nat} {M : Nat} (hP : ∀ j, PW j < 2 ^ 64)
    (hk : ∀ j < 6, KMOk (ks.getD j []) j PW) (hPv : colsV PW 6 = M)
    {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 48 ≤ 8192) (hb : bb + 48 ≤ 8192) (ho : o + 48 ≤ 8192)
    (hA : d6 s.mem (W + BitVec.ofNat 64 a) < M) (hB : d6 s.mem (W + BitVec.ofNat 64 bb) < M) :
    WP isa (.block (subWith ks)) s fun s' =>
      d6 s'.mem (W + BitVec.ofNat 64 o) =
        (d6 s.mem (W + BitVec.ofNat 64 a) + M - d6 s.mem (W + BitVec.ofNat 64 bb)) % M ∧
      Frame [⟨W + BitVec.ofNat 64 o, 48⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold subWith
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (subDiff_ok hw h4 h5 ha8 hb8 ha hb) fun s1 ⟨v1, c1, r1, m1⟩ => ?_)
  rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_li (imm := 0) (by decide) fun s2 u2 => wp_sub fun s3 u3 => wp_li (imm := 0) (by decide)
    fun s4 u4 => ?_
  have hm : IsMask (s4.gpr .t0) ∧ (s4.gpr .t0 = BitVec.allOnes 64 ↔ (s1.gpr .a2).toNat = 1) := by
    rw [u4.other _ (by decide), u3.gpr, u2.gpr, u2.other _ (by decide)]
    exact neg_mask c1
  have r4 : Rest clobM s s4 := r1.trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
    (u4.rest (by decide))))
  have hw4 : WsAt W s4 := hw.of_rest r4 (by decide)
  have p4 : s4.gpr .t2 = W + BitVec.ofNat 64 o := by rw [r4.gpr _ (by decide), h2]
  refine WP.mono (wp_range_flatMap (M := isa) (AddMInv (W + BitVec.ofNat 64 o) PW s4)
    (fun j s hj h => addMStep_ok hP hj (hk j hj) (al8 hw.al ho8) p4 hm.1 (hw4.inW ho) h) 6 (Nat.le_refl _) s4
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl, by rw [u4.gpr]; decide,
      by simp only [colsV, u4.gpr]; rfl⟩) fun s5 h5 => ?_
  have hx4 : ∀ k < 6, s4.gpr (X k) = s1.gpr (X k) := fun k hk => by
    obtain ⟨-, -, -, x7, x0, -⟩ := X_facts k hk
    rw [u4.other _ x7, u3.other _ x0, u2.other _ x0]
  have hm4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, m1]
  have hv := h5.val
  rw [VG.Proof.X448.RISCV64.R64.colsV_add, colsV_ite, hPv] at hv
  have hxv : colsV (fun k => (s4.gpr (X k)).toNat) 6 = xv s1 := colsV_congr' fun k hk => by rw [hx4 k hk]
  rw [hxv] at hv
  have hd := d6_lt s5.mem (W + BitVec.ofNat 64 o)
  have hY : xv s1 < 2 ^ 384 := by rw [two384]; exact colsV_lt_of _ (fun _ => BitVec.isLt _) 6
  have hMl : M < 2 ^ 384 := by rw [two384, ← hPv]; exact colsV_lt_of PW hP 6
  have hc7 := h5.cy
  refine ⟨?_, by rw [← hm4]; exact h5.frame, fun r hr => ?_, by rw [h5.rd, r4.rd], by rw [h5.wr, r4.wr],
    by rw [h5.sp, r4.sp]⟩
  · have hge := hm.2
    replace hv : d6 s5.mem (W + BitVec.ofNat 64 o) + 2 ^ 384 * (s5.gpr .a7).toNat =
        xv s1 + if s4.gpr .t0 = BitVec.allOnes 64 then M else 0 := by
      rw [two384]; exact hv
    generalize d6 s5.mem (W + BitVec.ofNat 64 o) = D at *
    generalize xv s1 = Y at *
    generalize d6 s.mem (W + BitVec.ofNat 64 a) = A at *
    generalize d6 s.mem (W + BitVec.ofNat 64 bb) = B at *
    split at hv
    · rename_i h
      have h1 := hge.mp h
      rw [h1] at v1
      have hAB : A < B := by omega
      have hlt : A + M - B < M := by omega
      rw [Nat.mod_eq_of_lt hlt]
      omega
    · rename_i h
      have h0 : (s1.gpr .a2).toNat = 0 := by
        have := c1; have : ¬ (s1.gpr .a2).toNat = 1 := fun h' => h (hge.mpr h'); omega
      rw [h0] at v1
      have hBA : B ≤ A := by omega
      rw [show A + M - B = (A - B) + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
  · have hA' : r ∉ clobA := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h | h | h | h | h | h | h | h <;> simp [h])
    rw [h5.gpr r hA', r4.gpr r hr]

/-- `p`'s words. -/
def PWp (j : Nat) : Nat := [2 ^ 32 - 1, 2 ^ 64 - 2 ^ 32, 2 ^ 64 - 2, 2 ^ 64 - 1, 2 ^ 64 - 1, 2 ^ 64 - 1].getD j 0

theorem PWp_lt (j : Nat) : PWp j < 2 ^ 64 := by
  unfold PWp
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp

theorem PWp_val : colsV PWp 6 = P := by
  simp only [colsV, PWp, List.getD_cons_zero, List.getD_cons_succ]
  unfold P Spec.P384.p
  omega

theorem kmP_ok : ∀ j < 6, KMOk (subPKs.getD j []) j PWp := by
  intro j hj s hm
  obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  · exact wp_srl (by decide) fun s1 u1 => WP.block_nil ⟨by
      rw [u1.gpr]; rcases hm with h | h <;> rw [h] <;> decide, upd_keeps u1⟩
  · exact wp_sll (by decide) fun s1 u1 => WP.block_nil ⟨by
      rw [u1.gpr]; rcases hm with h | h <;> rw [h] <;> decide, upd_keeps u1⟩
  · exact wp_sll (by decide) fun s1 u1 => WP.block_nil ⟨by
      rw [u1.gpr]; rcases hm with h | h <;> rw [h] <;> decide, upd_keeps u1⟩
  all_goals exact wp_addi (imm := 0) (by decide) fun s1 u1 => WP.block_nil ⟨by
      rw [u1.gpr]; rcases hm with h | h <;> rw [h] <;> decide, upd_keeps u1⟩

/-- `subCore`: `[t2] = ([t4] - [t5]) mod p`, for operands below `p`. -/
theorem subCore_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 48 ≤ 8192) (hb : bb + 48 ≤ 8192) (ho : o + 48 ≤ 8192)
    (hA : d6 s.mem (W + BitVec.ofNat 64 a) < P) (hB : d6 s.mem (W + BitVec.ofNat 64 bb) < P) :
    WP isa (.block subCore) s fun s' =>
      d6 s'.mem (W + BitVec.ofNat 64 o) =
        (d6 s.mem (W + BitVec.ofNat 64 a) + P - d6 s.mem (W + BitVec.ofNat 64 bb)) % P ∧
      Frame [⟨W + BitVec.ofNat 64 o, 48⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  subWith_ok (ks := subPKs) (PW := PWp) (M := P) PWp_lt kmP_ok PWp_val hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hA hB

end VG.Proof.Weierstrass.RISCV64.P384Field

/-!
## P-384's field on RISC-V: operands at offsets not multiples of 8

The byte-wise copies of `fn`'s other branch: twelve words a byte at a time,
as Ed25519's eight (`Proof/Ed25519/RISCV64/Packed.lean`): the operands into
`SA` and `SB` of the own working space (`unpack12_ok`), and the result from
`SO` to `[o]` (`pack12_ok`).
-/

namespace VG.Proof.Weierstrass.RISCV64.P384Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Weierstrass.RISCV64.P384Field VG.Proof.X25519.RISCV64
open VG.Proof.Ed25519.RISCV64 (not_a4_a5)

/-- After `k` words of `pack p a dst` from `s0`. -/
structure PackInv12 (b q : Addr) (a dst : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.a4, .a5] s0 s
  frame : Frame [⟨q + BitVec.ofNat 64 dst, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, wd s.mem q (dst + 4 * j) = limb s0.mem b a j

theorem pack12_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) {p : Reg}
    (hp : p ∉ [Reg.a4, .a5]) (h14 : s0.gpr p = q) {a dst : Nat}
    (ha : a + 48 ≤ 2048) (ha4 : a % 4 = 0) (hdst : dst + 48 < 2048)
    (hw : ∀ k < 12, InRegions s0.wr (q + BitVec.ofNat 64 (dst + 4 * k)) 4)
    (hd : (⟨q + BitVec.ofNat 64 dst, 48⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 a, 48⟩) :
    WP isa (.block (pack p a dst)) s0 (PackInv12 b q a dst s0 12) := by
  have hp' := not_a4_a5 hp
  refine wp_range_flatMap (M := isa) (PackInv12 b q a dst s0) (fun k s hk h => ?_)
    12 (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  refine lw0_ok hcs (d := a + 4 * k) (by omega) (by omega) fun t1 v1 => ?_
  have hq1 : t1.gpr p = q := by rw [v1.other _ hp'.1, h.rest.gpr _ hp, h14]
  refine WP.mono (ByteLoad.storeLE32_ok (v := .a4) (tmp := .a5) (n := p) (off := dst + 4 * k)
    (by decide) hp'.2.symm (by omega) (by rw [hq1, v1.wr, h.rest.wr]; exact hw k hk)) fun t2 e2 => ?_
  have em : t2.mem = s.mem.writeW (q + BitVec.ofNat 64 (dst + 4 * k)) ((t1.gpr .a4).setWidth 32) := by
    rw [e2, RegUpd.mem_write, hq1]
    show t1.mem.writeW _ _ = _
    rw [v1.mem]
  have hr2 : Rest [.a4, .a5] t1 t2 := by
    rw [e2]
    exact ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ (not_a4_a5 hr).2, rfl, rfl, rfl⟩
  have hsrc : wd s.mem b (a + 4 * k) = limb s0.mem b a k := by
    refine wd_frame h.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine fun x hx hx' => hd x ?_ ?_
    · exact Region.sub_prefix (by omega) x hx'
    · exact Offset.sub b (d := a + 4 * k) (n := 4) (e := a) (k := 48) (by omega) (by omega) x hx
  refine ⟨h.rest.trans ((v1.rest (by decide)).trans hr2), ?_, fun j hj => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega)
  · rw [em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.outs j hj
    · rw [wd_write_self, toNat_lo32, v1.gpr, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _)]
      exact hsrc

/-- After `k` words of `unpack p o src` from `s0`. -/
structure UnpackInv12 (b : Addr) (o : Nat) (s0 : State) (f : Nat → Nat) (k : Nat) (s : State) : Prop where
  rest : Rest [.a4, .a5] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, limb s.mem b o j = f j

/-- `unpack p o src`: the words at `src` from `p` into the element at `o`. -/
theorem unpack12_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) {p : Reg}
    (hp : p ∉ [Reg.a4, .a5]) (h14 : s0.gpr p = q) {o src : Nat}
    (ho : o + 48 ≤ 2048) (ho4 : o % 4 = 0) (hsrc : src + 48 < 2048)
    (hr : ∀ k < 12, InRegions (s0.rd ++ s0.wr) (q + BitVec.ofNat 64 (src + 4 * k)) 4)
    (hd : (⟨q + BitVec.ofNat 64 src, 48⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 o, 48⟩) :
    WP isa (.block (unpack p o src)) s0 fun t =>
      Rest [.a4, .a5] s0 t ∧ Frame [⟨b + BitVec.ofNat 64 o, 48⟩] s0.mem t.mem ∧
      ∀ j < 12, limb t.mem b o j = wd s0.mem q (src + 4 * j) := by
  have hp' := not_a4_a5 hp
  let f := fun k => wd s0.mem q (src + 4 * k)
  refine WP.mono (wp_range_flatMap (M := isa) (UnpackInv12 b o s0 f) (fun k s hk h => ?_)
    12 (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩)
    fun t ht => ⟨ht.rest, ht.frame, ht.outs⟩
  have hq : s.gpr p = q := by rw [h.rest.gpr _ hp, h14]
  refine WP.append (ByteLoad.loadLE32_ok (d := .a4) (tmp := .a5) (n := p) (off := src + 4 * k)
    hp'.1.symm hp'.2.symm (by decide) (by omega)
    (by rw [hq, h.rest.rd, h.rest.wr]; exact hr k hk)) fun t1 e1 => ?_
  have hr1 : Rest [.a4, .a5] s t1 := by
    rw [e1]
    refine ⟨fun r hr' => ?_, rfl, rfl, rfl⟩
    rw [RegUpd.gpr_write_of_ne _ _ (not_a4_a5 hr').1, RegUpd.gpr_write_of_ne _ _ (not_a4_a5 hr').2]
  have hm1 : t1.mem = s.mem := by rw [e1]; rfl
  have hv : (t1.gpr .a4).toNat % 2 ^ 32 = f k := by
    rw [e1, RegUpd.gpr_write_self, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _), hq]
    show wd s.mem q (src + 4 * k) = _
    refine wd_frame h.frame fun r hr' => ?_
    rw [List.mem_singleton.mp hr']
    refine fun x hx hx' => hd x ?_ ?_
    · exact Offset.sub q (d := src + 4 * k) (n := 4) (e := src) (k := 48) (by omega) (by omega) x hx
    · exact Region.sub_prefix (by omega) x hx'
  refine sw0_ok ((hc.of_rest h.rest (by decide)).of_rest hr1 (by decide))
    (by omega) (by omega) fun u hu => WP.block_nil ?_
  have em : u.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 4 * k)) ((t1.gpr .a4).setWidth 32) := by
    rw [hu.mem, hm1]
  refine ⟨h.rest.trans (hr1.trans (hu.rest _)), ?_, fun j hj => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega)
  · rw [limb, em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.outs j hj
    · rw [wd_write_self, toNat_lo32, hv]


end VG.Proof.Weierstrass.RISCV64.P384Field

namespace VG.Proof.Weierstrass.RISCV64.P384Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P384Field
open VG.Proof.X25519.RISCV64 (Ctx Rest limb wd in_base)
open VG.Proof.X448.RISCV64.R64 (dw dw_split al8 colsV)

/-- Six doublewords are their twelve words. -/
theorem d6_congr_wd {m m' : Mem} {O O' : Addr} (h : ∀ j < 12, wd m' O' (4 * j) = wd m O (4 * j)) :
    d6 m' O' = d6 m O := by
  simp only [d6, colsV, dw_split, Nat.mul_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd]
  have e : ∀ j < 12, wd m' O' (4 * j) = wd m O (4 * j) := h
  rw [show (0 : Nat) = 4 * 0 from rfl, show (4 : Nat) = 4 * 1 from rfl, show (8 : Nat) = 4 * 2 from rfl,
    show (12 : Nat) = 4 * 3 from rfl, show (16 : Nat) = 4 * 4 from rfl, show (20 : Nat) = 4 * 5 from rfl,
    show (24 : Nat) = 4 * 6 from rfl, show (28 : Nat) = 4 * 7 from rfl, show (32 : Nat) = 4 * 8 from rfl,
    show (36 : Nat) = 4 * 9 from rfl, show (40 : Nat) = 4 * 10 from rfl, show (44 : Nat) = 4 * 11 from rfl]
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide), e 5 (by decide),
    e 6 (by decide), e 7 (by decide), e 8 (by decide), e 9 (by decide), e 10 (by decide), e 11 (by decide)]

theorem wd_off (m : Mem) (b : Addr) (o d : Nat) : wd m b (o + d) = wd m (b + BitVec.ofNat 64 o) d := by
  simp only [VG.Proof.X25519.RISCV64.wd, off_add]

/-- `unpack p o 0` of the operand at `W + x` into `W + 2048 + o`. -/
theorem unpack_ok {W : Addr} {s : State} (hw : WsAt W s) {p : Reg} (hp : p ∉ [Reg.a4, .a5]) {x : Nat}
    (h : s.gpr p = W + BitVec.ofNat 64 x) (hx : x + 48 ≤ 3712) {o : Nat} (ho : 1856 ≤ o) (ho' : o + 48 ≤ 2048)
    (ho4 : o % 4 = 0) :
    WP isa (.block (unpack p o 0)) s fun t =>
      Rest [.a4, .a5] s t ∧ Frame [⟨W + BitVec.ofNat 64 (2048 + o), 48⟩] s.mem t.mem ∧
      d6 t.mem (W + BitVec.ofNat 64 (2048 + o)) = d6 s.mem (W + BitVec.ofNat 64 x) := by
  refine WP.mono (unpack12_ok hw.ctx hp h (o := o) (src := 0) ho' ho4 (by decide)
    (fun k hk => by
      rw [Nat.zero_add, off_add]
      obtain ⟨r, hr, hc⟩ := in_base (n := 4) hw.wr (d := x + 4 * k) (by omega) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [off_add, Nat.add_zero, off_add]; exact Offset.disjoint W (by omega) (by omega) (by omega)))
    fun t ⟨r, f, v⟩ => ⟨r, by rw [off_add] at f; exact f, ?_⟩
  rw [← off_add]
  exact d6_congr_wd fun j hj => by rw [← wd_off, ← limb, v j hj, Nat.zero_add]

/-- The slow branch's copies in, and its pointers. -/
theorem slowIn_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha : a + 48 ≤ 3712) (hb : bb + 48 ≤ 3712) :
    WP isa (.block (([.addi .t1 .t2 0] : List Instr) ++ unpack .t4 SA 0 ++
        unpack .t5 SB 0 ++ ([.addi .t4 .a3 SA, .addi .t5 .a3 SB, .addi .t2 .a3 SO] : List Instr))) s
      fun t => WsAt W t ∧ t.gpr .t1 = W + BitVec.ofNat 64 o ∧ t.gpr .t4 = W + BitVec.ofNat 64 3904 ∧
        t.gpr .t5 = W + BitVec.ofNat 64 3952 ∧ t.gpr .t2 = W + BitVec.ofNat 64 4000 ∧
        d6 t.mem (W + BitVec.ofNat 64 3904) = d6 s.mem (W + BitVec.ofNat 64 a) ∧
        d6 t.mem (W + BitVec.ofNat 64 3952) = d6 s.mem (W + BitVec.ofNat 64 bb) ∧
        Frame [⟨W + BitVec.ofNat 64 3904, 48⟩, ⟨W + BitVec.ofNat 64 3952, 48⟩] s.mem t.mem ∧
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
  rw [show 2048 + SA = 3904 from rfl] at f2' v2
  rw [show 2048 + SB = 3952 from rfl] at f3 v3
  refine ⟨hw.of_rest r6 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, r6⟩
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r3.gpr _ (by decide),
      r2.gpr _ (by decide), u1.gpr, h2]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, a3 s3 hw3, off_add]; rfl
  · rw [u6.other _ (by decide), u5.gpr, u4.other _ (by decide), a3 s3 hw3, off_add]; rfl
  · rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), a3 s3 hw3, off_add]; rfl
  · rw [m6, d6_frame f3 (by omega) (by omega) (by omega), v2, u1.mem]
  · rw [m6, v3, d6_frame f2' (by omega) (by omega) (by omega), u1.mem]
  · rw [m6, ← u1.mem]
    exact (f2'.mono (by simp)).trans (f3.mono (by simp))

/-- The slow branch's copy out: `[o]` from `SO`. -/
theorem slowOut_ok {W : Addr} {s : State} (hw : WsAt W s) {o : Nat}
    (h1 : s.gpr .t1 = W + BitVec.ofNat 64 o) (ho : o + 48 ≤ 3712) :
    WP isa (.block (pack .t1 SO 0)) s fun t =>
      Rest [.a4, .a5] s t ∧ Frame [⟨W + BitVec.ofNat 64 o, 48⟩] s.mem t.mem ∧
      d6 t.mem (W + BitVec.ofNat 64 o) = d6 s.mem (W + BitVec.ofNat 64 4000) := by
  refine WP.mono (pack12_ok hw.ctx (p := .t1) (by decide) h1 (a := SO) (dst := 0) (by decide) (by decide)
    (by decide) (fun k hk => by
      rw [Nat.zero_add, off_add]
      exact in_base (n := 4) hw.wr (by omega) (by omega))
    (by
      rw [off_add, Nat.add_zero, off_add]
      exact Offset.disjoint W (d := o) (n := 48) (e := 2048 + SO) (k := 48) (by unfold SO; omega) (by omega)
        (by unfold SO; omega)))
    fun t ht => ⟨ht.rest, ?_, ?_⟩
  · have f := ht.frame
    rw [off_add, Nat.add_zero] at f
    exact f
  · rw [show (4000 : Nat) = 2048 + SO from rfl, ← off_add]
    exact d6_congr_wd fun j hj => by
      have := ht.outs j hj
      rw [Nat.zero_add] at this
      rw [this, limb, wd_off]

end VG.Proof.Weierstrass.RISCV64.P384Field

namespace VG.Proof.Weierstrass.RISCV64.P384Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P384Field
open VG.Proof.X25519.RISCV64 (Ctx Rest)
open VG.Proof.Weierstrass.RISCV64.P256Field (ptr_mod8 aligned_of ptrs_ok zext_ok)

/-- An offset argument: the low word of its register. -/
abbrev lo (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- What an operation on the pointers `t4`, `t5` and `t2` does, for operands
satisfying `pre`: its result `res` of the operands, written at `[t2]`. -/
def CoreOk (core : Prog isa) (pre : Nat → Nat → Prop) (res : Nat → Nat → Nat → Prop) : Prop :=
  ∀ {W : Addr} {s : State} {a bb o : Nat}, WsAt W s → s.gpr .t4 = W + BitVec.ofNat 64 a →
    s.gpr .t5 = W + BitVec.ofNat 64 bb → s.gpr .t2 = W + BitVec.ofNat 64 o → a % 8 = 0 → bb % 8 = 0 →
    o % 8 = 0 → a + 48 ≤ 8192 → bb + 48 ≤ 8192 → o + 48 ≤ 8192 → Apart bb →
    pre (d6 s.mem (W + BitVec.ofNat 64 a)) (d6 s.mem (W + BitVec.ofNat 64 bb)) →
    WP isa core s fun s' =>
      res (d6 s.mem (W + BitVec.ofNat 64 a)) (d6 s.mem (W + BitVec.ofNat 64 bb)) (d6 s'.mem (W + BitVec.ofNat 64 o)) ∧
      Frame (mulW W o) s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

/-- Montgomery's product modulo `p`. -/
abbrev mulRes (A B r : Nat) : Prop := r < P ∧ r * 2 ^ 384 % P = A * B % P

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

/-- The registers the functions write. -/
abbrev clobF : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-- The regions the functions write: their own working space and the result. -/
abbrev fnW (W : Addr) (o : Nat) : List Region := [⟨W + BitVec.ofNat 64 3712, 384⟩, ⟨W + BitVec.ofNat 64 o, 48⟩]

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
    (ho : lo s .a1 + 48 ≤ 3712) (ha : lo s .a2 + 48 ≤ 3712) (hb : lo s .a3 + 48 ≤ 3712)
    (hpre : pre (d6 s.mem (W + BitVec.ofNat 64 (lo s .a2))) (d6 s.mem (W + BitVec.ofNat 64 (lo s .a3)))) :
    WP isa (fn core) s fun s' =>
      res (d6 s.mem (W + BitVec.ofNat 64 (lo s .a2))) (d6 s.mem (W + BitVec.ofNat 64 (lo s .a3)))
        (d6 s'.mem (W + BitVec.ofNat 64 (lo s .a1))) ∧
      Frame (fnW W (lo s .a1)) s.mem s'.mem ∧ (∀ r, r ∉ clobF → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold fn
  refine WP.seq (WP.mono (zext_ok s) fun s0 ⟨z0, r0, m0⟩ => ?_)
  refine WP.seq (WP.mono (ptrs_ok z0 h0) fun s1 ⟨p2, p4, p5, p3, p0, r1', m1'⟩ => ?_)
  have hlo : ∀ r, VG.Proof.Weierstrass.RISCV64.P256Field.lo s r = lo s r := fun _ => rfl
  rw [hlo] at p2 p4 p5 p0
  rw [hlo, hlo] at p0
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

end VG.Proof.Weierstrass.RISCV64.P384Field
