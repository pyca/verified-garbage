module

public import VerifiedGarbage.Proof.Divstep.BatchBasic
public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Math
import VerifiedGarbage.Proof.X25519.AArch64.Ops
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Exec
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Impl.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Ed25519.Word64
public import VerifiedGarbage.Proof.Weierstrass.MontContract
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
public import VerifiedGarbage.Proof.Mont.AArch64.Words

/-! ### `Ed25519.AArch64.Inv.Row`, which only this module used -/

section

/-! ### `Ed25519.AArch64.Inv.Half`, which only this module used -/

section

/-! # The inversion's rows: one product accumulated

`half a m wi wo ci co` adds `a m` (`mul`, `umulh`) to the two words
`wi + 2⁶⁴ ci` into `wo + 2⁶⁴ co`, dropping a carry out of `co`. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG VG.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.X25519.AArch64.Alt (exec_mul_x exec_umulh_x exec_adds_x exec_adc_x)
open VG.Impl.Ed25519.AArch64.Divstep (half)

/-- The arithmetic of `half`. -/
theorem half_arith {W C L H M wo co c e : Nat} (hm : L + 2 ^ 64 * H = M)
    (h1 : wo + 2 ^ 64 * c = W + L) (h2 : co + 2 ^ 64 * e = C + H + c) :
    wo + 2 ^ 64 * co + 2 ^ 128 * e = W + 2 ^ 64 * C + M := by
  omega_using [hm, h1, h2]

theorem half_ok (s : State) {a m wi wo ci co : Reg}
    (ha9 : a ≠ .x9) (hm9 : m ≠ .x9) (hw9 : wi ≠ .x9) (hw10 : wi ≠ .x10)
    (hc9 : ci ≠ .x9) (hc10 : ci ≠ .x10) (hco : ci ≠ wo) (hwo10 : wo ≠ .x10) (hwc : wo ≠ co) :
    WP isa (.block (half a m wi wo ci co)) s fun t =>
      (∃ e ≤ 1, (t.gpr wo).toNat + 2 ^ 64 * (t.gpr co).toNat + 2 ^ 128 * e =
        (s.gpr wi).toNat + 2 ^ 64 * (s.gpr ci).toNat + (s.gpr a).toNat * (s.gpr m).toNat) ∧
      Keeps [.x9, .x10, wo, co] s t := by
  apply WP.of_runBlock
  simp only [half, runBlock_cons, runStep_some, runBlock_nil, exec_mul_x, exec_umulh_x,
    exec_adds_x, exec_adc_x, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
      RegUpd.gpr_write, ha9, hm9, hw9, hw10, hc9, hc10, hco, hwo10, hwc,
      Ne.symm hwo10, Ne.symm hwc, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
    obtain hm := mul_lo_hi (s.gpr a) (s.gpr m)
    obtain h1 := addCarry_value (s.gpr wi) (s.gpr a * s.gpr m) false
    refine ⟨(carryOut (s.gpr ci) (mulHi (s.gpr a) (s.gpr m))
        (carryOut (s.gpr wi) (s.gpr a * s.gpr m) false)).toNat, Bool.toNat_le _, ?_⟩
    obtain h3 := addCarry_value (s.gpr ci) (mulHi (s.gpr a) (s.gpr m))
      (carryOut (s.gpr wi) (s.gpr a * s.gpr m) false)
    simp only [addCarry, carryOut, mulHi, Bool.toNat_false, Nat.add_zero, BitVec.add_zero] at h1 h3 hm ⊢
    exact half_arith hm h1 h3
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
      ite_false]

end VG.Proof.Ed25519.AArch64.Inv

end

end


/-! # The inversion's rows

A row of a batch (`Divstep.row`) leaves five words `W` at `t` with
`W + 2²⁵⁶ (ka + kb) ≡ c + X' a + Y' b` (mod `2³²⁰`) (`row_ok`): `a`, `b` the
magnitudes in `ma`, `mb`, `X'`, `Y'` the four words at `xo`, `yo`
complemented by the masks `sa`, `sb`, `c` the carry in `car`, and `ka`, `kb`
the corrections of the tops (`corrV`). Exactly, given magnitudes of at most
`2⁶²`: the words below the top carry nothing out. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG VG.AArch64 VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64 (KeepRegs)
open VG.Proof.X25519.AArch64 (exec_eor_x exec_and_x exec_sub_x exec_add_x exec_lsr)
open VG.Impl.Ed25519.AArch64 (ld st)
open VG.Impl.Ed25519.AArch64.Divstep (ldx corr digit top row half)

variable {large : Bool}

/-- The correction of a row's top for a word `x` (complemented) and magnitude
`m`: `m` if `x`'s sign is set (`signed`), or if the mask `r` is (else). -/
def corrV (signed : Bool) (x m r : Word) : Word := if signed then ((0 : Word) - (x >>> 63)) &&& m else r &&& m

theorem ldx_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat} (ho : o % 8 = 0)
    (ho' : o + 8 ≤ workSize large) {r : Reg} (hr : r ≠ .x8) :
    WP isa (.block (ldx o r)) s fun t =>
      t.gpr .x8 = word s.mem base o ^^^ s.gpr r ∧ Keeps [.x8] s t := by
  apply WP.of_runBlock
  simp only [ldx, runBlock_cons, runStep_some, runBlock_nil, load_sc hs ho ho', exec_eor_x,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_write, hr, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [List.mem_singleton] at hr'
    simp only [RegUpd.gpr_write, hr', ite_false]

theorem corr_ok (s : State) (signed : Bool) {d m r : Reg} (hz : s.gpr .x12 = 0)
    (hd12 : d ≠ .x12) (hmd : m ≠ d) :
    WP isa (.block (corr signed d m r)) s fun t =>
      t.gpr d = 0 - corrV signed (s.gpr .x8) (s.gpr m) (s.gpr r) ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  cases signed
  · simp only [corr, Bool.false_eq_true, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil,
      exec_and_x, exec_sub_x, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩⟩
    · simp only [RegUpd.gpr_write, Ne.symm hd12, hz, corrV, ite_true,
        ite_false, Bool.false_eq_true, BitVec.setWidth_eq]
    · simp only [List.mem_singleton] at hr'
      simp only [RegUpd.gpr_write, hr', ite_false]
  · simp only [corr, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil,
      exec_and_x, exec_sub_x, exec_lsr (by decide : 63 < 64), Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩⟩
    · simp only [RegUpd.gpr_write, Ne.symm hd12, hmd, hz, corrV, ite_true,
        ite_false, BitVec.setWidth_eq]
    · simp only [List.mem_singleton] at hr'
      simp only [RegUpd.gpr_write, hr', ite_false]

theorem st_ok {s : State} {base : Addr} (hs : Scr s base large) {d : Nat} (ha : d % 8 = 0)
    (hd : d + 8 ≤ workSize large) (r : Reg) :
    WP isa (.block [st r d]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ KeepRegs [] s t :=
  WP.block_cons_iff.mpr ⟨_, store_sc hs ha hd r, WP.block_nil ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl⟩⟩

/-- The registers of a row: none is a temporary, `x0` or `x12`. -/
def RowRegs (ma sa mb sb : Reg) : Prop :=
  ∀ r ∈ [ma, sa, mb, sb], r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧
    r ≠ .x10 ∧ r ≠ .x12

instance (ma sa mb sb : Reg) : Decidable (RowRegs ma sa mb sb) := by
  unfold RowRegs; exact inferInstance

theorem digit_arith {W PX PY w1 c1 e1 w c e : Nat} (hW : W < 2 ^ 64)
    (hPX : PX ≤ (2 ^ 64 - 1) * 2 ^ 62) (hPY : PY ≤ (2 ^ 64 - 1) * 2 ^ 62)
    (h1 : w1 + 2 ^ 64 * c1 + 2 ^ 128 * e1 = W + 2 ^ 64 * 0 + PX)
    (h2 : w + 2 ^ 64 * c + 2 ^ 128 * e = w1 + 2 ^ 64 * c1 + PY) :
    w + 2 ^ 64 * c = W + PX + PY := by
  omega_arith

theorem prod_le {x : Word} {a : Nat} (h : a ≤ 2 ^ 62) : x.toNat * a ≤ (2 ^ 64 - 1) * 2 ^ 62 :=
  Nat.mul_le_mul (by have := x.isLt; omega_arith) h

/-- A word below a row's top. -/
theorem digit_ok {s : State} {base : Addr} (hs : Scr s base large) {t xo yo : Nat}
    {ma sa mb sb wi : Reg} (hr : RowRegs ma sa mb sb)
    (hwi : wi ≠ .x1 ∧ wi ≠ .x8 ∧ wi ≠ .x9 ∧ wi ≠ .x10 ∧ wi ≠ .x12)
    (hz : s.gpr .x12 = 0) (hA : (s.gpr ma).toNat ≤ 2 ^ 62) (hB : (s.gpr mb).toNat ≤ 2 ^ 62)
    (ht : t % 8 = 0 ∧ t + 8 ≤ workSize large) (hx : xo % 8 = 0 ∧ xo + 8 ≤ workSize large)
    (hy : yo % 8 = 0 ∧ yo + 8 ≤ workSize large) :
    WP isa (.block (digit t xo yo ma sa mb sb wi)) s fun u =>
      (u.gpr .x1).toNat + 2 ^ 64 * (u.gpr .x2).toNat =
        (s.gpr wi).toNat + (word s.mem base xo ^^^ s.gpr sa).toNat * (s.gpr ma).toNat +
          (word s.mem base yo ^^^ s.gpr sb).toNat * (s.gpr mb).toNat ∧
      u.mem = s.mem.writeW (off base t) (u.gpr .x1) ∧
      KeepRegs [.x1, .x2, .x8, .x9, .x10] s u := by
  obtain ⟨⟨ma0, ma1, ma2, -, ma8, ma9, ma10, ma12⟩, ⟨sa0, sa1, sa2, -, sa8, sa9, sa10, sa12⟩,
    ⟨mb0, mb1, mb2, -, mb8, mb9, mb10, mb12⟩, ⟨sb0, sb1, sb2, -, sb8, sb9, sb10, sb12⟩⟩ :=
    (by simpa only [RowRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using hr :
      (ma ≠ .x0 ∧ ma ≠ .x1 ∧ ma ≠ .x2 ∧ ma ≠ .x3 ∧ ma ≠ .x8 ∧ ma ≠ .x9 ∧ ma ≠ .x10 ∧ ma ≠ .x12) ∧
      (sa ≠ .x0 ∧ sa ≠ .x1 ∧ sa ≠ .x2 ∧ sa ≠ .x3 ∧ sa ≠ .x8 ∧ sa ≠ .x9 ∧ sa ≠ .x10 ∧ sa ≠ .x12) ∧
      (mb ≠ .x0 ∧ mb ≠ .x1 ∧ mb ≠ .x2 ∧ mb ≠ .x3 ∧ mb ≠ .x8 ∧ mb ≠ .x9 ∧ mb ≠ .x10 ∧ mb ≠ .x12) ∧
      (sb ≠ .x0 ∧ sb ≠ .x1 ∧ sb ≠ .x2 ∧ sb ≠ .x3 ∧ sb ≠ .x8 ∧ sb ≠ .x9 ∧ sb ≠ .x10 ∧ sb ≠ .x12))
  obtain ⟨w1, w8, w9, w10, w12⟩ := hwi
  simp only [digit, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldx_ok hs hx.1 hx.2 sa8) fun a ⟨a8, ka⟩ => ?_
  obtain hsa : Scr a base large := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (half_ok a (by decide) ma9 w9 w10 (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun b ⟨⟨e1, _, h1⟩, kb⟩ => ?_
  obtain hsb : Scr b base large := hsa.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ldx_ok hsb hy.1 hy.2 sb8) fun c ⟨c8, kc⟩ => ?_
  obtain hsc : Scr c base large := hsb.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (half_ok c (by decide) mb9 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun d ⟨⟨e2, _, h2⟩, kd⟩ => ?_
  obtain hsd : Scr d base large := hsc.of_keeps kd (by decide)
  refine WP.mono (st_ok hsd ht.1 ht.2 .x1) fun u ⟨mu, ku⟩ => ?_
  -- the registers each step read
  obtain ga : ∀ r, r ≠ .x8 → a.gpr r = s.gpr r := fun r h => ka.gpr r (by simpa using h)
  obtain gb : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x1 → r ≠ .x2 → b.gpr r = a.gpr r := fun r h9 h10 h1 h2 =>
    kb.gpr r (by simp [h9, h10, h1, h2])
  obtain gc : ∀ r, r ≠ .x8 → c.gpr r = b.gpr r := fun r h => kc.gpr r (by simpa using h)
  obtain gd : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x1 → r ≠ .x2 → d.gpr r = c.gpr r := fun r h9 h10 h1 h2 =>
    kd.gpr r (by simp [h9, h10, h1, h2])
  obtain gu : ∀ r, u.gpr r = d.gpr r := fun r => ku.gpr r (by simp)
  have amem : a.mem = s.mem := ka.mem
  have bmem : b.mem = a.mem := kb.mem
  refine ⟨?_, ?_, ⟨fun r hr => ?_, by rw [ku.rd, kd.rd, kc.rd, kb.rd, ka.rd],
    by rw [ku.wr, kd.wr, kc.wr, kb.wr, ka.wr], by rw [ku.sp, kd.sp, kc.sp, kb.sp, ka.sp]⟩⟩
  · rw [gu, gu]
    rw [a8, ga ma ma8, ga wi w8, ga .x12 (by decide), hz] at h1
    rw [c8, gc mb mb8, gc .x1 (by decide), gc .x2 (by decide),
      gb mb mb9 mb10 mb1 mb2, gb sb sb9 sb10 sb1 sb2, ga mb mb8, ga sb sb8, bmem, amem] at h2
    rw [show (0 : Word).toNat = 0 from rfl] at h1
    exact digit_arith (s.gpr wi).isLt (prod_le hA) (prod_le hB) h1 h2
  · rw [mu, kd.mem, kc.mem, bmem, amem, gu]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gu, gd r hr.2.2.2.1 hr.2.2.2.2 hr.1 hr.2.1, gc r hr.2.2.1, gb r hr.2.2.2.1 hr.2.2.2.2 hr.1 hr.2.1,
      ga r hr.2.2.1]

theorem add_ok (s : State) (d n m : Reg) :
    WP isa (.block [.add .x d n m]) s fun t => t.gpr d = s.gpr n + s.gpr m ∧ Keeps [d] s t := by
  refine WP.block_cons_iff.mpr ⟨_, exec_add_x, WP.block_nil ?_⟩
  exact ⟨RegUpd.gpr_write_self _ _ _ _, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _
    (by simpa only [List.mem_singleton] using hr), rfl, rfl, rfl, rfl⟩⟩

theorem neg_toNat (v : Word) : ((0 : Word) - v).toNat = (2 ^ 64 - v.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_sub, show (0 : Word).toNat = 0 from rfl, Nat.add_zero]

theorem top_arith {W PX PY KA KB w1 h e w w4 e' : Nat} (hKA : KA < 2 ^ 64) (hKB : KB < 2 ^ 64)
    (h1 : w1 + 2 ^ 64 * h + 2 ^ 128 * e = W + 2 ^ 64 * ((2 ^ 64 - KA) % 2 ^ 64) + PX)
    (h2 : w + 2 ^ 64 * w4 + 2 ^ 128 * e' =
      w1 + 2 ^ 64 * ((h + (2 ^ 64 - KB) % 2 ^ 64) % 2 ^ 64) + PY) :
    (w + 2 ^ 64 * w4 + 2 ^ 64 * (KA + KB)) % 2 ^ 128 = (W + PX + PY) % 2 ^ 128 := by
  omega_arith

/-- The top two words of a row: `w + 2⁶⁴ w' + 2⁶⁴ (ka + kb) ≡ x2 + X' a + Y' b` (mod `2¹²⁸`). -/
theorem top_ok {s : State} {base : Addr} (hs : Scr s base large) (signed : Bool) {t xo yo : Nat}
    {ma sa mb sb : Reg} (hr : RowRegs ma sa mb sb) (hz : s.gpr .x12 = 0)
    (ht : t % 8 = 0 ∧ t + 16 ≤ workSize large) (hx : xo % 8 = 0 ∧ xo + 8 ≤ workSize large)
    (hy : yo % 8 = 0 ∧ yo + 8 ≤ workSize large) :
    WP isa (.block (top signed t xo yo ma sa mb sb)) s fun u =>
      ((u.gpr .x1).toNat + 2 ^ 64 * (u.gpr .x3).toNat +
          2 ^ 64 * ((corrV signed (word s.mem base xo ^^^ s.gpr sa) (s.gpr ma) (s.gpr sa)).toNat +
            (corrV signed (word s.mem base yo ^^^ s.gpr sb) (s.gpr mb) (s.gpr sb)).toNat)) % 2 ^ 128 =
        ((s.gpr .x2).toNat + (word s.mem base xo ^^^ s.gpr sa).toNat * (s.gpr ma).toNat +
          (word s.mem base yo ^^^ s.gpr sb).toNat * (s.gpr mb).toNat) % 2 ^ 128 ∧
      u.mem = (s.mem.writeW (off base t) (u.gpr .x1)).writeW (off base (t + 8)) (u.gpr .x3) ∧
      KeepRegs [.x1, .x2, .x3, .x8, .x9, .x10] s u := by
  obtain ⟨⟨_, ma1, ma2, ma3, ma8, ma9, ma10, ma12⟩, ⟨_, sa1, sa2, sa3, sa8, sa9, sa10, sa12⟩,
    ⟨_, mb1, mb2, mb3, mb8, mb9, mb10, mb12⟩, ⟨_, sb1, sb2, sb3, sb8, sb9, sb10, sb12⟩⟩ :=
    (by simpa only [RowRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using hr :
      (ma ≠ .x0 ∧ ma ≠ .x1 ∧ ma ≠ .x2 ∧ ma ≠ .x3 ∧ ma ≠ .x8 ∧ ma ≠ .x9 ∧ ma ≠ .x10 ∧ ma ≠ .x12) ∧
      (sa ≠ .x0 ∧ sa ≠ .x1 ∧ sa ≠ .x2 ∧ sa ≠ .x3 ∧ sa ≠ .x8 ∧ sa ≠ .x9 ∧ sa ≠ .x10 ∧ sa ≠ .x12) ∧
      (mb ≠ .x0 ∧ mb ≠ .x1 ∧ mb ≠ .x2 ∧ mb ≠ .x3 ∧ mb ≠ .x8 ∧ mb ≠ .x9 ∧ mb ≠ .x10 ∧ mb ≠ .x12) ∧
      (sb ≠ .x0 ∧ sb ≠ .x1 ∧ sb ≠ .x2 ∧ sb ≠ .x3 ∧ sb ≠ .x8 ∧ sb ≠ .x9 ∧ sb ≠ .x10 ∧ sb ≠ .x12))
  simp only [top, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldx_ok hs hx.1 hx.2 sa8) fun a ⟨a8, ka⟩ => ?_
  obtain ga : ∀ r, r ≠ .x8 → a.gpr r = s.gpr r := fun r h => ka.gpr r (by simpa using h)
  obtain hsa : Scr a base large := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (corr_ok a signed ((ga _ (by decide)).trans hz) (by decide) ma3)
    fun b ⟨b3, kb⟩ => ?_
  obtain gb : ∀ r, r ≠ .x3 → b.gpr r = a.gpr r := fun r h => kb.gpr r (by simpa using h)
  obtain hsb : Scr b base large := hsa.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (half_ok b (by decide) ma9 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun c ⟨⟨e1, _, h1⟩, kc⟩ => ?_
  obtain gc : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x1 → r ≠ .x3 → c.gpr r = b.gpr r := fun r h9 h10 h1 h3 =>
    kc.gpr r (by simp [h9, h10, h1, h3])
  obtain hsc : Scr c base large := hsb.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ldx_ok hsc hy.1 hy.2 sb8) fun d ⟨d8, kd⟩ => ?_
  obtain gd : ∀ r, r ≠ .x8 → d.gpr r = c.gpr r := fun r h => kd.gpr r (by simpa using h)
  obtain hsd : Scr d base large := hsc.of_keeps kd (by decide)
  rw [WP.block_append_iff]
  obtain dz : d.gpr .x12 = 0 := by
    rw [gd _ (by decide), gc _ (by decide) (by decide) (by decide) (by decide), gb _ (by decide),
      ga _ (by decide), hz]
  refine WP.mono (corr_ok d signed dz (by decide) mb2) fun e ⟨e2, ke⟩ => ?_
  obtain ge : ∀ r, r ≠ .x2 → e.gpr r = d.gpr r := fun r h => ke.gpr r (by simpa using h)
  obtain hse : Scr e base large := hsd.of_keeps ke (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (add_ok e .x3 .x3 .x2) fun f ⟨f3, kf⟩ => ?_
  obtain gf : ∀ r, r ≠ .x3 → f.gpr r = e.gpr r := fun r h => kf.gpr r (by simpa using h)
  obtain hsf : Scr f base large := hse.of_keeps kf (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (half_ok f (by decide) mb9 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun g ⟨⟨e2', _, h2⟩, kg⟩ => ?_
  obtain gg : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x1 → r ≠ .x3 → g.gpr r = f.gpr r := fun r h9 h10 h1 h3 =>
    kg.gpr r (by simp [h9, h10, h1, h3])
  obtain hsg : Scr g base large := hsf.of_keeps kg (by decide)
  rw [WP.block_cons_iff]
  refine ⟨_, store_sc hsg ht.1 (by omega_arith) .x1, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, store_sc (hsg.setMem _) (by omega_arith) (by omega_arith) .x3, WP.block_nil ?_⟩
  -- memory: the loads read `s.mem`
  obtain mc : c.mem = s.mem := by rw [kc.mem, kb.mem, ka.mem]
  obtain mf : f.mem = s.mem := by rw [kf.mem, ke.mem, kd.mem, mc]
  refine ⟨?_, ?_, ⟨fun r hr => ?_, by simp only [kg.rd, kf.rd, ke.rd, kd.rd, kc.rd, kb.rd, ka.rd],
    by simp only [kg.wr, kf.wr, ke.wr, kd.wr, kc.wr, kb.wr, ka.wr],
    by simp only [kg.sp, kf.sp, ke.sp, kd.sp, kc.sp, kb.sp, ka.sp]⟩⟩
  · simp only
    rw [b3, gb .x2 (by decide), gb .x8 (by decide), gb ma ma3] at h1
    rw [a8, ga .x2 (by decide), ga ma ma8, ga sa sa8, neg_toNat] at h1
    obtain hx3 : f.gpr .x3 = c.gpr .x3 +
        (0 - corrV signed (word s.mem base yo ^^^ s.gpr sb) (s.gpr mb) (s.gpr sb)) := by
      rw [f3, ge .x3 (by decide), gd .x3 (by decide), e2, d8, gd mb mb8, gd sb sb8,
        gc mb mb9 mb10 mb1 mb3, gc sb sb9 sb10 sb1 sb3, gb mb mb3, gb sb sb3, ga mb mb8,
        ga sb sb8, mc]
    obtain hx1 : f.gpr .x1 = c.gpr .x1 := by
      rw [gf .x1 (by decide), ge .x1 (by decide), gd .x1 (by decide)]
    obtain hx8 : f.gpr .x8 = word s.mem base yo ^^^ s.gpr sb := by
      rw [gf .x8 (by decide), ge .x8 (by decide), d8, gc sb sb9 sb10 sb1 sb3, gb sb sb3,
        ga sb sb8, mc]
    obtain hmb : f.gpr mb = s.gpr mb := by
      rw [gf mb mb3, ge mb mb2, gd mb mb8, gc mb mb9 mb10 mb1 mb3, gb mb mb3, ga mb mb8]
    rw [hx3, hx1, hx8, hmb, BitVec.toNat_add, neg_toNat] at h2
    exact top_arith (corrV signed _ _ _).isLt (corrV signed _ _ _).isLt h1 h2
  · simp only [mf, kg.mem]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only
    rw [gg r hr.2.2.2.2.1 hr.2.2.2.2.2 hr.1 hr.2.2.1, gf r hr.2.2.1, ge r hr.2.1, gd r hr.2.2.2.1,
      gc r hr.2.2.2.2.1 hr.2.2.2.2.2 hr.1 hr.2.2.1, gb r hr.2.2.1, ga r hr.2.2.2.1]

/-- Five words at `t`. -/
abbrev val5 (m : Mem) (base : Addr) (t : Nat) : Nat :=
  fe m base t + 2 ^ 256 * (word m base (t + 32)).toNat

/-- The four words at `o`, complemented by the mask `s`. -/
abbrev flip4 (m : Mem) (base : Addr) (o : Nat) (s : Word) : Nat :=
  val4 (word m base o ^^^ s) (word m base (o + 8) ^^^ s) (word m base (o + 16) ^^^ s)
    (word m base (o + 24) ^^^ s)

theorem row_arith {C P0 P1 P2 P3 Q0 Q1 Q2 Q3 w0 w1 w2 w3 w4 c1 c2 c3 K : Nat}
    (d0 : w0 + 2 ^ 64 * c1 = C + P0 + Q0) (d1 : w1 + 2 ^ 64 * c2 = c1 + P1 + Q1)
    (d2 : w2 + 2 ^ 64 * c3 = c2 + P2 + Q2)
    (d3 : (w3 + 2 ^ 64 * w4 + 2 ^ 64 * K) % 2 ^ 128 = (c3 + P3 + Q3) % 2 ^ 128) :
    (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3 + 2 ^ 256 * w4 + 2 ^ 256 * K) % (2 ^ 256 * 2 ^ 64) =
      (C + (P0 + 2 ^ 64 * P1 + 2 ^ 128 * P2 + 2 ^ 192 * P3) +
        (Q0 + 2 ^ 64 * Q1 + 2 ^ 128 * Q2 + 2 ^ 192 * Q3)) % (2 ^ 256 * 2 ^ 64) := by
  omega_arith

theorem val4_mul (x0 x1 x2 x3 : Word) (a : Nat) :
    val4 x0 x1 x2 x3 * a = x0.toNat * a + 2 ^ 64 * (x1.toNat * a) + 2 ^ 128 * (x2.toNat * a) +
      2 ^ 192 * (x3.toNat * a) := by
  simp only [val4, Nat.add_mul, Nat.mul_assoc]

/-- A row: `W + 2²⁵⁶ (ka + kb) ≡ c + X' a + Y' b` (mod `2³²⁰`). -/
theorem row_ok {s : State} {base : Addr} (hs : Scr s base large) (signed : Bool) {t xo yo : Nat}
    {ma sa mb sb car : Reg} (hr : RowRegs ma sa mb sb)
    (hcar : car ≠ .x1 ∧ car ≠ .x8 ∧ car ≠ .x9 ∧ car ≠ .x10 ∧ car ≠ .x12)
    (hz : s.gpr .x12 = 0) (hA : (s.gpr ma).toNat ≤ 2 ^ 62) (hB : (s.gpr mb).toNat ≤ 2 ^ 62)
    (ht : t % 8 = 0 ∧ t + 40 ≤ workSize large) (hx : xo % 8 = 0 ∧ xo + 32 ≤ workSize large)
    (hy : yo % 8 = 0 ∧ yo + 32 ≤ workSize large) (hsx : t + 40 ≤ xo ∨ xo + 32 ≤ t)
    (hsy : t + 40 ≤ yo ∨ yo + 32 ≤ t) :
    WP isa (.block (row signed t xo yo ma sa mb sb car)) s fun u =>
      (val5 u.mem base t + 2 ^ 256 *
          ((corrV signed (word s.mem base (xo + 24) ^^^ s.gpr sa) (s.gpr ma) (s.gpr sa)).toNat +
            (corrV signed (word s.mem base (yo + 24) ^^^ s.gpr sb) (s.gpr mb) (s.gpr sb)).toNat)) %
          (2 ^ 256 * 2 ^ 64) =
        ((s.gpr car).toNat + flip4 s.mem base xo (s.gpr sa) * (s.gpr ma).toNat +
          flip4 s.mem base yo (s.gpr sb) * (s.gpr mb).toNat) % (2 ^ 256 * 2 ^ 64) ∧
      Outside base t 40 s.mem u.mem ∧ KeepRegs [.x1, .x2, .x3, .x8, .x9, .x10] s u := by
  obtain _hcap := workSize_le large
  have hrr := hr
  obtain ⟨⟨_, ma1, ma2, ma3, ma8, ma9, ma10, ma12⟩, ⟨_, sa1, sa2, sa3, sa8, sa9, sa10, sa12⟩,
    ⟨_, mb1, mb2, mb3, mb8, mb9, mb10, mb12⟩, ⟨_, sb1, sb2, sb3, sb8, sb9, sb10, sb12⟩⟩ :=
    (by simpa only [RowRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using hr :
      (ma ≠ .x0 ∧ ma ≠ .x1 ∧ ma ≠ .x2 ∧ ma ≠ .x3 ∧ ma ≠ .x8 ∧ ma ≠ .x9 ∧ ma ≠ .x10 ∧ ma ≠ .x12) ∧
      (sa ≠ .x0 ∧ sa ≠ .x1 ∧ sa ≠ .x2 ∧ sa ≠ .x3 ∧ sa ≠ .x8 ∧ sa ≠ .x9 ∧ sa ≠ .x10 ∧ sa ≠ .x12) ∧
      (mb ≠ .x0 ∧ mb ≠ .x1 ∧ mb ≠ .x2 ∧ mb ≠ .x3 ∧ mb ≠ .x8 ∧ mb ≠ .x9 ∧ mb ≠ .x10 ∧ mb ≠ .x12) ∧
      (sb ≠ .x0 ∧ sb ≠ .x1 ∧ sb ≠ .x2 ∧ sb ≠ .x3 ∧ sb ≠ .x8 ∧ sb ≠ .x9 ∧ sb ≠ .x10 ∧ sb ≠ .x12))
  obtain k5 : ∀ r ∈ ([.x1, .x2, .x8, .x9, .x10] : List Reg), r ∈ ([.x1, .x2, .x3, .x8, .x9, .x10] : List Reg) := by
    decide
  -- a register the row keeps
  obtain keep : ∀ {r : Reg}, r ∈ [ma, sa, mb, sb] → r ∉ ([.x1, .x2, .x3, .x8, .x9, .x10] : List Reg) := by
    intro r h
    have := hrr r h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2.1⟩
  obtain sep : ∀ {d e : Nat}, d + 8 ≤ e ∨ e + 8 ≤ d → d + 8 ≤ workSize large → e + 8 ≤ workSize large →
      ∀ (m : Mem) (v : Word), word (m.writeW (off base d) v) base e = word m base e :=
    fun h hd he m v => word_writeW_sep m base v h.symm (by omega_arith) (by omega_arith)
  simp only [row, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok hs hr hcar hz hA hB ⟨ht.1, by omega_arith⟩ ⟨hx.1, by omega_arith⟩ ⟨hy.1, by omega_arith⟩)
    fun u0 ⟨e0, m0, k0⟩ => ?_
  obtain hs0 : Scr u0 base large := ⟨(k0.gpr _ (by decide)).trans hs.x0, k0.wr ▸ hs.wr, hs.nowrap⟩
  obtain g0 : ∀ {r : Reg}, r ∈ [ma, sa, mb, sb] → u0.gpr r = s.gpr r := fun h =>
    k0.gpr _ fun hm => keep h (k5 _ hm)
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok hs0 hr (by decide) ((k0.gpr _ (by decide)).trans hz)
    (by rw [g0 (r := ma) (by simp)]; exact hA) (by rw [g0 (r := mb) (by simp)]; exact hB)
    ⟨by omega_arith, by omega_arith⟩ ⟨by omega_arith, by omega_arith⟩ ⟨by omega_arith, by omega_arith⟩)
    fun u1 ⟨e1, m1, k1⟩ => ?_
  obtain hs1 : Scr u1 base large := ⟨(k1.gpr _ (by decide)).trans hs0.x0, k1.wr ▸ hs0.wr, hs.nowrap⟩
  obtain g1 : ∀ {r : Reg}, r ∈ [ma, sa, mb, sb] → u1.gpr r = s.gpr r := fun h =>
    (k1.gpr _ fun hm => keep h (k5 _ hm)).trans (g0 h)
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok hs1 hr (by decide) ((k1.gpr _ (by decide)).trans ((k0.gpr _ (by decide)).trans hz))
    (by rw [g1 (r := ma) (by simp)]; exact hA) (by rw [g1 (r := mb) (by simp)]; exact hB)
    ⟨by omega_arith, by omega_arith⟩ ⟨by omega_arith, by omega_arith⟩ ⟨by omega_arith, by omega_arith⟩)
    fun u2 ⟨e2, m2, k2⟩ => ?_
  obtain hs2 : Scr u2 base large := ⟨(k2.gpr _ (by decide)).trans hs1.x0, k2.wr ▸ hs1.wr, hs.nowrap⟩
  obtain g2 : ∀ {r : Reg}, r ∈ [ma, sa, mb, sb] → u2.gpr r = s.gpr r := fun h =>
    (k2.gpr _ fun hm => keep h (k5 _ hm)).trans (g1 h)
  refine WP.mono (top_ok hs2 signed hr ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans
      ((k0.gpr _ (by decide)).trans hz))) ⟨by omega_arith, by omega_arith⟩ ⟨by omega_arith, by omega_arith⟩
      ⟨by omega_arith, by omega_arith⟩)
    fun u ⟨e3, m3, k3⟩ => ?_
  -- the words the later steps read are the first's
  obtain r1 : ∀ e, (t + 8 ≤ e ∨ e + 8 ≤ t) → e + 8 ≤ workSize large → word u0.mem base e = word s.mem base e :=
    fun e h he => by rw [m0]; exact sep h (by omega_arith) he _ _
  obtain r2 : ∀ e, (t + 16 ≤ e ∨ e + 8 ≤ t) → e + 8 ≤ workSize large → word u1.mem base e = word s.mem base e :=
    fun e h he => by rw [m1, sep (by omega_arith) (by omega_arith) he, r1 e (by omega_arith) he]
  obtain r3 : ∀ e, (t + 24 ≤ e ∨ e + 8 ≤ t) → e + 8 ≤ workSize large → word u2.mem base e = word s.mem base e :=
    fun e h he => by rw [m2, sep (by omega_arith) (by omega_arith) he, r2 e (by omega_arith) he]
  rw [g0 (r := sa) (by simp), g0 (r := ma) (by simp), g0 (r := sb) (by simp), g0 (r := mb) (by simp), r1 _ (by omega_arith) (by omega_arith),
    r1 _ (by omega_arith) (by omega_arith)] at e1
  rw [g1 (r := sa) (by simp), g1 (r := ma) (by simp), g1 (r := sb) (by simp), g1 (r := mb) (by simp), r2 _ (by omega_arith) (by omega_arith),
    r2 _ (by omega_arith) (by omega_arith)] at e2
  rw [g2 (r := sa) (by simp), g2 (r := ma) (by simp), g2 (r := sb) (by simp), g2 (r := mb) (by simp), r3 _ (by omega_arith) (by omega_arith),
    r3 _ (by omega_arith) (by omega_arith)] at e3
  -- the words of the result
  obtain w0 : word u.mem base t = u0.gpr .x1 := by
    rw [m3, sep (by omega_arith) (by omega_arith) (by omega_arith), sep (by omega_arith) (by omega_arith) (by omega_arith), m2,
      sep (by omega_arith) (by omega_arith) (by omega_arith), m1, sep (by omega_arith) (by omega_arith) (by omega_arith), m0,
      word_writeW_self]
  obtain w1 : word u.mem base (t + 8) = u1.gpr .x1 := by
    rw [m3, sep (by omega_arith) (by omega_arith) (by omega_arith), sep (by omega_arith) (by omega_arith) (by omega_arith), m2,
      sep (by omega_arith) (by omega_arith) (by omega_arith), m1, word_writeW_self]
  obtain w2 : word u.mem base (t + 16) = u2.gpr .x1 := by
    rw [m3, sep (by omega_arith) (by omega_arith) (by omega_arith), sep (by omega_arith) (by omega_arith) (by omega_arith), m2,
      word_writeW_self]
  obtain w3 : word u.mem base (t + 24) = u.gpr .x1 := by
    rw [m3, sep (by omega_arith) (by omega_arith) (by omega_arith), word_writeW_self]
  obtain w4 : word u.mem base (t + 32) = u.gpr .x3 := by
    rw [m3, show t + 32 = t + 24 + 8 by omega_arith, word_writeW_self]
  refine ⟨?_, ?_, ((k0.mono k5).trans (k1.mono k5)).trans ((k2.mono k5).trans k3)⟩
  · simp only [val5, fe, w0, w1, w2, w3, w4, flip4, val4_mul]
    exact row_arith e0 e1 e2 e3
  · have o0 : Outside base t 40 s.mem u0.mem := by
      rw [m0]; exact (writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)
    obtain o1 : Outside base t 40 u0.mem u1.mem := by
      rw [m1]; exact (writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)
    obtain o2 : Outside base t 40 u1.mem u2.mem := by
      rw [m2]; exact (writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)
    obtain o3 : Outside base t 40 u2.mem u.mem := by
      rw [m3]
      exact ((writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
        ((writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
    exact o0.trans (o1.trans (o2.trans o3))

end VG.Proof.Ed25519.AArch64.Inv

end

end

/-! ### `Ed25519.AArch64.Inv.Mat`, which only this module used -/

section

/-! # The inversion's matrix as magnitudes and signs

`mat` leaves each entry `m` of the matrix as `|m|` and the mask of its sign,
and the rows' carries `negN` (`mat_ok`). -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG VG.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.X25519.AArch64 (exec_lsr exec_sub_x exec_eor_x exec_and_x exec_add_x exec_movz)
open VG.Impl.Ed25519.AArch64.Divstep (signMag mat)

/-- The mask of a word's sign. -/
def maskN (m : Word) : Word := if m.msb then BitVec.allOnes 64 else 0

theorem mask_eq (m : Word) : (0 : Word) - (m >>> 63) = maskN m := by
  rw [sgn_word, maskN]
  congr 1
  rw [BitVec.msb_eq_decide]
  simp only [decide_eq_true_eq]

theorem absN_word (m : Word) : ((m ^^^ maskN m) - maskN m).toNat = absN m := by
  unfold maskN absN
  cases hm : m.msb
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have h1 : m.toInt = (m.toNat : Int) := by
      have := BitVec.toInt_eq_msb_cond m
      rw [hm] at this
      simpa using this
    have hl := m.isLt
    rw [BitVec.toNat_sub, BitVec.toNat_xor, show (0 : Word).toNat = 0 from rfl, Nat.xor_zero, h1,
      Int.natAbs_natCast]
    omega_using []
  · simp only [↓reduceIte]
    have h1 : m.toInt = (m.toNat : Int) - 2 ^ 64 := by
      have := BitVec.toInt_eq_msb_cond m
      rw [hm] at this
      simpa using this
    have h2 : 2 ^ 63 ≤ m.toNat := by
      rw [BitVec.msb_eq_decide] at hm
      simpa using hm
    have hl := m.isLt
    rw [BitVec.xor_allOnes, BitVec.toNat_sub, BitVec.toNat_not, BitVec.toNat_allOnes, h1,
      show ((m.toNat : Int) - 2 ^ 64) = -((2 ^ 64 - m.toNat : Nat) : Int) by omega_using [],
      Int.natAbs_neg, Int.natAbs_natCast]
    omega_using [h2]

/-- The magnitude of a word as the code computes it. -/
abbrev absW (m : Word) : Word := (m ^^^ maskN m) - maskN m

theorem negN_word (m : Word) : (absW m &&& maskN m).toNat = negN m := by
  have ha := absN_word m
  unfold negN
  cases hm : m.msb
  · simp only [maskN, hm, Bool.false_eq_true, ↓reduceIte]
    rw [BitVec.toNat_and, show (0 : Word).toNat = 0 from rfl, Nat.and_zero]
  · simp only [absW, maskN, hm, ↓reduceIte] at ha ⊢
    rw [BitVec.and_allOnes]; exact ha

theorem signMag_ok (s : State) {m r : Reg} (hz : s.gpr .x12 = 0) (hmr : m ≠ r) (hr12 : r ≠ .x12) :
    WP isa (.block (signMag m r)) s fun t =>
      t.gpr m = absW (s.gpr m) ∧ t.gpr r = maskN (s.gpr m) ∧ Keeps [m, r] s t := by
  apply WP.of_runBlock
  simp only [signMag, runBlock_cons, runStep_some, runBlock_nil, exec_lsr (by decide : 63 < 64),
    exec_sub_x, exec_eor_x, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_write, hmr, Ne.symm hmr, Ne.symm hr12, hz, ite_true, ite_false,
      BitVec.setWidth_eq, mask_eq]
  · simp only [RegUpd.gpr_write, hmr, Ne.symm hmr, Ne.symm hr12, hz, ite_true, ite_false,
      BitVec.setWidth_eq, mask_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [RegUpd.gpr_write, hr'.1, hr'.2, ite_false]

theorem mat_ok (s : State) :
    WP isa (.block mat) s fun t =>
      t.gpr .x12 = 0 ∧
      t.gpr .x4 = absW (s.gpr .x4) ∧ t.gpr .x14 = maskN (s.gpr .x4) ∧
      t.gpr .x5 = absW (s.gpr .x5) ∧ t.gpr .x15 = maskN (s.gpr .x5) ∧
      t.gpr .x6 = absW (s.gpr .x6) ∧ t.gpr .x16 = maskN (s.gpr .x6) ∧
      t.gpr .x7 = absW (s.gpr .x7) ∧ t.gpr .x17 = maskN (s.gpr .x7) ∧
      t.gpr .x13 = (absW (s.gpr .x4) &&& maskN (s.gpr .x4)) + (absW (s.gpr .x5) &&& maskN (s.gpr .x5)) ∧
      t.gpr .x11 = (absW (s.gpr .x6) &&& maskN (s.gpr .x6)) + (absW (s.gpr .x7) &&& maskN (s.gpr .x7)) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s t := by
  simp only [mat, List.append_assoc]
  rw [WP.block_append_iff]
  have hz : WP isa (.block [.movz .x .x12 0 0]) s fun t => t.gpr .x12 = 0 ∧ Keeps [.x12] s t :=
    WP.block_cons_iff.mpr ⟨_, exec_movz, WP.block_nil ⟨RegUpd.gpr_write_self _ _ _ _,
      ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),
        rfl, rfl, rfl, rfl⟩⟩⟩
  refine WP.mono hz fun s0 ⟨z0, k0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (signMag_ok s0 z0 (by decide) (by decide)) fun s1 ⟨m1, r1, k1⟩ => ?_
  have z1 : s1.gpr .x12 = 0 := (k1.gpr _ (by decide)).trans z0
  rw [WP.block_append_iff]
  refine WP.mono (signMag_ok s1 z1 (by decide) (by decide)) fun s2 ⟨m2, r2, k2⟩ => ?_
  have z2 : s2.gpr .x12 = 0 := (k2.gpr _ (by decide)).trans z1
  rw [WP.block_append_iff]
  refine WP.mono (signMag_ok s2 z2 (by decide) (by decide)) fun s3 ⟨m3, r3, k3⟩ => ?_
  have z3 : s3.gpr .x12 = 0 := (k3.gpr _ (by decide)).trans z2
  rw [WP.block_append_iff]
  refine WP.mono (signMag_ok s3 z3 (by decide) (by decide)) fun s4 ⟨m4, r4, k4⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_and_x, exec_add_x,
    Option.some.injEq, exists_eq_left']
  simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  -- each register's value, in terms of `s`
  have g0 : ∀ r, r ≠ .x12 → s0.gpr r = s.gpr r := fun r h => k0.gpr r (by simpa using h)
  have e4 : s4.gpr .x4 = absW (s.gpr .x4) := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), m1, g0 _ (by decide)]
  have e14 : s4.gpr .x14 = maskN (s.gpr .x4) := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), r1, g0 _ (by decide)]
  have e5 : s4.gpr .x5 = absW (s.gpr .x5) := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), m2, k1.gpr _ (by decide), g0 _ (by decide)]
  have e15 : s4.gpr .x15 = maskN (s.gpr .x5) := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), r2, k1.gpr _ (by decide), g0 _ (by decide)]
  have e6 : s4.gpr .x6 = absW (s.gpr .x6) := by
    rw [k4.gpr _ (by decide), m3, k2.gpr _ (by decide), k1.gpr _ (by decide), g0 _ (by decide)]
  have e16 : s4.gpr .x16 = maskN (s.gpr .x6) := by
    rw [k4.gpr _ (by decide), r3, k2.gpr _ (by decide), k1.gpr _ (by decide), g0 _ (by decide)]
  have e7 : s4.gpr .x7 = absW (s.gpr .x7) := by
    rw [m4, k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide), g0 _ (by decide)]
  have e17 : s4.gpr .x17 = maskN (s.gpr .x7) := by
    rw [r4, k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide), g0 _ (by decide)]
  have z4 : s4.gpr .x12 = 0 := (k4.gpr _ (by decide)).trans z3
  refine ⟨z4, e4, e14, e5, e15, e6, e16, e7, e17, by rw [e4, e14, e5, e15],
    by rw [e6, e16, e7, e17], ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h4, h5, h6, h7, h8, h9, h11, h12, h13, h14, h15, h16, h17⟩ := hr
    simp only [RegUpd.gpr_write, h8, h9, h11, h13, ite_false]
    rw [k4.gpr r (by simp [h7, h17]), k3.gpr r (by simp [h6, h16]), k2.gpr r (by simp [h5, h15]),
      k1.gpr r (by simp [h4, h14]), g0 r h12]
  · simp only [RegUpd.mem_write]; rw [k4.mem, k3.mem, k2.mem, k1.mem, k0.mem]
  · simp only [RegUpd.rd_write]; rw [k4.rd, k3.rd, k2.rd, k1.rd, k0.rd]
  · simp only [RegUpd.wr_write]; rw [k4.wr, k3.wr, k2.wr, k1.wr, k0.wr]
  · simp only [RegUpd.sp_write]; rw [k4.sp, k3.sp, k2.sp, k1.sp, k0.sp]

end VG.Proof.Ed25519.AArch64.Inv

end

end

/-! ### `Ed25519.AArch64.Inv.Conn`, which only this module used -/

section

/-! # The inversion's rows as integers

A row of the code (`row_ok`) for the matrix entries `m₁`, `m₂` as `mat`
leaves them (magnitudes and masks) is `m₁ X + m₂ Y` modulo `2³²⁰`: `X`, `Y`
signed for the rows of `f` and `g` (`rowF_int`), unsigned for those of `u`
and `v` (`rowU_int`). -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG VG.AArch64 VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

theorem maskN_cases (w : Word) : (w.msb = true ∧ maskN w = BitVec.allOnes 64) ∨
    (w.msb = false ∧ maskN w = 0) := by
  unfold maskN; cases w.msb <;> simp

theorem flip4_eq (m : Mem) (base : Addr) (o : Nat) (w : Word) :
    flip4 m base o (maskN w) = flipN w (fe m base o) := by
  unfold flipN
  obtain l0 := (word m base o).isLt
  obtain l1 := (word m base (o + 8)).isLt
  obtain l2 := (word m base (o + 16)).isLt
  obtain l3 := (word m base (o + 24)).isLt
  rcases maskN_cases w with ⟨h, e⟩ | ⟨h, e⟩
  · simp only [flip4, e, h, ↓reduceIte, BitVec.xor_allOnes, val4, fe, BitVec.toNat_not]
    omega_using []
  · simp only [flip4, e, h, Bool.false_eq_true, ↓reduceIte, val4, fe, BitVec.toNat_xor,
      show (0 : Word).toNat = 0 from rfl, Nat.xor_zero]

theorem top_msb (m : Mem) (base : Addr) (o : Nat) (w : Word) :
    (word m base (o + 24) ^^^ maskN w).msb = decide (2 ^ 255 ≤ flipN w (fe m base o)) := by
  rw [← flip4_eq]
  obtain l0 := (word m base o ^^^ maskN w).isLt
  obtain l1 := (word m base (o + 8) ^^^ maskN w).isLt
  obtain l2 := (word m base (o + 16) ^^^ maskN w).isLt
  rw [BitVec.msb_eq_decide]
  simp only [flip4, val4]
  congr 1
  apply propext
  omega_using []

theorem corrV_true_eq (m : Mem) (base : Addr) (o : Nat) (w : Word) :
    (corrV true (word m base (o + 24) ^^^ maskN w) (absW w) (maskN w)).toNat =
      topN w (fe m base o) := by
  simp only [corrV, ↓reduceIte, mask_eq]
  unfold topN
  obtain hm : maskN (word m base (o + 24) ^^^ maskN w) =
      if 2 ^ 255 ≤ flipN w (fe m base o) then BitVec.allOnes 64 else 0 := by
    rw [maskN, top_msb]; simp only [decide_eq_true_eq]
  rw [hm]
  split
  · rw [BitVec.allOnes_and, absN_word]
  · rw [BitVec.toNat_and, show (0 : Word).toNat = 0 from rfl, Nat.zero_and]

theorem corrV_false_eq (x : Word) (w : Word) :
    (corrV false x (absW w) (maskN w)).toNat = negN w := by
  simp only [corrV, Bool.false_eq_true, ↓reduceIte]
  rw [BitVec.and_comm]
  exact negN_word w

theorem negN_le_absN (w : Word) : negN w ≤ absN w := by unfold negN; split <;> omega_using []

/-- The carry of two entries, below `2⁶⁴`. -/
theorem car_eq (a b : Word) (h : absN a + absN b < 2 ^ 64) :
    ((absW a &&& maskN a) + (absW b &&& maskN b)).toNat = negN a + negN b := by
  rw [BitVec.toNat_add, negN_word, negN_word]
  have := negN_le_absN a; have := negN_le_absN b
  exact Nat.mod_eq_of_lt (by omega_arith)

/-- A row of `f` and `g` as integers. -/
theorem rowF_int {a b : Word} {X Y W : Nat} (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256)
    (h : (W + 2 ^ 256 * (topN a X + topN b Y)) % (2 ^ 256 * 2 ^ 64) =
      (negN a + negN b + flipN a X * absN a + flipN b Y * absN b) % (2 ^ 256 * 2 ^ 64)) :
    (W : Int) % 2 ^ 320 = (a.toInt * sv X + b.toInt * sv Y) % 2 ^ 320 := by
  obtain e1 := fterm a hX
  obtain e2 := fterm b hY
  rw [Nat.mul_comm (absN a) (flipN a X)] at e1
  rw [Nat.mul_comm (absN b) (flipN b Y)] at e2
  generalize flipN a X * absN a = P1 at e1 h
  generalize flipN b Y * absN b = P2 at e2 h
  rw [show (2 : Int) ^ 320 = 2 ^ 256 * 2 ^ 64 by rw [← pow_add]]
  omega_using [e1, e2, h]

/-- A row of `u` and `v` as integers. -/
theorem rowU_int {a b : Word} {X Y W : Nat} (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256)
    (h : (W + 2 ^ 256 * (negN a + negN b)) % (2 ^ 256 * 2 ^ 64) =
      (negN a + negN b + flipN a X * absN a + flipN b Y * absN b) % (2 ^ 256 * 2 ^ 64)) :
    (W : Int) % 2 ^ 320 = (a.toInt * X + b.toInt * Y) % 2 ^ 320 := by
  obtain e1 := uterm a hX
  obtain e2 := uterm b hY
  rw [Nat.mul_comm (absN a) (flipN a X)] at e1
  rw [Nat.mul_comm (absN b) (flipN b Y)] at e2
  generalize flipN a X * absN a = P1 at e1 h
  generalize flipN b Y * absN b = P2 at e2 h
  rw [show (2 : Int) ^ 320 = 2 ^ 256 * 2 ^ 64 by rw [← pow_add]]
  omega_using [e1, e2, h]

end VG.Proof.Ed25519.AArch64.Inv

end

end

/-! ### `Ed25519.AArch64.Inv.Out`, which only this module used -/

section

/-! # The inversion's rows' results

`shift o t`: the five words at `t` shifted right by 59, four words at `o`
(`shift_ok`). -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG VG.AArch64 VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64 (KeepRegs)
open VG.Impl.Ed25519.AArch64 (ld st)
open VG.Impl.Ed25519.AArch64.Divstep (shift reduce)
open VG.Proof.X25519.AArch64 (exec_lsr exec_lsl exec_sub_x exec_add_x exec_and_x)
open VG.Proof.X25519.AArch64.Alt (exec_mul_x exec_umulh_x exec_adds_x exec_adcs_x exec_adc_x)

variable {large : Bool}

theorem exec_extr_x (s : State) (d n m : Reg) {lsb : Nat} (h : lsb < 64) :
    exec (.extr .x d n m lsb) s = some (s.write .x d ((s.gpr n ++ s.gpr m).extractLsb' lsb 64)) := by
  rw [exec_extr h]
  simp only [State.read, BitVec.setWidth_eq, Size.bits]

/-- The words of a shift by 59. -/
theorem shift_arith (w0 w1 w2 w3 w4 : Nat) (h0 : w0 < 2 ^ 64) (h1 : w1 < 2 ^ 64)
    (h2 : w2 < 2 ^ 64) :
    (w1 * 2 ^ 64 + w0) / 2 ^ 59 % 2 ^ 64 + 2 ^ 64 * ((w2 * 2 ^ 64 + w1) / 2 ^ 59 % 2 ^ 64) +
        2 ^ 128 * ((w3 * 2 ^ 64 + w2) / 2 ^ 59 % 2 ^ 64) +
        2 ^ 192 * ((w4 * 2 ^ 64 + w3) / 2 ^ 59 % 2 ^ 64) =
      (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3 + 2 ^ 256 * w4) / 2 ^ 59 % 2 ^ 256 := by
  omega_using [h0, h1, h2]

/-- The five words at `t` into `x1`–`x3`, `x8`, `x9`. -/
theorem ld5_ok {s : State} {base : Addr} (hs : Scr s base large) {t : Nat}
    (ht : t % 8 = 0 ∧ t + 40 ≤ workSize large) :
    WP isa (.block [ld .x1 t, ld .x2 (t + 8), ld .x3 (t + 16), ld .x8 (t + 24), ld .x9 (t + 32)]) s
      fun u => u.gpr .x1 = word s.mem base t ∧ u.gpr .x2 = word s.mem base (t + 8) ∧
        u.gpr .x3 = word s.mem base (t + 16) ∧ u.gpr .x8 = word s.mem base (t + 24) ∧
        u.gpr .x9 = word s.mem base (t + 32) ∧ Keeps [.x1, .x2, .x3, .x8, .x9] s u := by
  obtain w1 : Reg.x1 ≠ .x0 := by decide
  obtain w2 : Reg.x2 ≠ .x0 := by decide
  obtain w3 : Reg.x3 ≠ .x0 := by decide
  obtain w8 : Reg.x8 ≠ .x0 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    load_sc hs ht.1 (by omega_using [ht]), load_sc (hs.write w1 _) (d := t + 8) (by omega_using [ht]) (by omega_using [ht]),
    load_sc ((hs.write w1 _).write w2 _) (d := t + 16) (by omega_using [ht]) (by omega_using [ht]),
    load_sc (((hs.write w1 _).write w2 _).write w3 _) (d := t + 24) (by omega_using [ht]) (by omega_using [ht]),
    load_sc ((((hs.write w1 _).write w2 _).write w3 _).write w8 _) (d := t + 32) (by omega_using [ht])
      (by omega_using [ht]), Option.some.injEq, exists_eq_left']
  simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    BitVec.setWidth_eq]
  refine ⟨trivial, trivial, trivial, trivial, trivial, ⟨fun r hr => ?_, by simp only [RegUpd.mem_write],
    by simp only [RegUpd.rd_write], by simp only [RegUpd.wr_write], by simp only [RegUpd.sp_write]⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- Four words from `x1`–`x3`, `x8` stored at `o`. -/
theorem st4w_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat}
    (ho : o % 8 = 0 ∧ o + 32 ≤ workSize large) (a b c d : Reg) :
    WP isa (.block [st a o, st b (o + 8), st c (o + 16), st d (o + 24)]) s fun u =>
      u.mem = st4 s.mem base o (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d) ∧ KeepRegs [] s u := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, store_sc hs ho.1 (by omega_using [ho]),
    store_sc (hs.setMem _) (d := o + 8) (by omega_using [ho]) (by omega_using [ho]),
    store_sc ((hs.setMem _).setMem _) (d := o + 16) (by omega_using [ho]) (by omega_using [ho]),
    store_sc (((hs.setMem _).setMem _).setMem _) (d := o + 24) (by omega_using [ho]) (by omega_using [ho]),
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The words loaded, shifted and stored. -/
theorem shift_ok {s : State} {base : Addr} (hs : Scr s base large) {o t : Nat}
    (ho : o % 8 = 0 ∧ o + 32 ≤ workSize large) (ht : t % 8 = 0 ∧ t + 40 ≤ workSize large) :
    WP isa (.block (shift o t)) s fun u =>
      fe u.mem base o = val5 s.mem base t / 2 ^ 59 % 2 ^ 256 ∧ Outside base o 32 s.mem u.mem ∧
      KeepRegs [.x1, .x2, .x3, .x8, .x9] s u := by
  obtain _hcap := workSize_le large
  change WP isa (.block (([ld .x1 t, ld .x2 (t + 8), ld .x3 (t + 16), ld .x8 (t + 24),
    ld .x9 (t + 32)] : List Instr) ++ (([.extr .x .x1 .x2 .x1 59, .extr .x .x2 .x3 .x2 59,
    .extr .x .x3 .x8 .x3 59, .extr .x .x8 .x9 .x8 59] : List Instr) ++
    ([st .x1 o, st .x2 (o + 8), st .x3 (o + 16), st .x8 (o + 24)] : List Instr)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (ld5_ok hs ht) fun a ⟨a1, a2, a3, a8, a9, ka⟩ => ?_
  rw [WP.block_append_iff]
  obtain hx : WP isa (.block ([.extr .x .x1 .x2 .x1 59, .extr .x .x2 .x3 .x2 59,
      .extr .x .x3 .x8 .x3 59, .extr .x .x8 .x9 .x8 59] : List Instr)) a fun b =>
      b.gpr .x1 = (a.gpr .x2 ++ a.gpr .x1).extractLsb' 59 64 ∧
      b.gpr .x2 = (a.gpr .x3 ++ a.gpr .x2).extractLsb' 59 64 ∧
      b.gpr .x3 = (a.gpr .x8 ++ a.gpr .x3).extractLsb' 59 64 ∧
      b.gpr .x8 = (a.gpr .x9 ++ a.gpr .x8).extractLsb' 59 64 ∧ Keeps [.x1, .x2, .x3, .x8] a b := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_extr_x _ _ _ _ (by decide : 59 < 64),
      Option.some.injEq, exists_eq_left']
    simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
    refine ⟨trivial, trivial, trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  refine WP.mono hx fun b ⟨b1, b2, b3, b8, kb⟩ => ?_
  obtain hsb : Scr b base large := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  refine WP.mono (st4w_ok hsb ho .x1 .x2 .x3 .x8) fun u ⟨mu, ku⟩ => ?_
  obtain mb : b.mem = s.mem := by rw [kb.mem, ka.mem]
  refine ⟨?_, ?_, ⟨fun r hr => ?_, by rw [ku.rd, kb.rd, ka.rd], by rw [ku.wr, kb.wr, ka.wr],
    by rw [ku.sp, kb.sp, ka.sp]⟩⟩
  · rw [mu, fe_st4 _ _ (by omega_using [ho, _hcap]), b1, b2, b3, b8, a1, a2, a3, a8, a9]
    simp only [val4, val5, fe, extr_toNat]
    exact shift_arith _ _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
  · rw [mu, mb]; exact st4_outside _ _ (by omega_using [ho, _hcap]) _ _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ku.gpr r (by simp), kb.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]),
      ka.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]

/-! ## The reduction -/

theorem add4_mod (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    val4 (addCarry a0 b0 false) (addCarry a1 b1 (carryOut a0 b0 false))
        (addCarry a2 b2 (carryOut a1 b1 (carryOut a0 b0 false)))
        (addCarry a3 b3 (carryOut a2 b2 (carryOut a1 b1 (carryOut a0 b0 false)))) =
      (val4 a0 a1 a2 a3 + val4 b0 b1 b2 b3) % 2 ^ 256 := by
  obtain h := add4_value a0 a1 a2 a3 b0 b1 b2 b3 false
  dsimp only at h
  obtain hl := val4_lt (addCarry a0 b0 false) (addCarry a1 b1 (carryOut a0 b0 false))
    (addCarry a2 b2 (carryOut a1 b1 (carryOut a0 b0 false)))
    (addCarry a3 b3 (carryOut a2 b2 (carryOut a1 b1 (carryOut a0 b0 false))))
  rw [Bool.toNat_false, Nat.add_zero] at h
  omega_using [h, hl]

/-- The four words `reduce` stores. -/
def redW (w0 w1 w2 w3 w4 : Word) : Word × Word × Word × Word :=
  let q := redQ w3 w4
  let sg := (0 : Word) - (q >>> 63)
  let L := q * 19
  let H := mulHi q 19 - (sg &&& 19)
  let c0 := carryOut w0 L false
  let c1 := carryOut w1 H c0
  let c2 := carryOut w2 sg c1
  (addCarry w0 L false, addCarry w1 H c0, addCarry w2 sg c1, addCarry (w3 + (q <<< 63)) sg c2)

theorem redW_val (w0 w1 w2 w3 w4 : Word) :
    val4 (redW w0 w1 w2 w3 w4).1 (redW w0 w1 w2 w3 w4).2.1 (redW w0 w1 w2 w3 w4).2.2.1
      (redW w0 w1 w2 w3 w4).2.2.2 = redV w0 w1 w2 w3 w4 := by
  simp only [redW, redV]
  exact add4_mod _ _ _ _ _ _ _ _

/-- The words loaded, reduced and stored, given `x12 = 0` and `x13 = 19`. -/
theorem reduce_ok {s : State} {base : Addr} (hs : Scr s base large) {o t : Nat}
    (hz : s.gpr .x12 = 0) (h19 : s.gpr .x13 = 19)
    (ho : o % 8 = 0 ∧ o + 32 ≤ workSize large) (ht : t % 8 = 0 ∧ t + 40 ≤ workSize large) :
    WP isa (.block (reduce o t)) s fun u =>
      fe u.mem base o = redV (word s.mem base t) (word s.mem base (t + 8)) (word s.mem base (t + 16))
        (word s.mem base (t + 24)) (word s.mem base (t + 32)) ∧
      Outside base o 32 s.mem u.mem ∧
      KeepRegs [.x1, .x2, .x3, .x8, .x9, .x10, .x11, .x14, .x15] s u := by
  obtain _hcap := workSize_le large
  change WP isa (.block (([ld .x1 t, ld .x2 (t + 8), ld .x3 (t + 16), ld .x8 (t + 24),
    ld .x9 (t + 32)] : List Instr) ++ (([.extr .x .x10 .x9 .x8 63, .lsr .x .x11 .x9 63,
    .sub .x .x10 .x10 .x11, .lsl .x .x11 .x10 63, .add .x .x8 .x8 .x11,
    .lsr .x .x14 .x10 63, .sub .x .x14 .x12 .x14,
    .mul .x .x9 .x10 .x13, .umulh .x11 .x10 .x13, .logic .and .x .x15 .x14 .x13,
    .sub .x .x11 .x11 .x15,
    .adds .x .x1 .x1 .x9, .adcs .x .x2 .x2 .x11, .adcs .x .x3 .x3 .x14, .adc .x .x8 .x8 .x14] :
      List Instr) ++
    ([st .x1 o, st .x2 (o + 8), st .x3 (o + 16), st .x8 (o + 24)] : List Instr)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (ld5_ok hs ht) fun a ⟨a1, a2, a3, a8, a9, ka⟩ => ?_
  obtain az : a.gpr .x12 = 0 := (ka.gpr _ (by decide)).trans hz
  obtain a19 : a.gpr .x13 = 19 := (ka.gpr _ (by decide)).trans h19
  rw [WP.block_append_iff]
  obtain hx : WP isa (.block ([.extr .x .x10 .x9 .x8 63, .lsr .x .x11 .x9 63,
      .sub .x .x10 .x10 .x11, .lsl .x .x11 .x10 63, .add .x .x8 .x8 .x11,
      .lsr .x .x14 .x10 63, .sub .x .x14 .x12 .x14,
      .mul .x .x9 .x10 .x13, .umulh .x11 .x10 .x13, .logic .and .x .x15 .x14 .x13,
      .sub .x .x11 .x11 .x15,
      .adds .x .x1 .x1 .x9, .adcs .x .x2 .x2 .x11, .adcs .x .x3 .x3 .x14, .adc .x .x8 .x8 .x14] :
        List Instr)) a fun b =>
      b.gpr .x1 = (redW (a.gpr .x1) (a.gpr .x2) (a.gpr .x3) (a.gpr .x8) (a.gpr .x9)).1 ∧
      b.gpr .x2 = (redW (a.gpr .x1) (a.gpr .x2) (a.gpr .x3) (a.gpr .x8) (a.gpr .x9)).2.1 ∧
      b.gpr .x3 = (redW (a.gpr .x1) (a.gpr .x2) (a.gpr .x3) (a.gpr .x8) (a.gpr .x9)).2.2.1 ∧
      b.gpr .x8 = (redW (a.gpr .x1) (a.gpr .x2) (a.gpr .x3) (a.gpr .x8) (a.gpr .x9)).2.2.2 ∧
      Keeps [.x1, .x2, .x3, .x8, .x9, .x10, .x11, .x14, .x15] a b := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_extr_x _ _ _ _ (by decide : 63 < 64),
      exec_lsr (by decide : 63 < 64), exec_lsl (by decide : 63 < 64), exec_sub_x, exec_add_x,
      exec_mul_x, exec_umulh_x, exec_and_x, exec_adds_x, exec_adcs_x, exec_adc_x,
      Option.some.injEq, exists_eq_left']
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
      reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, az, a19]
    refine ⟨?_, ?_, ?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
    any_goals (simp only [redW, redQ, addCarry, carryOut, mulHi, Size.bits]; done)
    any_goals (simp only [redW, redQ, addCarry, carryOut, mulHi, Size.bits]; rfl)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2,
      ite_false]
  refine WP.mono hx fun b ⟨b1, b2, b3, b8, kb⟩ => ?_
  obtain hsb : Scr b base large := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  refine WP.mono (st4w_ok hsb ho .x1 .x2 .x3 .x8) fun u ⟨mu, ku⟩ => ?_
  obtain mb : b.mem = s.mem := by rw [kb.mem, ka.mem]
  refine ⟨?_, ?_, ⟨fun r hr => ?_, by rw [ku.rd, kb.rd, ka.rd], by rw [ku.wr, kb.wr, ka.wr],
    by rw [ku.sp, kb.sp, ka.sp]⟩⟩
  · rw [mu, fe_st4 _ _ (by omega_using [ho, _hcap]), b1, b2, b3, b8, redW_val, a1, a2, a3, a8, a9]
  · rw [mu, mb]; exact st4_outside _ _ (by omega_using [ho, _hcap]) _ _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ku.gpr r (by simp), kb.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
        hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      ka.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1])]

end VG.Proof.Ed25519.AArch64.Inv

end

end


/-! # A batch of the inversion modulo `p` on AArch64

What a batch's proof (`DivstepSound.batch_ok`) is built from: its rows are the
matrix's combinations (`row_ok`, `rowF_rel`, `rowU_rel`), shifted and reduced
(`outs_ok`: `shift_ok`, `reduce_ok`), and it counts down. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG VG.AArch64 VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64 VG.Spec.X25519
open VG.Proof.Mont.AArch64 (KeepRegs Keeps.regs)
open VG.Proof.Divstep (MSt msteps)
open VG.Proof.X25519.AArch64 (exec_movz)
open VG.Impl.Ed25519.AArch64 (ld st)
open VG.Impl.Ed25519.AArch64.Divstep (F G U V TF TG TU TV DSAVE batch shift reduce)

variable {large : Bool}

/-- The registers a batch may change. -/
abbrev batchRegs : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x20]

/-- The low word of a field element, as an integer modulo `2⁶⁴`. -/
theorem low_rel {m : Mem} {base : Addr} {o : Nat} {f : Int} (h : sv (fe m base o) = f) :
    ((word m base o).toNat : Int) % 2 ^ 64 = f % 2 ^ 64 := by
  rw [← h]
  have := (word m base o).isLt
  have := (word m base (o + 8)).isLt
  have := (word m base (o + 16)).isLt
  have := (word m base (o + 24)).isLt
  unfold sv
  simp only [fe, val4]
  split <;> omega_arith

theorem lds3_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block [ld .x1 DSAVE, ld .x2 F, ld .x3 G]) s fun t =>
      t.gpr .x1 = word s.mem base DSAVE ∧ t.gpr .x2 = word s.mem base F ∧
      t.gpr .x3 = word s.mem base G ∧ Keeps [.x1, .x2, .x3] s t := by
  obtain _hmin := workSize_ge large
  change WP isa (.block (([ld .x1 DSAVE] : List Instr) ++ (([ld .x2 F] : List Instr) ++
    ([ld .x3 G] : List Instr)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs (by decide) (by simp only [DSAVE]; omega_arith) .x1) fun a ⟨a1, ka⟩ => ?_
  obtain hsa := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hsa (by decide) (by simp only [F]; omega_arith) .x2) fun b ⟨b2, kb⟩ => ?_
  obtain hsb := hsa.of_keeps kb (by decide)
  refine WP.mono (ld_ok hsb (by decide) (by simp only [G]; omega_arith) .x3) fun t ⟨t3, kt⟩ => ?_
  refine ⟨by rw [kt.gpr _ (by decide), kb.gpr _ (by decide), a1],
    by rw [kt.gpr _ (by decide), b2, ka.mem], by rw [t3, kb.mem, ka.mem], ?_⟩
  exact (ka.mono (by decide)).trans ((kb.mono (by decide)).trans (kt.mono (by decide)))

/-- The registers after `mat`, for the matrix `T`. -/
structure MatRegs (T : MSt) (t : State) : Prop where
  z : t.gpr .x12 = 0
  u : t.gpr .x4 = absW (BitVec.ofInt 64 T.u)
  su : t.gpr .x14 = maskN (BitVec.ofInt 64 T.u)
  v : t.gpr .x5 = absW (BitVec.ofInt 64 T.v)
  sv' : t.gpr .x15 = maskN (BitVec.ofInt 64 T.v)
  q : t.gpr .x6 = absW (BitVec.ofInt 64 T.q)
  sq : t.gpr .x16 = maskN (BitVec.ofInt 64 T.q)
  r : t.gpr .x7 = absW (BitVec.ofInt 64 T.r)
  sr : t.gpr .x17 = maskN (BitVec.ofInt 64 T.r)
  c0 : t.gpr .x13 = (absW (BitVec.ofInt 64 T.u) &&& maskN (BitVec.ofInt 64 T.u)) +
    (absW (BitVec.ofInt 64 T.v) &&& maskN (BitVec.ofInt 64 T.v))
  c1 : t.gpr .x11 = (absW (BitVec.ofInt 64 T.q) &&& maskN (BitVec.ofInt 64 T.q)) +
    (absW (BitVec.ofInt 64 T.r) &&& maskN (BitVec.ofInt 64 T.r))

theorem MatRegs.keep {T : MSt} {t t' : State} (h : MatRegs T t)
    (k : KeepRegs [.x1, .x2, .x3, .x8, .x9, .x10] t t') : MatRegs T t' :=
  ⟨(k.gpr _ (by decide)).trans h.z, (k.gpr _ (by decide)).trans h.u, (k.gpr _ (by decide)).trans h.su,
    (k.gpr _ (by decide)).trans h.v, (k.gpr _ (by decide)).trans h.sv',
    (k.gpr _ (by decide)).trans h.q, (k.gpr _ (by decide)).trans h.sq,
    (k.gpr _ (by decide)).trans h.r, (k.gpr _ (by decide)).trans h.sr,
    (k.gpr _ (by decide)).trans h.c0, (k.gpr _ (by decide)).trans h.c1⟩

theorem absW_le {u : Int} (h : |u| ≤ 2 ^ 59) : (absW (BitVec.ofInt 64 u)).toNat ≤ 2 ^ 62 := by
  rw [absN_word]
  unfold absN
  rw [VG.Proof.Divstep.toInt_small h]
  rw [Int.abs_eq_natAbs] at h
  omega_arith

theorem absN_le {u : Int} (h : |u| ≤ 2 ^ 59) : absN (BitVec.ofInt 64 u) ≤ 2 ^ 59 := by
  unfold absN
  rw [VG.Proof.Divstep.toInt_small h]
  rw [Int.abs_eq_natAbs] at h
  omega_arith

/-- A row of `f` and `g` as the code leaves it, as integers. -/
theorem rowF_rel {m m' : Mem} {base : Addr} {t xo yo : Nat} {a b : Int}
    (ha : |a| ≤ 2 ^ 59) (hb : |b| ≤ 2 ^ 59)
    (h : (val5 m' base t + 2 ^ 256 *
          ((corrV true (word m base (xo + 24) ^^^ maskN (BitVec.ofInt 64 a)) (absW (BitVec.ofInt 64 a))
              (maskN (BitVec.ofInt 64 a))).toNat +
            (corrV true (word m base (yo + 24) ^^^ maskN (BitVec.ofInt 64 b)) (absW (BitVec.ofInt 64 b))
              (maskN (BitVec.ofInt 64 b))).toNat)) % (2 ^ 256 * 2 ^ 64) =
        (((absW (BitVec.ofInt 64 a) &&& maskN (BitVec.ofInt 64 a)) +
            (absW (BitVec.ofInt 64 b) &&& maskN (BitVec.ofInt 64 b))).toNat +
          flip4 m base xo (maskN (BitVec.ofInt 64 a)) * (absW (BitVec.ofInt 64 a)).toNat +
          flip4 m base yo (maskN (BitVec.ofInt 64 b)) * (absW (BitVec.ofInt 64 b)).toNat) % (2 ^ 256 * 2 ^ 64)) :
    (val5 m' base t : Int) % 2 ^ 320 = (a * sv (fe m base xo) + b * sv (fe m base yo)) % 2 ^ 320 := by
  rw [corrV_true_eq, corrV_true_eq, car_eq _ _ (by have := absN_le ha; have := absN_le hb; omega_arith),
    flip4_eq, flip4_eq, absN_word, absN_word] at h
  obtain e := rowF_int (val4_lt _ _ _ _) (val4_lt _ _ _ _) h
  rwa [VG.Proof.Divstep.toInt_small ha, VG.Proof.Divstep.toInt_small hb] at e

/-- A row of `u` and `v` as the code leaves it, as integers. -/
theorem rowU_rel {m m' : Mem} {base : Addr} {t xo yo : Nat} {a b : Int}
    (ha : |a| ≤ 2 ^ 59) (hb : |b| ≤ 2 ^ 59)
    (h : (val5 m' base t + 2 ^ 256 *
          ((corrV false (word m base (xo + 24) ^^^ maskN (BitVec.ofInt 64 a)) (absW (BitVec.ofInt 64 a))
              (maskN (BitVec.ofInt 64 a))).toNat +
            (corrV false (word m base (yo + 24) ^^^ maskN (BitVec.ofInt 64 b)) (absW (BitVec.ofInt 64 b))
              (maskN (BitVec.ofInt 64 b))).toNat)) % (2 ^ 256 * 2 ^ 64) =
        (((absW (BitVec.ofInt 64 a) &&& maskN (BitVec.ofInt 64 a)) +
            (absW (BitVec.ofInt 64 b) &&& maskN (BitVec.ofInt 64 b))).toNat +
          flip4 m base xo (maskN (BitVec.ofInt 64 a)) * (absW (BitVec.ofInt 64 a)).toNat +
          flip4 m base yo (maskN (BitVec.ofInt 64 b)) * (absW (BitVec.ofInt 64 b)).toNat) % (2 ^ 256 * 2 ^ 64)) :
    (val5 m' base t : Int) % 2 ^ 320 = (a * fe m base xo + b * fe m base yo) % 2 ^ 320 := by
  rw [corrV_false_eq, corrV_false_eq, car_eq _ _ (by have := absN_le ha; have := absN_le hb; omega_arith),
    flip4_eq, flip4_eq, absN_word, absN_word] at h
  obtain e := rowU_int (val4_lt _ _ _ _) (val4_lt _ _ _ _) h
  rwa [VG.Proof.Divstep.toInt_small ha, VG.Proof.Divstep.toInt_small hb] at e

theorem prod_bnd {a : Int} {U : Nat} (ha : |a| ≤ 2 ^ 59) (hU : U < 2 ^ 256) :
    -(2 ^ 59 * 2 ^ 256) ≤ a * U ∧ a * U ≤ 2 ^ 59 * 2 ^ 256 := by
  obtain h0 : (0 : Int) ≤ U := by positivity
  obtain h1 : (U : Int) ≤ 2 ^ 256 := by exact_mod_cast hU.le
  rw [abs_le] at ha
  obtain p1 := mul_nonneg (by linarith : (0 : Int) ≤ a + 2 ^ 59) h0
  obtain p2 := mul_nonneg (by linarith : (0 : Int) ≤ 2 ^ 59 - a) h0
  rw [add_mul] at p1
  rw [sub_mul] at p2
  constructor <;> linarith

theorem sum_bnd {a b : Int} {U V : Nat} (ha : |a| ≤ 2 ^ 59) (hb : |b| ≤ 2 ^ 59) (hU : U < 2 ^ 256)
    (hV : V < 2 ^ 256) : -2 ^ 317 ≤ a * U + b * V ∧ a * U + b * V < 2 ^ 317 := by
  obtain h1 := prod_bnd ha hU
  obtain h2 := prod_bnd hb hV
  obtain hK : (0 : Int) < 2 ^ 59 * 2 ^ 256 := by positivity
  rw [show (2 : Int) ^ 317 = 2 ^ 59 * 2 ^ 256 * 2 ^ 2 by rw [← pow_add, ← pow_add]]
  generalize (2 : Int) ^ 59 * 2 ^ 256 = K at h1 h2 hK ⊢
  constructor <;> linarith

theorem val5_out {base : Addr} {o n t : Nat} {m m' : Mem} (h : Outside base o n m m')
    (ht : t + 40 ≤ o ∨ o + n ≤ t) (hl : t + 40 < 2 ^ 64) : val5 m' base t = val5 m base t := by
  simp only [val5]
  rw [h.fe (by omega_arith) (by omega_arith), h.word (by omega_arith) (by omega_arith)]

theorem cnt_val {i : Nat} (hi : i < 10) :
    BitVec.ofNat 64 (10 - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (10 - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

theorem scr_of {rs : List Reg} {s s' : State} {base : Addr} (hs : Scr s base large)
    (h : KeepRegs rs s s') (hr : .x0 ∉ rs) : Scr s' base large :=
  ⟨(h.gpr _ hr).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

/-- The counter one down. -/
theorem cnt_ok (s : State) {i : Nat} (hi : i < 10) (hc : s.gpr .x20 = BitVec.ofNat 64 (10 - i)) :
    WP isa (.block [.subImm .x .x20 .x20 1]) s fun t =>
      t.gpr .x20 = BitVec.ofNat 64 (10 - (i + 1)) ∧ Keeps [.x20] s t :=
  WP.block_cons_iff.mpr ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil
    ⟨by
      rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
      simp only [State.read, hc]
      exact cnt_val hi,
      ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),
        rfl, rfl, rfl, rfl⟩⟩⟩

/-- The five words at `t` reduced, as they were before bytes outside them changed. -/
theorem redV_out {base : Addr} {o n t : Nat} {m m' : Mem} (h : Outside base o n m m')
    (ht : t + 40 ≤ o ∨ o + n ≤ t) (hl : t + 40 < 2 ^ 64) :
    redV (word m' base t) (word m' base (t + 8)) (word m' base (t + 16)) (word m' base (t + 24))
        (word m' base (t + 32)) =
      redV (word m base t) (word m base (t + 8)) (word m base (t + 16)) (word m base (t + 24))
        (word m base (t + 32)) := by
  rw [h.word (by omega_arith) (by omega_arith), h.word (by omega_arith) (by omega_arith), h.word (by omega_arith) (by omega_arith),
    h.word (by omega_arith) (by omega_arith), h.word (by omega_arith) (by omega_arith)]

/-- Five words at `t` reduced. -/
abbrev red5 (m : Mem) (base : Addr) (t : Nat) : Nat :=
  redV (word m base t) (word m base (t + 8)) (word m base (t + 16)) (word m base (t + 24))
    (word m base (t + 32))

/-- The rows shifted and reduced, and the counter one down. -/
theorem outs_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x12 = 0) {i : Nat}
    (hi : i < 10) (hc : s.gpr .x20 = BitVec.ofNat 64 (10 - i)) :
    WP isa (.block (shift F TF ++ (shift G TG ++ (([.movz .x .x13 19 0] : List Instr) ++ (reduce U TU ++
        (reduce V TV ++ ([.subImm .x .x20 .x20 1] : List Instr))))))) s
      fun t =>
        fe t.mem base F = val5 s.mem base TF / 2 ^ 59 % 2 ^ 256 ∧
        fe t.mem base G = val5 s.mem base TG / 2 ^ 59 % 2 ^ 256 ∧
        fe t.mem base U = red5 s.mem base TU ∧ fe t.mem base V = red5 s.mem base TV ∧
        t.gpr .x20 = BitVec.ofNat 64 (10 - (i + 1)) ∧
        word t.mem base DSAVE = word s.mem base DSAVE ∧
        Outside base 192 296 s.mem t.mem ∧ KeepRegs batchRegs s t := by
  obtain _hmin := workSize_ge large
  obtain _hcap := workSize_le large
  rw [WP.block_append_iff]
  refine WP.mono (shift_ok hs (o := F) (t := TF) ⟨by decide, by simp only [F]; omega_arith⟩
    ⟨by decide, by simp only [TF]; omega_arith⟩) fun a ⟨a1, oa, ka⟩ => ?_
  obtain hsa := scr_of hs ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (shift_ok hsa (o := G) (t := TG) ⟨by decide, by simp only [G]; omega_arith⟩
    ⟨by decide, by simp only [TG]; omega_arith⟩) fun b ⟨b1, ob, kb⟩ => ?_
  obtain hsb := scr_of hsa kb (by decide)
  rw [WP.block_append_iff]
  obtain hm : WP isa (.block [.movz .x .x13 19 0]) b fun c => c.gpr .x13 = 19 ∧ Keeps [.x13] b c :=
    WP.block_cons_iff.mpr ⟨_, exec_movz, WP.block_nil ⟨(RegUpd.gpr_write_self _ _ _ _).trans (by decide),
      ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),
        rfl, rfl, rfl, rfl⟩⟩⟩
  refine WP.mono hm fun c ⟨c13, kc⟩ => ?_
  obtain hsc := hsb.of_keeps kc (by decide)
  obtain zc : c.gpr .x12 = 0 := by
    rw [kc.gpr _ (by decide), kb.gpr _ (by decide), ka.gpr _ (by decide), hz]
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok hsc (o := U) (t := TU) zc c13 ⟨by decide, by simp only [U]; omega_arith⟩
    ⟨by decide, by simp only [TU]; omega_arith⟩) fun d ⟨d1, od, kd⟩ => ?_
  obtain hsd := scr_of hsc kd (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok hsd (o := V) (t := TV) ((kd.gpr _ (by decide)).trans zc)
    ((kd.gpr _ (by decide)).trans c13) ⟨by decide, by simp only [V]; omega_arith⟩
    ⟨by decide, by simp only [TV]; omega_arith⟩) fun e ⟨e1, oe, ke⟩ => ?_
  obtain hse := scr_of hsd ke (by decide)
  have mc : c.mem = b.mem := kc.mem
  obtain cnt : e.gpr .x20 = BitVec.ofNat 64 (10 - i) := by
    rw [ke.gpr _ (by decide), kd.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide),
      ka.gpr _ (by decide), hc]
  refine WP.mono (cnt_ok e hi cnt) fun t ⟨t20, kt⟩ => ?_
  obtain ot : Outside base 488 0 e.mem t.mem := by rw [kt.mem]; exact Outside.refl _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, t20, ?_, ?_, ?_⟩
  · rw [ot.fe (by decide) (by decide), oe.fe (by decide) (by decide), od.fe (by decide) (by decide),
      mc, ob.fe (by decide) (by decide), a1]
  · rw [ot.fe (by decide) (by decide), oe.fe (by decide) (by decide), od.fe (by decide) (by decide),
      mc, b1, val5_out oa (by decide) (by decide)]
  · rw [ot.fe (by decide) (by decide), oe.fe (by decide) (by decide), d1, mc,
      redV_out ob (by decide) (by decide), redV_out oa (by decide) (by decide)]
  · rw [ot.fe (by decide) (by decide), e1, redV_out od (by decide) (by decide), mc,
      redV_out ob (by decide) (by decide), redV_out oa (by decide) (by decide)]
  · rw [ot.word (by decide) (by decide), oe.word (by decide) (by decide),
      od.word (by decide) (by decide), mc, ob.word (by decide) (by decide),
      oa.word (by decide) (by decide)]
  · exact ((((oa.mono (by decide) (by decide)).trans (ob.mono (by decide) (by decide))).trans
      (mc ▸ (od.mono (by decide) (by decide)))).trans (oe.mono (by decide) (by decide))).trans
      (ot.mono (by decide) (by decide))
  · exact ((((ka.mono (by decide)).trans (kb.mono (by decide))).trans
      (((Keeps.regs kc).mono (by decide)).trans (kd.mono (by decide)))).trans (ke.mono (by decide))).trans
      ((Keeps.regs kt).mono (by decide))

end VG.Proof.Ed25519.AArch64.Inv
