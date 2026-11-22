module

public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFnG
import VerifiedGarbage.Proof.Mont.AArch64.P521Linear
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Arithmetic
public import VerifiedGarbage.Impl.Mont.AArch64.P256Square
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
public import VerifiedGarbage.Proof.Ed25519.Word64
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Mont.AArch64.P256Square.Core`, which this module and modules that import it used -/

section

/-! ### `Mont.AArch64.P256Square.Words`, which this module and modules that import it used -/

section

/-! Word-level identities for the shift/subtract P-256 reduction. -/

@[expose] public section

namespace VG.Proof.Mont.AArch64.P256Square
open VG.Proof.Ed25519.Word64

/-- The two half-word shifts are the low and high words of `u · 2³²`. -/
theorem shifts (u : BitVec 64) :
    u.toNat * 2 ^ 32 = (u <<< 32).toNat + B * (u >>> 32).toNat := by
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, B]
  have hu := u.isLt
  have h := Nat.mod_add_div u.toNat (2 ^ 32)
  have hm := Nat.mod_lt u.toNat (by decide : 0 < 2 ^ 32)
  omega_using []

/-- The second subtraction cannot borrow: `u >> 32` is strictly below positive `u`. -/
theorem high_no_borrow (u : BitVec 64) :
    carryOut u (~~~(u >>> 32)) (carryOut u (~~~(u <<< 32)) true) = true := by
  have hh := sub_borrow u (u >>> 32) (carryOut u (~~~(u <<< 32)) true)
  have ht := (addCarry u (~~~(u >>> 32)) (carryOut u (~~~(u <<< 32)) true)).isLt
  have hhi : (u >>> 32).toNat = u.toNat / 2 ^ 32 := by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hb := Bool.toNat_le (!(carryOut u (~~~(u <<< 32)) true))
  by_cases hz : u = 0
  · subst hz; decide
  · have hpos : 0 < u.toNat := by
      have hn : u.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq h)
      omega_using [hn]
    have hlt : u.toNat / 2 ^ 32 < u.toNat := Nat.div_lt_self hpos (by decide)
    cases h : carryOut u (~~~(u >>> 32)) (carryOut u (~~~(u <<< 32)) true) with
    | false =>
      rw [h, Bool.not_false, Bool.toNat_true, Nat.mul_one, hhi] at hh
      omega
    | true => rfl

/-- The subtraction pair forms the upper two words of `u (p+1)/B`. -/
theorem subtract_pair (u : BitVec 64) :
    let lo := u <<< 32
    let hi := u >>> 32
    let d0 := addCarry u (~~~lo) true
    let d1 := addCarry u (~~~hi) (carryOut u (~~~lo) true)
    u.toNat * ((p+1)/B) = lo.toNat + B*hi.toNat + 2^128*d0.toNat + 2^192*d1.toNat := by
  have h0 := sub_borrow u (u <<< 32) true
  have h1 := sub_borrow u (u >>> 32) (carryOut u (~~~(u <<< 32)) true)
  rw [high_no_borrow] at h1
  simp only [Bool.not_true, Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at h0 h1
  exact reduction_words (shifts u) h0 h1

/-- A four-word carry chain, with its final carry retained. -/
def add4 (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) × Bool :=
  let c0 := carryOut a0 b0 false
  let c1 := carryOut a1 b1 c0
  let c2 := carryOut a2 b2 c1
  ((addCarry a0 b0 false, addCarry a1 b1 c0, addCarry a2 b2 c1,
    addCarry a3 b3 c2), carryOut a3 b3 c2)

def value4 (a : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) : Nat :=
  val4 a.1 a.2.1 a.2.2.1 a.2.2.2

theorem add4_value (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    value4 (add4 a0 a1 a2 a3 b0 b1 b2 b3).1 + R * (add4 a0 a1 a2 a3 b0 b1 b2 b3).2.toNat =
      val4 a0 a1 a2 a3 + val4 b0 b1 b2 b3 := by
  have h0 := addCarry_value a0 b0 false
  have h1 := addCarry_value a1 b1 (carryOut a0 b0 false)
  have h2 := addCarry_value a2 b2 (carryOut a1 b1 (carryOut a0 b0 false))
  have h3 := addCarry_value a3 b3 (carryOut a2 b2 (carryOut a1 b1 (carryOut a0 b0 false)))
  simp only [add4,value4,val4,R,Bool.toNat_false] at *
  omega_using [h0, h1, h2, h3]

def reduceWords (u v w x : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let lo := u <<< 32
  let hi := u >>> 32
  let d0 := addCarry u (~~~lo) true
  let d1 := addCarry u (~~~hi) (carryOut u (~~~lo) true)
  (add4 v w x d1 lo hi d0 0).1

/-- The four-word reduction implements `(t + low(t)·p)/2⁶⁴` exactly. -/
theorem reduceWords_value (u v w x : BitVec 64) :
    B * value4 (reduceWords u v w x) = val4 u v w x + u.toNat * p := by
  let lo := u <<< 32
  let hi := u >>> 32
  let d0 := addCarry u (~~~lo) true
  let d1 := addCarry u (~~~hi) (carryOut u (~~~lo) true)
  let q := v.toNat + B*w.toNat + 2^128*x.toNat
  have he := add4_value v w x d1 lo hi d0 0
  have hs := subtract_pair u
  change u.toNat * ((p+1)/B) = lo.toNat + B*hi.toNat + 2^128*d0.toNat + 2^192*d1.toNat at hs
  have hq : val4 u v w x = u.toNat + B*q := by
    simp only [val4,q,B,Nat.mul_add,←Nat.mul_assoc]
    omega_using []
  have hr := reduction_round (val4_lt u v w x) u.isLt hq (rfl : q+u.toNat*((p+1)/B)=_)
  have he' : value4 (reduceWords u v w x) + R*(add4 v w x d1 lo hi d0 0).2.toNat =
      q + u.toNat*((p+1)/B) := by
    change value4 (add4 v w x d1 lo hi d0 0).1 + R*(add4 v w x d1 lo hi d0 0).2.toNat = _
    rw [he]
    simp only [val4, B, q]
    rw [show (0 : BitVec 64).toNat = 0 from rfl]
    simp only [B] at hs
    omega_using [hs]
  have hv : value4 (reduceWords u v w x) = q + u.toNat*((p+1)/B) := by
    have hb := Bool.toNat_le (add4 v w x d1 lo hi d0 0).2
    simp only [R] at hr he'
    omega_using [hr, he']
  rw [hv]
  exact hr.1

end VG.Proof.Mont.AArch64.P256Square

end

end

/-! ### `Mont.AArch64.P256Square.Reduce`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Mont.AArch64.P256Square
open VG VG.AArch64 VG.Impl.Mont.AArch64.P256Square
open VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64

abbrev lowValue (s : State) := val4 (s.gpr .x8) (s.gpr .x9) (s.gpr .x10) (s.gpr .x11)
abbrev highValue (s : State) := val4 (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15)
abbrev reduceClob : List Reg := [.x1,.x2,.x3,.x6,.x8,.x9,.x10,.x11]

private theorem reduce_false_ok (s : State) (hz : s.gpr .x7 = 0)
    (hlo : s.gpr .x1 = s.gpr .x8 <<< 32) (hhi : s.gpr .x2 = s.gpr .x8 >>> 32) :
    WP isa (.block (reduceCode false)) s fun t =>
      B*lowValue t = lowValue s + (s.gpr .x8).toNat*p ∧
      (false = true → t.gpr .x1 = t.gpr .x8 <<< 32 ∧ t.gpr .x2 = t.gpr .x8 >>> 32) ∧
      Keeps reduceClob s t := by
  dsimp only [lowValue, reduceClob]
  apply WP.of_runBlock
  simp only [reduceCode, Bool.false_eq_true, ite_false, ite_true, List.append_nil,
      List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
      BitVec.setWidth_eq, reduceCtorEq, hz, hlo, hhi,
      Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := reduceWords_value (s.gpr .x8) (s.gpr .x9) (s.gpr .x10) (s.gpr .x11)
    dsimp only [lowValue, reduceWords, value4, add4, addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · reg_keeps

private theorem reduce_true_ok (s : State) (hz : s.gpr .x7 = 0)
    (hlo : s.gpr .x1 = s.gpr .x8 <<< 32) (hhi : s.gpr .x2 = s.gpr .x8 >>> 32) :
    WP isa (.block (reduceCode true)) s fun t =>
      B*lowValue t = lowValue s + (s.gpr .x8).toNat*p ∧
      (true = true → t.gpr .x1 = t.gpr .x8 <<< 32 ∧ t.gpr .x2 = t.gpr .x8 >>> 32) ∧
      Keeps reduceClob s t := by
  dsimp only [lowValue, reduceClob]
  apply WP.of_runBlock
  simp only [reduceCode, ite_false, ite_true,
      List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
      BitVec.setWidth_eq, reduceCtorEq, hz, hlo, hhi,
      show 32 < Size.x.bits by decide,
      Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := reduceWords_value (s.gpr .x8) (s.gpr .x9) (s.gpr .x10) (s.gpr .x11)
    dsimp only [lowValue, reduceWords, value4, add4, addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · reg_keeps

theorem reduce_ok (s : State) (next : Bool) (hz : s.gpr .x7 = 0)
    (hlo : s.gpr .x1 = s.gpr .x8 <<< 32) (hhi : s.gpr .x2 = s.gpr .x8 >>> 32) :
    WP isa (.block (reduceCode next)) s fun t =>
      B*lowValue t = lowValue s + (s.gpr .x8).toNat*p ∧
      (next = true → t.gpr .x1 = t.gpr .x8 <<< 32 ∧ t.gpr .x2 = t.gpr .x8 >>> 32) ∧
      Keeps reduceClob s t := by
  cases next
  · exact reduce_false_ok s hz hlo hhi
  · exact reduce_true_ok s hz hlo hhi

theorem finish_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block finishCode) s fun t =>
      lowValue t + R*(t.gpr .x12).toNat = lowValue s + highValue s ∧
      Keeps [.x8,.x9,.x10,.x11,.x12] s t := by
  apply WP.of_runBlock
  simp only [finishCode, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := add4_value (s.gpr .x8) (s.gpr .x9) (s.gpr .x10) (s.gpr .x11)
      (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15)
    dsimp only [lowValue, highValue, value4, add4, addCarry, carryOut, Size.bits] at h ⊢
    have hc (c : Bool) : ((0 : BitVec 64) + 0 + BitVec.ofNat 64 c.toNat).toNat = c.toNat := by
      cases c <;> rfl
    simp only [hc]
    exact h
  · reg_keeps

theorem reduceFour_ok (s : State) (hz : s.gpr .x7 = 0)
    (hlo : s.gpr .x1 = s.gpr .x8 <<< 32) (hhi : s.gpr .x2 = s.gpr .x8 >>> 32) :
    WP isa (.block (reduceCode true ++ reduceCode true ++ reduceCode true ++ reduceCode false)) s fun t =>
      (∃ u < R, R*lowValue t = lowValue s + u*p) ∧ Keeps reduceClob s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s true hz hlo hhi) fun s₁ ⟨e₁, h₁, k₁⟩ => ?_
  obtain ⟨lo₁, hi₁⟩ := h₁ rfl
  have z₁ : s₁.gpr .x7 = 0 := (k₁.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s₁ true z₁ lo₁ hi₁) fun s₂ ⟨e₂, h₂, k₂⟩ => ?_
  obtain ⟨lo₂, hi₂⟩ := h₂ rfl
  have z₂ : s₂.gpr .x7 = 0 := (k₂.gpr _ (by decide)).trans z₁
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s₂ true z₂ lo₂ hi₂) fun s₃ ⟨e₃, h₃, k₃⟩ => ?_
  obtain ⟨lo₃, hi₃⟩ := h₃ rfl
  have z₃ : s₃.gpr .x7 = 0 := (k₃.gpr _ (by decide)).trans z₂
  refine WP.mono (reduce_ok s₃ false z₃ lo₃ hi₃) fun t ⟨e₄, _, k₄⟩ => ?_
  refine ⟨⟨val4 (s.gpr .x8) (s₁.gpr .x8) (s₂.gpr .x8) (s₃.gpr .x8),
    val4_lt _ _ _ _, ?_⟩, k₁.trans (k₂.trans (k₃.trans k₄))⟩
  have h := reduction_four (hi := 0) e₁ e₂ e₃ e₄ (rfl : lowValue t = lowValue t + 0)
  simpa only [Nat.mul_zero, Nat.add_zero, val4] using h

end VG.Proof.Mont.AArch64.P256Square

end

end


@[expose] public section

namespace VG.Proof.Mont.AArch64.P256Square
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64
open VG.Impl.Mont.AArch64.P256Square VG.Proof.Mont
open VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- Internal register footprint of the scheduled square; no saved register is used. -/
abbrev squareClob : List Reg := [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17]

structure SquareKeep (base : Addr) (o : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ squareClob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : ∀ x, (ofs base x < o ∨ o+32 ≤ ofs base x) → t.mem x = s.mem x

def core (a : Nat) : List Instr :=
  zero7 :: loads bRegs a ++ (crossCode ++ doubleCode ++ diagCode) ++
  (reduceCode true ++ reduceCode true ++ reduceCode true ++ reduceCode false) ++ finishCode

theorem low_regs (s : State) : regsVal s [.x8,.x9,.x10,.x11] = lowValue s := by
  simp only [regsVal,lowValue,val4,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc]
  omega_using []

theorem load_value {s t : State} {base : Addr} {a : Nat}
    (h : ∀ j (r : Reg), bRegs[j]? = some r → t.gpr r = word s.mem base (a+8*j)) :
    val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x16) (t.gpr .x17) = wordsVal s.mem base a 4 := by
  rw [h 0 .x4 rfl,h 1 .x5 rfl,h 2 .x16 rfl,h 3 .x17 rfl]
  simp only [val4, wordsVal, Nat.mul_zero, Nat.add_zero, Nat.mul_one,
    Nat.mul_add, ←Nat.mul_assoc, Nat.add_assoc]

theorem core_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {a : Nat} (ha : a+32 ≤ size) (ha8 : a%8=0) :
    WP isa (.block (core a)) s fun t =>
      (∃ u < R, R*(lowValue t+R*(t.gpr .x12).toNat) =
        wordsVal s.mem base a 4 * wordsVal s.mem base a 4 + u*p) ∧
      t.gpr .x7 = 0 ∧ Keeps squareClob s t := by
  rw [core, show zero7 :: loads bRegs a = [zero7] ++ loads bRegs a from rfl]
  rw [show (([zero7] ++ loads bRegs a) ++ (crossCode ++ doubleCode ++ diagCode) ++
      (reduceCode true ++ reduceCode true ++ reduceCode true ++ reduceCode false) ++ finishCode) =
      [zero7] ++ (loads bRegs a ++ ((crossCode ++ doubleCode ++ diagCode) ++
      ((reduceCode true ++ reduceCode true ++ reduceCode true ++ reduceCode false) ++ finishCode)))
      by simp only [List.append_assoc]]
  rw [WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₀ ⟨z₀,k₀⟩ => ?_
  rw [WP.block_append_iff]
  rw [loads_eq]
  refine WP.mono (loadsEach_ok bRegs (hs.of_keeps k₀ (by decide)).ptr ha ha8 (by decide) (by decide))
    fun s₁ ⟨l₁,k₁⟩ => ?_
  have hl := load_value l₁
  rw [k₀.mem] at hl
  have z₁ : s₁.gpr .x7=0 := (k₁.gpr _ (by decide)).trans z₀
  rw [WP.block_append_iff]
  refine WP.mono (product_ok s₁ z₁) fun s₂ ⟨e₂,lo₂,hi₂,k₂⟩ => ?_
  have z₂ : s₂.gpr .x7=0 := (k₂.gpr _ (by decide)).trans z₁
  rw [WP.block_append_iff]
  refine WP.mono (reduceFour_ok s₂ z₂ lo₂ hi₂) fun s₃ ⟨⟨u,hu,e₃⟩,k₃⟩ => ?_
  have z₃ : s₃.gpr .x7=0 := (k₃.gpr _ (by decide)).trans z₂
  refine WP.mono (finish_ok s₃ z₃) fun t ⟨e₄,k₄⟩ => ?_
  refine ⟨⟨u,hu,?_⟩,(k₄.gpr _ (by decide)).trans z₃,
    (k₀.mono (by decide)).trans ((k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans
      ((k₃.mono (by decide)).trans (k₄.mono (by decide)))))⟩
  have hh : highValue s₃ = highValue s₂ := by
    dsimp only [highValue]
    rw [k₃.gpr .x12 (by decide),k₃.gpr .x13 (by decide),k₃.gpr .x14 (by decide),k₃.gpr .x15 (by decide)]
  change lowValue s₂+R*highValue s₂ = _ at e₂
  rw [hl] at e₂
  rw [e₄,Nat.mul_add,e₃,hh]
  omega_using [e₂]

/-- Dedicated P-256 Montgomery squaring, including alias-safe loads and stores. -/
theorem square_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {M : Mod} (hN : M.n=4) (hM : ModOkA M size p s.mem base) (hA : ModA M)
    {o a : Nat} (ho : o+32 ≤ size) (ha : a+32 ≤ size) (ho8 : o%8=0) (ha8 : a%8=0)
    (hB : wordsVal s.mem base a 4 < p) :
    WP isa (.block (square M o a)) s fun t => SquareKeep base o s t ∧
      wordsVal t.mem base o 4 < p ∧
      wordsVal t.mem base o 4 * R % p = wordsVal s.mem base a 4 * wordsVal s.mem base a 4 % p := by
  have heq : square M o a = core a ++ (csubR M [.x8,.x9,.x10,.x11] .x12 ++
      stores [.x8,.x9,.x10,.x11] o) := by
    simp only [square,core,List.append_assoc]
  rw [heq,WP.block_append_iff]
  refine WP.mono (core_ok hs ha ha8) fun s₁ ⟨⟨u,hu,e₁⟩,z₁,k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hb := square_redc_bound hB hu e₁
  have hV : regsVal s₁ [.x8,.x9,.x10,.x11] + 2^(64*M.n)*(s₁.gpr .x12).toNat < 2*p := by
    simpa only [low_regs,hN] using hb
  rw [WP.block_append_iff]
  refine WP.mono (csubR_ok hs₁ (M:=M) (ts:=[.x8,.x9,.x10,.x11]) (top:=.x12)
    (by simpa only [List.length_cons,List.length_nil] using hN.symm) hM.n0 hM.n10
    (by unfold Fresh; decide) hM.mo hA.mo z₁ (by rw [k₁.mem]; exact hM.val) hV)
    fun s₂ ⟨e₂,k₂⟩ => ?_
  have hkc : ∀ r ∈ (.x2 :: .x17 :: [.x8,.x9,.x10,.x11] ++ dRegs M.n), r ∈ squareClob := by
    rw [hN]; decide
  have k₂' := k₂.mono hkc
  have hs₂ := hs₁.of_keeps k₂' (by decide)
  refine WP.mono (stores_ok [.x8,.x9,.x10,.x11] hs₂ ho ho8 (by decide))
    fun t ⟨e₃,k₃,o₃⟩ => ?_
  change wordsVal t.mem base o 4 = regsVal s₂ [.x8,.x9,.x10,.x11] at e₃
  have kp := k₁.trans k₂'
  refine ⟨⟨fun r hr => (k₃.gpr r (by simp)).trans (kp.gpr r hr),
    k₃.rd.trans kp.rd,k₃.wr.trans kp.wr,k₃.sp.trans kp.sp,
    fun x hx => (o₃ x hx).trans (congrFun kp.mem x)⟩,?_,?_⟩
  · rw [e₃,e₂]; exact Nat.mod_lt _ (by decide)
  · rw [e₃,e₂,low_regs,hN,Nat.mod_mul_mod,Nat.mul_comm]
    change R*(lowValue s₁+R*(s₁.gpr .x12).toNat)%p = _
    rw [e₁,Nat.add_mul_mod_self_right]

/-- Validated reduction coefficients identify the modulus uniquely. -/
theorem supported_mod {M : Mod} {m : Nat} (h : supported M = true) (hm : M.ok m = true) :
    M.n = 4 ∧ m = p := by
  simp only [supported, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  refine ⟨h.1, ?_⟩
  have hr := M.ok_red hm
  rw [h.2] at hr
  simp only [reduction, Red.ok, Bool.and_eq_true, beq_iff_eq] at hr
  have hd := hr.1.2
  have hl := hr.1.1.2
  change 6277101733925179126845168871924920046849447032244165148672 = (m+1)/2^64 at hd
  have hrem := Nat.mod_add_div m (2^64)
  simp only [p,Spec.P256.curve,Spec.P256.p]
  omega_using [hl, hd]

theorem SquareKeep.toOpKeep {M : Mod} {base : Addr} {o : Nat} {s t : State}
    (h : SquareKeep base o s t) (hn : M.n = 4) : OpKeep M base o s t := by
  refine ⟨fun r hr => h.gpr r ?_,h.rd,h.wr,h.sp,fun x hx _ => h.mem x ?_⟩
  · rw [hn] at hr
    exact fun hh => hr ((by decide : ∀ r ∈ squareClob, r ∈ clob 4) r hh)
  · simpa only [hn] using hx

end VG.Proof.Mont.AArch64.P256Square

end

end

/-!
# Field programs on AArch64

`fprog M ops` runs the field operations `ops` on slots of the working space
(`fprog_ok`), one by one with `mul_ok`, `add_ok` and `sub_ok`: on slots that
are apart from each other, from the modulus and from the temporary area
(`Proof.Mont.Lay`), what the slots stand for (`toM`) follows `runOps ops`, the program
on environments (`Inv`). A slot is read only once it holds a number below
`m`: either it did at the start (`V`) or an earlier operation wrote it
(`Proof.Weierstrass.readsOk`). Only the registers `clob n`, the slots written and the temporary
area change (`ProgKeep`).

The complete addition `rcb` is such a program, and computes `rcbAdd`
(`rcb_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass VG.Proof.Mont.AArch64 VG.Proof.Mont

/-- Products of at most four words are never calls. -/
theorem callOf_small {M : Mod} (h : M.n ≤ 4) : Mont.callOf M = none := by
  unfold Mont.callOf; split
  · have h5 : (5 == M.n) = false := by simp only [beq_eq_false_iff_ne]; omega_arith
    have h6 : (6 == M.n) = false := by simp only [beq_eq_false_iff_ne]; omega_arith
    have h8 : (8 == M.n) = false := by simp only [beq_eq_false_iff_ne]; omega_arith
    have h9 : (9 == M.n) = false := by simp only [beq_eq_false_iff_ne]; omega_arith
    simp only [Mont.fns, List.find?_cons, List.find?_nil, Impl.Weierstrass.Mont.p384p,
      Impl.Weierstrass.Mont.p521p, Impl.Weierstrass.Mont.p384n, Impl.Weierstrass.Mont.p521n,
      Impl.Weierstrass.Mont.brainpoolp512r1p, Impl.Weierstrass.Mont.brainpoolp512r1n,
      Impl.Weierstrass.Mont.brainpoolp384r1p, Impl.Weierstrass.Mont.brainpoolp384r1n,
      Impl.Weierstrass.Mont.brainpoolp320r1p, h5, h6, h8, h9,
      Bool.false_and, Option.map_none]
  · rfl

/-- The slots `Sl`, the modulus and the temporary area are at offsets that
loads and stores can encode; and if the products are calls of a function, it
is one that computes them (`Mont.ModOk`). -/
structure Aligned (M : Mod) (Sl : Nat → Prop) : Prop where
  sl : ∀ x, Sl x → x % 8 = 0
  mod : ModA M
  call : ∀ f m', Mont.callOf M = some (f, m') → Mont.ModOk M.n m'

/-- The slots `l` are below the working space of the function the products
call, if they are calls, as its offsets must be. -/
def Low (M : Mod) (l : List Nat) : Prop :=
  Mont.callOf M = none ∨ ∀ x ∈ l, x + 8 * M.n ≤ Mont.own M.n

theorem Low.small {M : Mod} (hn : M.n ≤ 4) (l : List Nat) : Low M l := .inl (callOf_small hn)

theorem Low.mono {M : Mod} {l l' : List Nat} (h : Low M l) (hl : ∀ x ∈ l', x ∈ l) : Low M l' :=
  h.imp id fun h x hx => h x (hl x hx)

theorem Low.of_call {M : Mod} {l : List Nat}
    (h : ∀ f m', Mont.callOf M = some (f, m') → ∀ x ∈ l, x + 8 * M.n ≤ Mont.own M.n) : Low M l := by
  cases hc : Mont.callOf M with
  | none => exact .inl hc
  | some c => exact .inr (h c.1 c.2 hc)

/-- The state holds the environment `E` in Montgomery's form in the slots
`V`, below `m`, with the modulus in place. -/
structure Inv (M : Mod) (base : Addr) (size m : Nat) [NeZero m] (Sl : Nat → Prop) (V : List Nat)
    (E : Nat → Fin m) (s : State) : Prop where
  scr : Scr s base size
  mod : ModOkA M size m s.mem base
  sl : ∀ x ∈ V, Sl x
  lt : ∀ x ∈ V, wordsVal s.mem base x M.n < m
  val : ∀ x ∈ V, toM m (2 ^ (64 * M.n)) (wordsVal s.mem base x M.n) = E x

theorem Inv.sub {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} {V V' : List Nat}
    {E : Nat → Fin m} {s : State} (h : Inv M base size m Sl V E s) (hV : ∀ x ∈ V', x ∈ V) :
    Inv M base size m Sl V' E s :=
  ⟨h.scr, h.mod, fun x hx => h.sl x (hV x hx), fun x hx => h.lt x (hV x hx),
    fun x hx => h.val x (hV x hx)⟩

/-- What a program writing the slots `W` keeps: the registers but `clob`,
the regions, and the memory but the slots `W` and the temporary area. -/
structure ProgKeep (M : Mod) (base : Addr) (W : List Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob M.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : ∀ x, (∀ w ∈ W, ofs base x < w ∨ w + 8 * M.n ≤ ofs base x) →
    (ofs base x < M.tmp ∨ M.tmp + 8 * M.n ≤ ofs base x) → s'.mem x = s.mem x

theorem ProgKeep.refl (M : Mod) (base : Addr) (W : List Nat) (s : State) : ProgKeep M base W s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem ProgKeep.mono {M : Mod} {base : Addr} {W W' : List Nat} {s s' : State}
    (h : ProgKeep M base W s s') (hW : ∀ w ∈ W, w ∈ W') : ProgKeep M base W' s s' :=
  ⟨h.gpr, h.rd, h.wr, h.sp, fun x hx ht => h.mem x (fun w hw => hx w (hW w hw)) ht⟩

theorem x0_not_clob' (n : Nat) : Reg.x0 ∉ clob n := fun h => absurd (mem_clobAll h) (by decide)

theorem ProgKeep.scr {M : Mod} {base : Addr} {W : List Nat} {s s' : State} {size : Nat}
    (h : ProgKeep M base W s s') (hs : Scr s base size) : Scr s' base size :=
  ⟨(h.gpr _ (x0_not_clob' _)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap, hs.enc⟩

/-- A number in memory apart from what an operation writes. -/
theorem opKeep_wordsVal {M : Mod} {base : Addr} {o : Nat} {s s' : State}
    (h : OpKeep M base o s s') : ∀ {k y : Nat}, (y + 8 * k ≤ o ∨ o + 8 * M.n ≤ y) →
      (y + 8 * k ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ y) → y + 8 * k ≤ 2 ^ 64 →
      wordsVal s'.mem base y k = wordsVal s.mem base y k
  | 0, _, _, _, _ => rfl
  | k + 1, y, ho, ht, hy => by
    simp only [wordsVal]
    have hw : word s'.mem base y = word s.mem base y :=
      Mem.readW_congr fun i hi => h.mem _ (by rw [ofs_off base (by omega_arith)]; omega_arith)
        (by rw [ofs_off base (by omega_arith)]; omega_arith)
    rw [opKeep_wordsVal h (k := k) (y := y + 8) (by omega_arith) (by omega_arith) (by omega_arith), hw]

/-- An operation writing `o`, which then holds `v`, keeps the invariant. -/
theorem Inv.update {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    {V : List Nat} {E : Nat → Fin m} {s s' : State} (hI : Inv M base size m Sl V E s) {o : Nat}
    (ho : Sl o) (hk : OpKeep M base o s s') (hr : wordsVal s'.mem base o M.n < m) {v : Fin m}
    (hv : toM m (2 ^ (64 * M.n)) (wordsVal s'.mem base o M.n) = v) :
    Inv M base size m Sl (o :: V) (Function.update E o v) s' := by
  have hn := hI.scr.nowrap
  have hlo := hL.le o ho
  have hmo := hL.mo o ho
  have hto := hL.tmp o ho
  have hM := hI.mod
  have heq : ∀ x, Sl x → x ≠ o → wordsVal s'.mem base x M.n = wordsVal s.mem base x M.n :=
    fun x hx hxo => by
      have := hL.apart x o hx ho hxo
      have := hL.tmp x hx
      have := hL.le x hx
      exact opKeep_wordsVal hk (by omega_arith) (by omega_arith) (by omega_arith)
  refine ⟨⟨(hk.gpr _ (x0_not_clob' _)).trans hI.scr.x0, hk.wr ▸ hI.scr.wr, hn, hI.scr.enc⟩,
    ⟨hM.n0, hM.n10, hM.mo, hM.tmp, hM.sep, ?_, hM.inv, hM.red, hM.call⟩, ?_, ?_, ?_⟩
  · have := hM.mo
    have := hM.sep
    rw [opKeep_wordsVal hk (by omega_arith) (by omega_arith) (by omega_arith)]
    exact hM.val
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ho
    · exact hI.sl x hx
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; exact hr
    · rw [heq x (hI.sl x (List.mem_of_ne_of_mem hxo hx)) hxo]
      exact hI.lt x (List.mem_of_ne_of_mem hxo hx)
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; rw [Function.update_self]; exact hv
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x (hI.sl x hx') hxo, Function.update_of_ne hxo]
      exact hI.val x hx'

/-- Multiplication dispatches squaring only for validated P-256 coefficients. -/
theorem mulOp_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkA M size m s.mem base) (hA : ModA M) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (opCode M (.mul o a b))) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  rw [opCode]
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl,hsup⟩ := h
    obtain ⟨hn,rfl⟩ := Mont.AArch64.P256Square.supported_mod hsup hM.red
    refine WP.mono (Mont.AArch64.P256Square.square_ok hs hn hM hA
      (by simpa only [hn] using ho) (by simpa only [hn] using hb) ho8 hb8
      (by simpa only [hn] using hB)) fun s' ⟨hk,hlt,he⟩ => ?_
    exact ⟨hk.toOpKeep hn, by simpa only [hn] using hlt, by simpa only [hn] using he⟩
  · exact mul_ok hs hM hA ho ha hb ho8 ha8 hb8 hB

private theorem linearKeep {M : Mod} {base : Addr} {o : Nat} {s t : State}
    (hn : M.n = 9) (k : KeepRegs (clob 9) s t) (O : Outside base o 72 s.mem t.mem) :
    OpKeep M base o s t :=
  ⟨fun r hr => k.gpr r (by simpa only [hn] using hr),k.rd,k.wr,k.sp,
    fun x hx _ => O x (by simpa only [hn] using hx)⟩

theorem addOp_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkA M size m s.mem base) (hA : ModA M) {o a b : Nat}
    (ho : o+8*M.n ≤ size) (ha : a+8*M.n ≤ size) (hb : b+8*M.n ≤ size)
    (ho8 : o%8 = 0) (ha8 : a%8 = 0) (hb8 : b%8 = 0)
    (hAB : wordsVal s.mem base a M.n+wordsVal s.mem base b M.n < 2*m) :
    WP isa (.block (opCode M (.add o a b))) s fun t => OpKeep M base o s t ∧
      wordsVal t.mem base o M.n = (wordsVal s.mem base a M.n+wordsVal s.mem base b M.n)%m := by
  rw [opCode]
  split
  · rename_i h
    obtain ⟨hn,hm⟩ := P521Linear.supported_mod h hM.red
    simp only [hn] at ho ha hb hAB ⊢
    refine WP.mono (P521Linear.add_ok hs ho ha hb ho8 ha8 hb8 hm hAB)
      fun t ⟨he,_,hk,O⟩ => ⟨linearKeep hn hk O,he⟩
  · exact add_ok hs hM hA ho ha hb ho8 ha8 hb8 hAB

theorem subOp_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkA M size m s.mem base) (hMA : ModA M) {o a b : Nat}
    (ho : o+8*M.n ≤ size) (ha : a+8*M.n ≤ size) (hb : b+8*M.n ≤ size)
    (ho8 : o%8 = 0) (ha8 : a%8 = 0) (hb8 : b%8 = 0)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (opCode M (.sub o a b))) s fun t => OpKeep M base o s t ∧
      wordsVal t.mem base o M.n = (wordsVal s.mem base a M.n+m-wordsVal s.mem base b M.n)%m := by
  rw [opCode]
  split
  · rename_i h
    obtain ⟨hn,hm⟩ := P521Linear.supported_mod h hM.red
    simp only [hn] at ho ha hb hA hB ⊢
    refine WP.mono (P521Linear.sub_ok hs ho ha hb ho8 ha8 hb8 hm hA hB)
      fun t ⟨he,_,hk,O⟩ => ⟨linearKeep hn hk O,he⟩
  · exact sub_ok hs hM hMA ho ha hb ho8 ha8 hb8 hA hB

/-- Hand-composed negation blocks use the general subtraction directly. -/
theorem subRaw_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hAl : Aligned M Sl) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {o a b : Nat}
    (hS : ∀ x ∈ (FOp.sub o a b).out::(FOp.sub o a b).ins, Sl x)
    (hR : ∀ x ∈ (FOp.sub o a b).ins, x ∈ V) :
    WP isa (.block (VG.Impl.Mont.AArch64.sub M o a b)) s fun t =>
      OpKeep M base o s t ∧ Inv M base size m Sl (o::V) ((FOp.sub o a b).run E) t := by
  simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq] at hS hR
  have hA := hI.lt a hR.1
  have hB := hI.lt b hR.2
  refine WP.mono (sub_ok hI.scr hI.mod hAl.mod (hL.le o hS.1) (hL.le a hS.2.1)
    (hL.le b hS.2.2) (hAl.sl o hS.1) (hAl.sl a hS.2.1) (hAl.sl b hS.2.2) hA hB)
    fun t ⟨hk,he⟩ => ⟨hk,hI.update hL hS.1 hk ?_ ?_⟩
  · rw [he]; exact Nat.mod_lt _ (by omega_arith)
  · rw [he,toM_sub (by omega_arith),hI.val a hR.1,hI.val b hR.2]

/-- One operation. -/
theorem fop_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x)
    (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (.block (opCode M op)) s fun s' =>
      OpKeep M base op.out s s' ∧ Inv M base size m Sl (op.out :: V) (op.run E) s' := by
  cases op with
  | mul o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    refine WP.mono (mulOp_ok hI.scr hI.mod hAl.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hAl.sl o hS.1) (hAl.sl a hS.2.1) (hAl.sl b hS.2.2) (hI.lt b hR.2)) fun s' ⟨hk, hlt, heq⟩ => ⟨hk, hI.update hL hS.1 hk hlt ?_⟩
    rw [toM_mul hm heq, hI.val a hR.1, hI.val b hR.2]
  | add o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (addOp_ok hI.scr hI.mod hAl.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hAl.sl o hS.1) (hAl.sl a hS.2.1) (hAl.sl b hS.2.2) (by omega_arith)) fun s' ⟨hk, heq⟩ => ⟨hk, hI.update hL hS.1 hk ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega_arith)
    · rw [heq, toM_add, hI.val a hR.1, hI.val b hR.2]
  | sub o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (subOp_ok hI.scr hI.mod hAl.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hAl.sl o hS.1) (hAl.sl a hS.2.1) (hAl.sl b hS.2.2) hA hB)
      fun s' ⟨hk, heq⟩ => ⟨hk, hI.update hL hS.1 hk ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega_arith)
    · rw [heq, toM_sub (by omega_arith), hI.val a hR.1, hI.val b hR.2]

theorem fprog_cons (M : Mod) (op : FOp) (ops : List FOp) :
    fprog M (op :: ops) = opCode M op ++ fprog M ops := rfl

/-- A field program. -/
theorem fprog_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin m} {s : State},
      Inv M base size m Sl V E s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      readsOk ops V = true →
      WP isa (.block (fprog M ops)) s fun s' => ProgKeep M base (ops.map FOp.out) s s' ∧
        Inv M base size m Sl (validAfter ops V) (runOps ops E) s'
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨ProgKeep.refl _ _ _ s, hI⟩
  | op :: ops, V, E, s, hI, hS, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    rw [fprog_cons, WP.block_append_iff]
    refine WP.mono (fop_ok hL hAl hm hI (hS op (List.mem_cons_self ..)) hR.1) fun s₁ ⟨k₁, I₁⟩ => ?_
    refine WP.mono (fprog_ok hL hAl hm ops I₁ (fun op' h => hS op' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨⟨fun r hr => (k₂.gpr r hr).trans (k₁.gpr r hr), k₂.rd.trans k₁.rd,
        k₂.wr.trans k₁.wr, k₂.sp.trans k₁.sp, fun x hx ht => ?_⟩, I₂⟩
    rw [List.map_cons] at hx
    rw [k₂.mem x (fun w hw => hx w (List.mem_cons_of_mem _ hw)) ht,
      k₁.mem x (hx _ (List.mem_cons_self ..)) ht]

set_option exponentiation.threshold 1024 in
/-- One operation, a call for a product modulo a modulus whose products are
calls. -/
theorem opProg_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x)
    (hLow : Low M (op.out :: op.ins)) (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (opProg M op) s fun s' =>
      OpKeep M base op.out s s' ∧ Inv M base size m Sl (op.out :: V) (op.run E) s' := by
  cases op with
  | mul o a b =>
    cases hc : Mont.callOf M with
    | none =>
      simp only [opProg, hc]
      exact fop_ok hL hAl hm hI hS hR
    | some c =>
      obtain ⟨f, m'⟩ := c
      simp only [opProg, hc]
      have hH := hAl.call f m' hc
      have hown : ∀ x ∈ FOp.out (.mul o a b) :: FOp.ins (.mul o a b), x + 8 * M.n ≤ Mont.own M.n :=
        hLow.resolve_left (by rw [hc]; simp)
      have ht : M.tmp = Mont.moAt M.n := by
        rw [Mont.callOf] at hc; split at hc
        · rename_i h; exact h
        · cases hc
      obtain rfl := hI.mod.call f m' hc
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hS hR
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hown
      by_cases hsq : (a == b && sparseOk M.n m') = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at hsq
        obtain ⟨rfl, hsp⟩ := hsq
        obtain ⟨hn6, hm'⟩ := Mont.sparseOk_eq hsp
        subst hm'
        simp only [hsp, beq_self_eq_true, Bool.and_self, ↓reduceIte]
        refine WP.mono (Mont.sqrCall_ok hI.scr hI.mod hn6 ht hown.1 hown.2.1 (hI.lt a hR.1))
          fun s' ⟨hk, hlt, heq⟩ => ⟨hk, hI.update hL hS.1 hk hlt ?_⟩
        rw [toM_mul hm heq, hI.val a hR.1]
      · simp only [Bool.not_eq_true] at hsq
        simp only [hsq, Bool.false_eq_true, ↓reduceIte]
        by_cases hsq521 : (a == b && sqr521Ok M.n m') = true
        · simp only [Bool.and_eq_true, beq_iff_eq] at hsq521
          obtain ⟨rfl, hsp⟩ := hsq521
          obtain ⟨hn9, hm'⟩ := Mont.sqr521Ok_eq hsp
          subst hm'
          simp only [hsp, beq_self_eq_true, Bool.and_self, ↓reduceIte]
          refine WP.mono (Mont.sqrCall521_ok hI.scr hI.mod hn9 ht hown.1 hown.2.1 (hI.lt a hR.1))
            fun s' ⟨hk, hlt, heq⟩ => ⟨hk, hI.update hL hS.1 hk hlt ?_⟩
          rw [toM_mul hm heq, hI.val a hR.1]
        · simp only [Bool.not_eq_true] at hsq521
          simp only [hsq521, Bool.false_eq_true, ↓reduceIte]
          refine WP.mono (Mont.mulCall_ok hI.scr hI.mod hH ht hown.1 hown.2.1 hown.2.2
            (hI.lt b hR.2)) fun s' ⟨hk, hlt, heq⟩ => ⟨hk, hI.update hL hS.1 hk hlt ?_⟩
          rw [toM_mul hm heq, hI.val a hR.1, hI.val b hR.2]
  | add o a b => exact fop_ok hL hAl hm hI hS hR
  | sub o a b => exact fop_ok hL hAl hm hI hS hR

/-- A field program, a call for each product modulo a modulus whose products
are calls. -/
theorem fprogB_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin m} {s : State},
      Inv M base size m Sl V E s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      (∀ op ∈ ops, Low M (op.out :: op.ins)) → readsOk ops V = true →
      WP isa (fprogB M ops) s fun s' => ProgKeep M base (ops.map FOp.out) s s' ∧
        Inv M base size m Sl (validAfter ops V) (runOps ops E) s'
  | [], _, _, s, hI, _, _, _ => WP.block_nil ⟨ProgKeep.refl _ _ _ s, hI⟩
  | [op], V, E, s, hI, hS, hLo, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    refine WP.mono (opProg_ok hL hAl hm hI (hS op (List.mem_cons_self ..)) (hLo op (List.mem_cons_self ..))
      hR.1) fun s₁ ⟨k₁, I₁⟩ =>
      ⟨⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp, fun x hx ht => k₁.mem x (hx _ (List.mem_cons_self ..)) ht⟩, I₁⟩
  | op :: op' :: ops, V, E, s, hI, hS, hLo, hR => by
    rw [readsOk, Bool.and_eq_true, List.all_eq_true] at hR
    simp only [decide_eq_true_eq] at hR
    show WP isa (.seq (opProg M op) (fprogB M (op' :: ops))) s _
    refine WP.seq (WP.mono (opProg_ok hL hAl hm hI (hS op (List.mem_cons_self ..)) (hLo op (List.mem_cons_self ..))
      hR.1) fun s₁ ⟨k₁, I₁⟩ => ?_)
    refine WP.mono (fprogB_ok (ops := op' :: ops) hL hAl hm I₁ (fun op'' h => hS op'' (List.mem_cons_of_mem _ h))
      (fun op'' h => hLo op'' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨⟨fun r hr => (k₂.gpr r hr).trans (k₁.gpr r hr), k₂.rd.trans k₁.rd,
        k₂.wr.trans k₁.wr, k₂.sp.trans k₁.sp, fun x hx ht => ?_⟩, I₂⟩
    rw [List.map_cons] at hx
    rw [k₂.mem x (fun w hw => hx w (List.mem_cons_of_mem _ hw)) ht,
      k₁.mem x (hx _ (List.mem_cons_self ..)) ht]

/-! ## The complete addition -/

/-- `o = p + q` by `rcb`, on slots of `Sl` that are apart (`RcbApart`; `p` may
be `q`), from a state holding `E`, in particular `p`, `q`, `a` and `3b`
(`rcbR`): `o` holds `rcbAdd` of their values, and the slots but those `rcb`
writes (`rcbW`) keep theirs. -/
theorem rcb_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) (hLow : Low M (rcbW S o ++ rcbR S p q)) {V : List Nat}
    {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprogB M (rcb S p q o)) s fun s' => ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl (rcbW S o ++ V) (runOps (rcb S p q o) E) s' ∧
      (runOps (rcb S p q o) E o.x, runOps (rcb S p q o) E o.y, runOps (rcb S p q o) E o.z) =
        VG.Proof.Weierstrass.rcbAdd (E S.a) (E S.b3) (E p.x) (E p.y) (E p.z) (E q.x) (E q.y)
          (E q.z) ∧
      ∀ x, x ∉ rcbW S o → runOps (rcb S p q o) E x = E x := by
  have hR : readsOk (rcb S p q o) V = true := by
    rw [rcb_eq_rename]
    exact readsOk_mono (readsOk_rename _ rcbN_reads) hV
  refine WP.mono (fprogB_ok hL hAl hm _ hI (fun op hop x hx => hSl x (rcb_slots op hop x hx))
    (fun op hop => hLow.mono (rcb_slots op hop)) hR)
    fun s' ⟨hk, hI'⟩ => ⟨hk.mono fun w hw => ?_, hI'.sub fun x hx => ?_, rcb_run hA E,
      fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ rcb_out op hop)⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact rcb_out op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (rcb_out_mem hx)
    · exact Or.inl hx

/-- A formula on numbered slots, renamed to `p`, `q` and `o`: it writes only
`rcbW S o`, and its result is what the numbered formula computes. -/
theorem ofN_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {N : List FOp} (hN : NumOk N) {S : RcbSlots}
    {p q o : Pt} (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    (hLow : Low M (rcbW S o ++ rcbR S p q)) {V : List Nat}
    {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprogB M (ofN N S p q o)) s fun s' => ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl ([o.x, o.y, o.z] ++ V) (runOps (ofN N S p q o) E) s' ∧
      (runOps (ofN N S p q o) E o.x, runOps (ofN N S p q o) E o.y, runOps (ofN N S p q o) E o.z) =
        (runOps N (fun y => E (rcbσ S p q o y)) 6, runOps N (fun y => E (rcbσ S p q o y)) 7,
          runOps N (fun y => E (rcbσ S p q o y)) 8) := by
  have hR : readsOk (ofN N S p q o) V = true := readsOk_mono (ofN_readsOk hN S p q o) hV
  refine WP.mono (fprogB_ok hL hAl hm _ hI (fun op hop x hx => hSl x (ofN_slots op hop x hx))
    (fun op hop => hLow.mono (ofN_slots op hop)) hR)
    fun s' ⟨hk, hI'⟩ => ⟨hk.mono fun w hw => ?_, hI'.sub fun x hx => ?_, ?_⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact ofN_out hN op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem hN hx)
    · exact Or.inl hx
  · exact congrArg₂ Prod.mk (ofN_run hN hA E 6) (congrArg₂ Prod.mk (ofN_run hN hA E 7) (ofN_run hN hA E 8))

/-- `o = p + q` by Algorithm 4 (`a = -3`, with `b` in `S.b3`). -/
theorem rcb3_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) (hLow : Low M (rcbW S o ++ rcbR S p q))
    {V : List Nat} {E : Nat → Fin m}
    {s : State} (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprogB M (rcb3 S p q o)) s fun s' => ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl ([o.x, o.y, o.z] ++ V) (runOps (rcb3 S p q o) E) s' ∧
      (runOps (rcb3 S p q o) E o.x, runOps (rcb3 S p q o) E o.y, runOps (rcb3 S p q o) E o.z) =
        VG.Proof.Weierstrass.rcbAdd3 (E S.b3) (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) (E q.z) := by
  rw [rcb3_eq]
  exact WP.mono (ofN_ok hL hAl hm rcb3N_ok hA hSl hLow hI hV) fun s' ⟨k, I, v⟩ =>
    ⟨k, I, v.trans (rcb3N_run _)⟩

end VG.Proof.Weierstrass.AArch64
