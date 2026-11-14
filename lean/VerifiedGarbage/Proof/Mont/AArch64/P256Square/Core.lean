module

public import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Arithmetic
public import VerifiedGarbage.Impl.Mont.AArch64.P256Square
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
public import VerifiedGarbage.Proof.Ed25519.Word64
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Words
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Framework.Block

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
