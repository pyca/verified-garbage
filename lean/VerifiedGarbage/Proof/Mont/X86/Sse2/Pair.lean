module

public import VerifiedGarbage.Impl.Mont.X86.Sse2
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Mont.X86.Sse2.Lanes
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.TCB.X86.Isa

/-! # The products of the `pmuludq` kernel

`pair` (two products) and `single` (one), stated on the state they leave
(`SseOnly`: only `xmm0` to `xmm3` change) and on the sums' lanes (`Sums`):
the products added to `xmm0` modulo `2⁶⁴`, their high words to `xmm1`.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.RegUpd VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2

/-! ## Fields through register writes -/

theorem ea_setXmm (s : State) (r : XReg) (v : BitVec 128) (m : MemOp) : (s.setXmm r v).ea m = s.ea m := rfl
theorem mcdt_setXmm (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).mcdt = s.mcdt := rfl
theorem mcdt_setReg (s : State) (r : Reg) (v : BitVec 32) : (s.setReg r v).mcdt = s.mcdt := rfl
theorem mcdt_setFlags (s : State) (a b c d : Option Bool) : (s.setFlags a b c d).mcdt = s.mcdt := rfl
theorem mcdt_arithFlags (s : State) (x : BitVec 32) (c o : Bool) : (arithFlags s x c o).mcdt = s.mcdt := rfl

/-- Only `xmm0` to `xmm3` changed. -/
structure SseOnly (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  cf : t.cf = s.cf
  zf : t.zf = s.zf
  mcdt : t.mcdt = s.mcdt
  x4 : t.xmm .xmm4 = s.xmm .xmm4
  x5 : t.xmm .xmm5 = s.xmm .xmm5
  x6 : t.xmm .xmm6 = s.xmm .xmm6
  x7 : t.xmm .xmm7 = s.xmm .xmm7

/-! ## The sums -/

/-- The sums' lanes: `xmm0`'s add to `S` modulo `2⁶⁴`, `xmm1`'s exactly to `H`. -/
structure Sums (x0 x1 : BitVec 128) (S H : Nat) : Prop where
  low : qword x0 0 + qword x0 1 = BitVec.ofNat 64 S
  high : (qword x1 0).toNat + (qword x1 1).toNat = H

/-- Adding a vector of two products `p` (and their high words to the high sums). -/
theorem Sums.add {x0 x1 p : BitVec 128} {S H : Nat} (h : Sums x0 x1 S H) {p0 p1 : Nat}
    (e0 : qword p 0 = BitVec.ofNat 64 p0) (e1 : qword p 1 = BitVec.ofNat 64 p1)
    (b0 : p0 < 2 ^ 64) (b1 : p1 < 2 ^ 64) (hH : H + 2 ^ 32 < 2 ^ 64) :
    Sums (XBinOp.eval .paddq x0 p) (XBinOp.eval .paddq x1 (XShiftOp.eval .psrlq p 32))
      (S + p0 + p1) (H + p0 / 2 ^ 32 + p1 / 2 ^ 32) := by
  have q0 : p0 / 2 ^ 32 < 2 ^ 32 := (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega)
  have q1 : p1 / 2 ^ 32 < 2 ^ 32 := (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega)
  have hh := h.high
  refine ⟨?_, ?_⟩
  · rw [qword_paddq _ _ (by decide), qword_paddq _ _ (by decide), e0, e1]
    rw [show qword x0 0 + BitVec.ofNat 64 p0 + (qword x0 1 + BitVec.ofNat 64 p1) =
      (qword x0 0 + qword x0 1) + BitVec.ofNat 64 p0 + BitVec.ofNat 64 p1 by ac_rfl, h.low]
    simp only [BitVec.ofNat_add]
  · rw [qword_paddq _ _ (by decide), qword_paddq _ _ (by decide), qword_psrlq _ (by decide),
      qword_psrlq _ (by decide), e0, e1]
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt b0, Nat.mod_eq_of_lt b1, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## `pair` -/

/-- The products of a pair: the words `v` at `X_i` and `w` at `Y_(k-i-1)`. -/
def pairP (v w : BitVec 64) : BitVec 128 :=
  pmuludq (shufDwords ((0 : BitVec 64) ++ v) 0x10) (shufDwords ((0 : BitVec 64) ++ w) 0x01)

theorem pairP_0 (v w : BitVec 64) :
    qword (pairP v w) 0 = BitVec.ofNat 64 ((v.extractLsb' 0 32).toNat * (w.extractLsb' 32 32).toNat) := by
  rw [pairP, qword_pmuludq_0, dword_shuf10_0, dword_shuf01_0, dword_movq_0, dword_movq_1, mul_setWidth]

theorem pairP_1 (v w : BitVec 64) :
    qword (pairP v w) 1 = BitVec.ofNat 64 ((v.extractLsb' 32 32).toNat * (w.extractLsb' 0 32).toNat) := by
  rw [pairP, qword_pmuludq_1, dword_shuf10_2, dword_shuf01_2, dword_movq_1, dword_movq_0, mul_setWidth]

theorem word_mul_lt (x y : BitVec 32) : x.toNat * y.toNat < 2 ^ 64 := by
  have := Nat.mul_lt_mul'' x.isLt y.isLt; simpa using this

theorem pair_run (s : State) (dx dy : Nat) (hm : 0 < s.mcdt)
    (h1 : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi dx)) 8) (h2 : InRegions (s.rd ++ s.wr) (s.ea (at_ .edi dy)) 8) :
    ∃ t, runBlock isa (pair dx dy) s = some t ∧ SseOnly s t ∧
      t.xmm .xmm0 = XBinOp.eval .paddq (s.xmm .xmm0)
        (pairP (s.mem.readW (s.ea (at_ .esi dx)) 64) (s.mem.readW (s.ea (at_ .edi dy)) 64)) ∧
      t.xmm .xmm1 = XBinOp.eval .paddq (s.xmm .xmm1) (XShiftOp.eval .psrlq
        (pairP (s.mem.readW (s.ea (at_ .esi dx)) 64) (s.mem.readW (s.ea (at_ .edi dy)) 64)) 32) := by
  simp only [pair, acc, List.cons_append, List.nil_append, runBlock_cons, exec, State.load64, h1,
    Option.map_some, runStep_some, XOp.exec, ↓reduceIte, Option.some.injEq, exists_eq_left',
    rd_setXmm, wr_setXmm, mem_setXmm, ea_setXmm, h2, mcdt_setXmm, hm, xmm_setXmm, reduceCtorEq, runBlock_nil]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [xmm_setXmm, reduceCtorEq, ↓reduceIte, pairP, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm,
      cf_setXmm, zf_setXmm, mcdt_setXmm]

/-- A pair's effect on the sums: `X_i Y_(k-i)` and `X_(i+1) Y_(k-i-1)`, for the
words `x0`, `x1` at `X_i` and `y0`, `y1` at `Y_(k-i-1)`. -/
theorem pair_sums {s t : State} {S H : Nat} (hs : Sums (s.xmm .xmm0) (s.xmm .xmm1) S H)
    (hH : H + 2 ^ 32 < 2 ^ 64) {v w : BitVec 64}
    (h0 : t.xmm .xmm0 = XBinOp.eval .paddq (s.xmm .xmm0) (pairP v w))
    (h1 : t.xmm .xmm1 = XBinOp.eval .paddq (s.xmm .xmm1) (XShiftOp.eval .psrlq (pairP v w) 32)) :
    let x0 := (v.extractLsb' 0 32).toNat
    let x1 := (v.extractLsb' 32 32).toNat
    let y0 := (w.extractLsb' 0 32).toNat
    let y1 := (w.extractLsb' 32 32).toNat
    Sums (t.xmm .xmm0) (t.xmm .xmm1) (S + x0 * y1 + x1 * y0) (H + x0 * y1 / 2 ^ 32 + x1 * y0 / 2 ^ 32) := by
  intro x0 x1 y0 y1
  rw [h0, h1]
  exact hs.add (pairP_0 v w) (pairP_1 v w) (word_mul_lt _ _) (word_mul_lt _ _) hH

/-! ## `single` -/

/-- The product of `single`: the words `x` and `y` in doublewords 0. -/
def singleP (x y : BitVec 32) : BitVec 128 :=
  pmuludq ((0 : BitVec 96) ++ x) ((0 : BitVec 96) ++ y)

theorem singleP_0 (x y : BitVec 32) : qword (singleP x y) 0 = BitVec.ofNat 64 (x.toNat * y.toNat) := by
  rw [singleP, qword_pmuludq_0, dword_movd_0, dword_movd_0, mul_setWidth]

theorem singleP_1 (x y : BitVec 32) : qword (singleP x y) 1 = BitVec.ofNat 64 0 := by
  rw [singleP, qword_pmuludq_1, dword_movd_2, dword_movd_2]; rfl

theorem single_run (s : State) (hm : 0 < s.mcdt)
    (h1 : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi 0)) 4) (h2 : InRegions (s.rd ++ s.wr) (s.ea (at_ .edi 4)) 4) :
    ∃ t, runBlock isa single s = some t ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mcdt = s.mcdt ∧
      (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧
      t.xmm .xmm4 = s.xmm .xmm4 ∧ t.xmm .xmm5 = s.xmm .xmm5 ∧ t.xmm .xmm6 = s.xmm .xmm6 ∧
      t.xmm .xmm7 = s.xmm .xmm7 ∧
      t.xmm .xmm0 = XBinOp.eval .paddq (s.xmm .xmm0)
        (singleP (s.mem.readW (s.ea (at_ .esi 0)) 32) (s.mem.readW (s.ea (at_ .edi 4)) 32)) ∧
      t.xmm .xmm1 = XBinOp.eval .paddq (s.xmm .xmm1) (XShiftOp.eval .psrlq
        (singleP (s.mem.readW (s.ea (at_ .esi 0)) 32) (s.mem.readW (s.ea (at_ .edi 4)) 32)) 32) := by
  have ea2 : ∀ v : BitVec 32, (s.setReg .eax v).ea (at_ .edi 4) = s.ea (at_ .edi 4) := fun _ => rfl
  have ea2' : ∀ (v : BitVec 32) (x : BitVec 128),
      ((s.setReg .eax v).setXmm .xmm2 x).ea (at_ .edi 4) = s.ea (at_ .edi 4) := fun _ _ => rfl
  simp only [single, acc, List.cons_append, List.nil_append, runBlock_cons, exec, readSrc, State.load32, h1,
    Option.map_some, runStep_some, XOp.exec, ↓reduceIte, Option.some.injEq, exists_eq_left',
    rd_setXmm, wr_setXmm, mem_setXmm, rd_setReg, wr_setReg, mem_setReg, ea2', h2, mcdt_setXmm, mcdt_setReg, hm,
    xmm_setXmm, xmm_setReg, reduceCtorEq, runBlock_nil, gpr_setXmm, gpr_setReg_self]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, trivial, trivial, trivial, trivial, rfl, rfl⟩
  simp only [gpr_setXmm, gpr_setReg_of_ne _ _ hr]

theorem single_sums {s t : State} {S H : Nat} (hs : Sums (s.xmm .xmm0) (s.xmm .xmm1) S H)
    (hH : H + 2 ^ 32 < 2 ^ 64) {x y : BitVec 32}
    (h0 : t.xmm .xmm0 = XBinOp.eval .paddq (s.xmm .xmm0) (singleP x y))
    (h1 : t.xmm .xmm1 = XBinOp.eval .paddq (s.xmm .xmm1) (XShiftOp.eval .psrlq (singleP x y) 32)) :
    Sums (t.xmm .xmm0) (t.xmm .xmm1) (S + x.toNat * y.toNat) (H + x.toNat * y.toNat / 2 ^ 32) := by
  rw [h0, h1]
  have := hs.add (singleP_0 x y) (singleP_1 x y) (word_mul_lt _ _) (by decide) hH
  simpa using this

end VG.Proof.Mont.X86.Sse2
