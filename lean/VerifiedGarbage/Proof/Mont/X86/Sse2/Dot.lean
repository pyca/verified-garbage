module

public import VerifiedGarbage.Impl.Mont.X86.Sse2
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Mont.X86.Sse2.Lanes
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Proof.Framework.X86.Reduce
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Mont.X86.Sse2.Pair`, which only this module used -/

section

/-! # The products of the `pmuludq` kernel

`turn` (four products, in any registers apart from the sums' and the
digits'), `pairMul` (two) and `single` (one), stated on the state they leave
(`SseOnly`: of the registers, only `xmm0` to `xmm5` and `xmm7` change, and
`eax` for `single`) and on the sums' lanes (`Sums`): the
products added to `xmm0` modulo `2⁶⁴`, their high words to `xmm1`. Each
product is of the words at the same offset from `esi` and from `edi`
(`pw`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.RegUpd VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2

/-! ## Fields through register writes -/

theorem ea_setXmm (s : State) (r : XReg) (v : BitVec 128) (m : MemOp) : (s.setXmm r v).ea m = s.ea m := rfl
theorem mcdt_setXmm (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).mcdt = s.mcdt := rfl
theorem mcdt_setReg (s : State) (r : Reg) (v : BitVec 32) : (s.setReg r v).mcdt = s.mcdt := rfl
/-- Only `xmm0` to `xmm5` and `xmm7` changed. -/
structure SseOnly (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  cf : t.cf = s.cf
  zf : t.zf = s.zf
  mcdt : t.mcdt = s.mcdt
  x6 : t.xmm .xmm6 = s.xmm .xmm6

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
  have q0 : p0 / 2 ^ 32 < 2 ^ 32 := (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega_using [b0])
  have q1 : p1 / 2 ^ 32 < 2 ^ 32 := (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega_using [b1])
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
      Nat.mod_eq_of_lt (by omega_using [b0, hH, hh]), Nat.mod_eq_of_lt (by omega_using [b1, hH, hh])]
    omega_using [hh]

theorem word_mul_lt (x y : BitVec 32) : x.toNat * y.toNat < 2 ^ 64 := by
  have := Nat.mul_lt_mul'' x.isLt y.isLt; simpa using this

/-- The product of the words at `a` and `b`. -/
def pw (m : Mem) (a b : Addr) : Nat := (m.readW a 32).toNat * (m.readW b 32).toNat

/-- Two products by `pmuludq`, of doublewords 0 and 2. -/
theorem Sums.addMul {x0 x1 u v : BitVec 128} {S H : Nat} (h : Sums x0 x1 S H) (hH : H + 2 ^ 32 < 2 ^ 64) :
    Sums (XBinOp.eval .paddq x0 (pmuludq u v)) (XBinOp.eval .paddq x1 (XShiftOp.eval .psrlq (pmuludq u v) 32))
      (S + (dword u 0).toNat * (dword v 0).toNat + (dword u 2).toNat * (dword v 2).toNat)
      (H + (dword u 0).toNat * (dword v 0).toNat / 2 ^ 32 + (dword u 2).toNat * (dword v 2).toNat / 2 ^ 32) :=
  h.add (by rw [qword_pmuludq_0, mul_setWidth]) (by rw [qword_pmuludq_1, mul_setWidth])
    (word_mul_lt _ _) (word_mul_lt _ _) hH

/-- Doubleword `j` of a 16-byte read. -/
theorem dword_read128 (m : Mem) (a : Addr) {j : Nat} (hj : j < 4) :
    (dword (m.readW a 128) j).toNat = (m.readW (a + BitVec.ofNat 64 (4 * j)) 32).toNat := by
  rw [dword_readW m a hj]

/-! ## `turn` -/

/-- A turn's three registers: apart from each other, from the sums' and from the digits'. -/
structure TurnRegs (e o y : XReg) : Prop where
  eo : e ≠ o
  ey : e ≠ y
  oy : o ≠ y
  e0 : e ≠ .xmm0
  e1 : e ≠ .xmm1
  e6 : e ≠ .xmm6
  o0 : o ≠ .xmm0
  o1 : o ≠ .xmm1
  o6 : o ≠ .xmm6
  y0 : y ≠ .xmm0
  y1 : y ≠ .xmm1
  y6 : y ≠ .xmm6

/-- A turn, in any registers and at any offset from the pointers: the products of the two
16-byte reads' even doublewords, and of their odd ones, into the sums. -/
theorem turn_run (s : State) (hm : 0 < s.mcdt) {e o y : XReg} (R : TurnRegs e o y) (d : Nat)
    (h1 : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi d)) 16) (h2 : InRegions (s.rd ++ s.wr) (s.ea (at_ .edi d)) 16) :
    ∃ t, runBlock isa (turn e o y d) s = some t ∧ SseOnly s t ∧
      t.xmm .xmm0 = XBinOp.eval .paddq (XBinOp.eval .paddq (s.xmm .xmm0)
        (pmuludq (s.mem.readW (s.ea (at_ .esi d)) 128) (s.mem.readW (s.ea (at_ .edi d)) 128)))
        (pmuludq (shufDwords (s.mem.readW (s.ea (at_ .esi d)) 128) 0x31)
          (XShiftOp.eval .psrlq (s.mem.readW (s.ea (at_ .edi d)) 128) 32)) ∧
      t.xmm .xmm1 = XBinOp.eval .paddq (XBinOp.eval .paddq (s.xmm .xmm1) (XShiftOp.eval .psrlq
        (pmuludq (s.mem.readW (s.ea (at_ .esi d)) 128) (s.mem.readW (s.ea (at_ .edi d)) 128)) 32))
        (XShiftOp.eval .psrlq (pmuludq (shufDwords (s.mem.readW (s.ea (at_ .esi d)) 128) 0x31)
          (XShiftOp.eval .psrlq (s.mem.readW (s.ea (at_ .edi d)) 128) 32)) 32) := by
  obtain ⟨eo, ey, oy, e0, e1, e6, o0, o1, o6, y0, y1, y6⟩ := R
  simp only [turn, acc, List.cons_append, List.nil_append, runBlock_cons, reduceExec, State.load128, h1, h2,
    Option.map_some, runStep_some, XOp.exec, ↓reduceIte, Option.some.injEq, exists_eq_left',
    rd_setXmm, wr_setXmm, mem_setXmm, ea_setXmm, mcdt_setXmm, hm, xmm_setXmm, runBlock_nil,
    eo, eo.symm, ey, ey.symm, oy, oy.symm, e0, e0.symm, e1, e1.symm, o0, o0.symm, o1, o1.symm, y0, y0.symm,
    y1, y1.symm, reduceCtorEq]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [xmm_setXmm, reduceCtorEq, ↓reduceIte, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm,
      cf_setXmm, zf_setXmm, mcdt_setXmm, e6.symm, o6.symm, y6.symm]

theorem dword_shuf31_0 (a : BitVec 128) : dword (shufDwords a 0x31) 0 = dword a 1 := by
  rw [dword_shufDwords _ _ (by decide)]; rfl

theorem dword_shuf31_2 (a : BitVec 128) : dword (shufDwords a 0x31) 2 = dword a 3 := by
  rw [dword_shufDwords _ _ (by decide)]; rfl

/-- The four products of a turn, of the 16 bytes at `x` and at `y`. -/
theorem turn_sums {s t : State} {S H : Nat} (hs : Sums (s.xmm .xmm0) (s.xmm .xmm1) S H)
    (hH : H + 4 * 2 ^ 32 < 2 ^ 64) {x y : Addr}
    (h0 : t.xmm .xmm0 = XBinOp.eval .paddq (XBinOp.eval .paddq (s.xmm .xmm0)
      (pmuludq (s.mem.readW x 128) (s.mem.readW y 128)))
      (pmuludq (shufDwords (s.mem.readW x 128) 0x31) (XShiftOp.eval .psrlq (s.mem.readW y 128) 32)))
    (h1 : t.xmm .xmm1 = XBinOp.eval .paddq (XBinOp.eval .paddq (s.xmm .xmm1) (XShiftOp.eval .psrlq
      (pmuludq (s.mem.readW x 128) (s.mem.readW y 128)) 32))
      (XShiftOp.eval .psrlq (pmuludq (shufDwords (s.mem.readW x 128) 0x31)
        (XShiftOp.eval .psrlq (s.mem.readW y 128) 32)) 32)) :
    Sums (t.xmm .xmm0) (t.xmm .xmm1)
      (S + pw s.mem x y + pw s.mem (x + 8) (y + 8) + pw s.mem (x + 4) (y + 4) + pw s.mem (x + 12) (y + 12))
      (H + pw s.mem x y / 2 ^ 32 + pw s.mem (x + 8) (y + 8) / 2 ^ 32 + pw s.mem (x + 4) (y + 4) / 2 ^ 32 +
        pw s.mem (x + 12) (y + 12) / 2 ^ 32) := by
  have a1 := hs.addMul (u := s.mem.readW x 128) (v := s.mem.readW y 128) (by omega_using [hH])
  have q0 := Nat.div_lt_iff_lt_mul (k := 2 ^ 32) (x := (dword (s.mem.readW x 128) 0).toNat *
    (dword (s.mem.readW y 128) 0).toNat) (y := 2 ^ 32) (by decide) |>.2 (by have := word_mul_lt (dword (s.mem.readW x 128) 0) (dword (s.mem.readW y 128) 0); omega_using [this])
  have q2 := Nat.div_lt_iff_lt_mul (k := 2 ^ 32) (x := (dword (s.mem.readW x 128) 2).toNat *
    (dword (s.mem.readW y 128) 2).toNat) (y := 2 ^ 32) (by decide) |>.2 (by have := word_mul_lt (dword (s.mem.readW x 128) 2) (dword (s.mem.readW y 128) 2); omega_using [this])
  have a2 := a1.addMul (u := shufDwords (s.mem.readW x 128) 0x31) (v := XShiftOp.eval .psrlq (s.mem.readW y 128) 32) (by omega_using [hH, q0, q2])
  rw [h0, h1]
  rw [dword_shuf31_0, dword_psrlq_0, dword_shuf31_2, dword_psrlq_2] at a2
  simp only [dword_read128 _ _ (show 0 < 4 by decide),
    dword_read128 _ _ (show 1 < 4 by decide), dword_read128 _ _ (show 2 < 4 by decide),
    dword_read128 _ _ (show 3 < 4 by decide), Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    show 4 * 1 = 4 from rfl, show 4 * 2 = 8 from rfl, show 4 * 3 = 12 from rfl] at a2
  exact a2

/-! ## `pairMul` -/

theorem pairMul_run (s : State) (hm : 0 < s.mcdt)
    (h1 : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi 0)) 8) (h2 : InRegions (s.rd ++ s.wr) (s.ea (at_ .edi 0)) 8) :
    ∃ t, runBlock isa pairMul s = some t ∧ SseOnly s t ∧
      t.xmm .xmm0 = XBinOp.eval .paddq (s.xmm .xmm0)
        (pmuludq (XBinOp.eval .punpckldq ((0 : BitVec 64) ++ s.mem.readW (s.ea (at_ .esi 0)) 64)
            ((0 : BitVec 64) ++ s.mem.readW (s.ea (at_ .esi 0)) 64))
          (XBinOp.eval .punpckldq ((0 : BitVec 64) ++ s.mem.readW (s.ea (at_ .edi 0)) 64)
            ((0 : BitVec 64) ++ s.mem.readW (s.ea (at_ .edi 0)) 64))) ∧
      t.xmm .xmm1 = XBinOp.eval .paddq (s.xmm .xmm1) (XShiftOp.eval .psrlq
        (pmuludq (XBinOp.eval .punpckldq ((0 : BitVec 64) ++ s.mem.readW (s.ea (at_ .esi 0)) 64)
            ((0 : BitVec 64) ++ s.mem.readW (s.ea (at_ .esi 0)) 64))
          (XBinOp.eval .punpckldq ((0 : BitVec 64) ++ s.mem.readW (s.ea (at_ .edi 0)) 64)
            ((0 : BitVec 64) ++ s.mem.readW (s.ea (at_ .edi 0)) 64))) 32) := by
  simp only [pairMul, acc, List.cons_append, List.nil_append, runBlock_cons, reduceExec, State.load64, h1, h2,
    Option.map_some, runStep_some, XOp.exec, ↓reduceIte, Option.some.injEq, exists_eq_left',
    rd_setXmm, wr_setXmm, mem_setXmm, ea_setXmm, mcdt_setXmm, hm, xmm_setXmm, reduceCtorEq, runBlock_nil]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [xmm_setXmm, reduceCtorEq, ↓reduceIte, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm,
      cf_setXmm, zf_setXmm, mcdt_setXmm]

theorem dword_unpack_0 (v : BitVec 64) :
    (dword (XBinOp.eval .punpckldq ((0 : BitVec 64) ++ v) ((0 : BitVec 64) ++ v)) 0).toNat = (v.extractLsb' 0 32).toNat := by
  rw [punpckldq_eq, dword_ofDwords_0, dword_movq_0]

theorem dword_unpack_2 (v : BitVec 64) :
    (dword (XBinOp.eval .punpckldq ((0 : BitVec 64) ++ v) ((0 : BitVec 64) ++ v)) 2).toNat = (v.extractLsb' 32 32).toNat := by
  rw [punpckldq_eq, dword_ofDwords_2, dword_movq_1]

/-- The two products of `pairMul`, for `esi` at `x` and `edi` at `y`. -/
theorem pair_sums {s t : State} {S H : Nat} (hs : Sums (s.xmm .xmm0) (s.xmm .xmm1) S H)
    (hH : H + 2 ^ 32 < 2 ^ 64) {x y : Addr}
    (h0 : t.xmm .xmm0 = XBinOp.eval .paddq (s.xmm .xmm0)
      (pmuludq (XBinOp.eval .punpckldq ((0 : BitVec 64) ++ s.mem.readW x 64) ((0 : BitVec 64) ++ s.mem.readW x 64))
        (XBinOp.eval .punpckldq ((0 : BitVec 64) ++ s.mem.readW y 64) ((0 : BitVec 64) ++ s.mem.readW y 64))))
    (h1 : t.xmm .xmm1 = XBinOp.eval .paddq (s.xmm .xmm1) (XShiftOp.eval .psrlq
      (pmuludq (XBinOp.eval .punpckldq ((0 : BitVec 64) ++ s.mem.readW x 64) ((0 : BitVec 64) ++ s.mem.readW x 64))
        (XBinOp.eval .punpckldq ((0 : BitVec 64) ++ s.mem.readW y 64) ((0 : BitVec 64) ++ s.mem.readW y 64))) 32)) :
    Sums (t.xmm .xmm0) (t.xmm .xmm1) (S + pw s.mem x y + pw s.mem (x + 4) (y + 4))
      (H + pw s.mem x y / 2 ^ 32 + pw s.mem (x + 4) (y + 4) / 2 ^ 32) := by
  have a := hs.addMul (u := XBinOp.eval .punpckldq ((0 : BitVec 64) ++ s.mem.readW x 64) ((0 : BitVec 64) ++ s.mem.readW x 64))
    (v := XBinOp.eval .punpckldq ((0 : BitVec 64) ++ s.mem.readW y 64) ((0 : BitVec 64) ++ s.mem.readW y 64)) hH
  rw [h0, h1]
  simp only [dword_unpack_0, dword_unpack_2, readW64_lo, readW64_hi] at a
  exact a

/-! ## `single` -/

/-- The product of `single`: the words `x` and `y` in doublewords 0. -/
def singleP (x y : BitVec 32) : BitVec 128 :=
  pmuludq ((0 : BitVec 96) ++ x) ((0 : BitVec 96) ++ y)

theorem singleP_0 (x y : BitVec 32) : qword (singleP x y) 0 = BitVec.ofNat 64 (x.toNat * y.toNat) := by
  rw [singleP, qword_pmuludq_0, dword_movd_0, dword_movd_0, mul_setWidth]

theorem singleP_1 (x y : BitVec 32) : qword (singleP x y) 1 = BitVec.ofNat 64 0 := by
  rw [singleP, qword_pmuludq_1, dword_movd_2, dword_movd_2]; rfl

theorem single_run (s : State) (hm : 0 < s.mcdt)
    (h1 : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi 0)) 4) (h2 : InRegions (s.rd ++ s.wr) (s.ea (at_ .edi 0)) 4) :
    ∃ t, runBlock isa single s = some t ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mcdt = s.mcdt ∧
      (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧
      t.xmm .xmm6 = s.xmm .xmm6 ∧
      t.xmm .xmm0 = XBinOp.eval .paddq (s.xmm .xmm0)
        (singleP (s.mem.readW (s.ea (at_ .esi 0)) 32) (s.mem.readW (s.ea (at_ .edi 0)) 32)) ∧
      t.xmm .xmm1 = XBinOp.eval .paddq (s.xmm .xmm1) (XShiftOp.eval .psrlq
        (singleP (s.mem.readW (s.ea (at_ .esi 0)) 32) (s.mem.readW (s.ea (at_ .edi 0)) 32)) 32) := by
  have ea2 : ∀ v : BitVec 32, (s.setReg .eax v).ea (at_ .edi 0) = s.ea (at_ .edi 0) := fun _ => rfl
  have ea2' : ∀ (v : BitVec 32) (x : BitVec 128),
      ((s.setReg .eax v).setXmm .xmm7 x).ea (at_ .edi 0) = s.ea (at_ .edi 0) := fun _ _ => rfl
  simp only [single, acc, List.cons_append, List.nil_append, runBlock_cons, reduceExec, readSrc, State.load32, h1,
    Option.map_some, runStep_some, XOp.exec, ↓reduceIte, Option.some.injEq, exists_eq_left',
    rd_setXmm, wr_setXmm, mem_setXmm, rd_setReg, wr_setReg, mem_setReg, ea2', h2, mcdt_setXmm, mcdt_setReg, hm,
    xmm_setXmm, xmm_setReg, reduceCtorEq, runBlock_nil, gpr_setXmm, gpr_setReg_self]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, trivial, rfl, rfl⟩
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

end

end


/-! # The products of a column: `dot`

`dot` adds `Σ X_j Y_j` over `j < n` to the sums (`Sums`), for numbers `X`
and `Y` at offsets `x` and `y` of the working space (`dsum`): four products
at a time while a fifth word follows (`quadBody`), then four (`quadLast`),
two (`pair`) and one (`single`), counted down by `ebp`, the bytes left.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.RegUpd VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.X86.Wp

/-! ## Sums of products -/

/-- `Σ f (a + j)` for `j < n`. -/
def rsum (f : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rsum f a n + f (a + n)

/-- The product of the words `j` of the numbers at offsets `x` and `y`. -/
def dprod (m : Mem) (W : Addr) (x y j : Nat) : Nat := w32 m W (x + 4 * j) * w32 m W (y + 4 * j)

/-- The products' sum and their high words' sum, over `j < n`. -/
def dsum (m : Mem) (W : Addr) (x y n : Nat) : Nat := rsum (dprod m W x y) 0 n
def dhigh (m : Mem) (W : Addr) (x y n : Nat) : Nat := rsum (fun j => dprod m W x y j / 2 ^ 32) 0 n

theorem dprod_lt (m : Mem) (W : Addr) (x y j : Nat) : dprod m W x y j < 2 ^ 64 := by
  have := word_mul_lt (m.readW (off W (x + 4 * j)) 32) (m.readW (off W (y + 4 * j)) 32)
  simpa [dprod, w32] using this

theorem dprod_div_lt (m : Mem) (W : Addr) (x y j : Nat) : dprod m W x y j / 2 ^ 32 < 2 ^ 32 :=
  (Nat.div_lt_iff_lt_mul (by decide)).2 (by have := dprod_lt m W x y j; omega_arith)

theorem dhigh_le (m : Mem) (W : Addr) (x y n : Nat) : dhigh m W x y n ≤ n * (2 ^ 32 - 1) := by
  induction n with
  | zero => simp [dhigh, rsum]
  | succ n ih =>
    have := dprod_div_lt m W x y n
    simp only [dhigh, rsum, Nat.zero_add] at ih ⊢
    rw [Nat.succ_mul]; omega_arith

theorem dsum_succ (m : Mem) (W : Addr) (x y n : Nat) :
    dsum m W x y (n + 1) = dsum m W x y n + dprod m W x y n := by
  simp only [dsum, rsum, Nat.zero_add]

theorem dhigh_succ (m : Mem) (W : Addr) (x y n : Nat) :
    dhigh m W x y (n + 1) = dhigh m W x y n + dprod m W x y n / 2 ^ 32 := by
  simp only [dhigh, rsum, Nat.zero_add]

/-- The address `d` bytes past `off W a`. -/
theorem off_plus (W : Addr) (a d : Nat) : off W a + BitVec.ofNat 64 d = off W (a + d) := by
  rw [off, off, BitVec.ofNat_add, BitVec.add_assoc]

theorem off_4 (W : Addr) (a : Nat) : off W a + 4 = off W (a + 4) := off_plus W a 4
theorem off_8 (W : Addr) (a : Nat) : off W a + 8 = off W (a + 8) := off_plus W a 8
theorem off_12 (W : Addr) (a : Nat) : off W a + 12 = off W (a + 12) := off_plus W a 12

theorem pw_d0 (m : Mem) (W : Addr) (x y j : Nat) :
    pw m (off W (x + 4 * j)) (off W (y + 4 * j)) = dprod m W x y j := rfl

theorem pw_d (m : Mem) (W : Addr) (x y j d k : Nat) (hk : 4 * k = 4 * j + d) :
    pw m (off W (x + 4 * j + d)) (off W (y + 4 * j + d)) = dprod m W x y k := by
  simp only [pw, dprod, w32]
  rw [show x + 4 * j + d = x + 4 * k by omega_arith, show y + 4 * j + d = y + 4 * k by omega_arith]

/-! ## Scalar instructions, keeping `mcdt` and the XMM registers -/

section
variable {s : State} {is : List Instr} {Q : State → Prop}

theorem wp_addX {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (s.gpr d + v) → t.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)) →
      t.mcdt = s.mcdt → t.xmm = s.xmm → WP isa (.block is) t Q) :
    WP isa (.block (.alu .add d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl rfl rfl)

theorem wp_subX {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (s.gpr d - v) → t.cf = some (decide ((s.gpr d).toNat < v.toNat)) →
      t.mcdt = s.mcdt → t.xmm = s.xmm → WP isa (.block is) t Q) :
    WP isa (.block (.alu .sub d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl rfl rfl)

theorem wp_cmpX {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Fupd s t → t.cf = some (decide ((s.gpr d).toNat < v.toNat)) → t.zf = some (s.gpr d - v == 0) →
      t.mcdt = s.mcdt → t.xmm = s.xmm → WP isa (.block is) t Q) :
    WP isa (.block (.alu .cmp d src :: is)) s Q :=
  cons (s' := arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat)) (subOverflow (s.gpr d) v (s.gpr d - v)))
    (by simp only [exec, execAlu, h, Option.bind_some]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl)

theorem wp_movX {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d v → t.mcdt = s.mcdt → t.xmm = s.xmm → WP isa (.block is) t Q) :
    WP isa (.block (.mov d src :: is)) s Q :=
  cons (s' := s.setReg d v) (by simp only [exec, h, Option.map_some]) (k _ (Upd.setReg _ _ _) rfl rfl)

end

/-! ## The loop's invariant -/

/-- After the products `j' < j` (from the state `s0` before them): the
pointers, the count `4 (n - j)`, the sums, and what stays. -/
structure DotI (s0 : State) (W : Addr) (L x y n S H j : Nat) (t : State) : Prop where
  hi : j ≤ n
  ws : Ws t W L
  esi : PtrAt t W .esi (x + 4 * j)
  edi : PtrAt t W .edi (y + 4 * j)
  cnt : t.gpr .ebp = BitVec.ofNat 32 (4 * (n - j))
  sums : Sums (t.xmm .xmm0) (t.xmm .xmm1) (S + dsum s0.mem W x y j) (H + dhigh s0.mem W x y j)
  keep : Keeps [.eax, .esi, .edi, .ebp] s0 t
  mem : t.mem = s0.mem
  mcdt : t.mcdt = s0.mcdt
  x6 : t.xmm .xmm6 = s0.xmm .xmm6
  x7 : t.xmm .xmm7 = s0.xmm .xmm7

/-- What the products need: both numbers' `n` words within the working space
(if there are any),
room for the high sums, `pmuludq` allowed, and counts below `2³²`. -/
structure DotEnv (s0 : State) (L x y n H : Nat) : Prop where
  xr : n = 0 ∨ x + 4 * n ≤ L
  yr : n = 0 ∨ y + 4 * n ≤ L
  hH : H + (n + 4) * 2 ^ 32 < 2 ^ 64
  hn : 4 * n < 2 ^ 32
  mcdt : 0 < s0.mcdt

theorem Sums.of_eq {x0 x1 : BitVec 128} {S H S' H' : Nat} (h : Sums x0 x1 S H) (hs : S = S') (hh : H = H') :
    Sums x0 x1 S' H' := hs ▸ hh ▸ h

/-- The pointers' advance and the count's, then a comparison of the count. -/
theorem wp_advCmp {s : State} {d c : BitVec 32} {Q : State → Prop}
    (k : ∀ t, t.gpr .esi = s.gpr .esi + d → t.gpr .edi = s.gpr .edi + d → t.gpr .ebp = s.gpr .ebp - d →
      (∀ r, r ≠ .esi → r ≠ .edi → r ≠ .ebp → t.gpr r = s.gpr r) →
      t.cf = some (decide ((s.gpr .ebp - d).toNat < c.toNat)) → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr →
      t.mcdt = s.mcdt → t.xmm = s.xmm → Q t) :
    WP isa (.block [.alu .add .esi (.imm d), .alu .add .edi (.imm d), .alu .sub .ebp (.imm d),
      .alu .cmp .ebp (.imm c)]) s Q := by
  refine WP.of_runBlock ?_
  simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left']
  refine k _ ?_ ?_ ?_ (fun r h1 h2 h3 => ?_) ?_ rfl rfl rfl rfl rfl
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [gpr_arithFlags, gpr_setReg, h1, h2, h3, ↓reduceIte]
  · simp only [cf_arithFlags, gpr_setReg, gpr_arithFlags, ↓reduceIte]; rfl

/-- The pointers' advance and the count's. -/
theorem wp_adv {s : State} {d : BitVec 32} {Q : State → Prop}
    (k : ∀ t, t.gpr .esi = s.gpr .esi + d → t.gpr .edi = s.gpr .edi + d → t.gpr .ebp = s.gpr .ebp - d →
      (∀ r, r ≠ .esi → r ≠ .edi → r ≠ .ebp → t.gpr r = s.gpr r) → t.mem = s.mem → t.rd = s.rd →
      t.wr = s.wr → t.mcdt = s.mcdt → t.xmm = s.xmm → Q t) :
    WP isa (.block [.alu .add .esi (.imm d), .alu .add .edi (.imm d), .alu .sub .ebp (.imm d)]) s Q := by
  refine WP.of_runBlock ?_
  simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left']
  refine k _ ?_ ?_ ?_ (fun r h1 h2 h3 => ?_) rfl rfl rfl rfl rfl
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [gpr_arithFlags, gpr_setReg, h1, h2, h3, ↓reduceIte]

theorem dsum_add (m : Mem) (W : Addr) (x y j i : Nat) :
    dsum m W x y (j + i) = dsum m W x y j + rsum (dprod m W x y) j i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [← Nat.add_assoc, dsum_succ, ih]; simp only [rsum]; omega_arith

theorem dhigh_add (m : Mem) (W : Addr) (x y j i : Nat) :
    dhigh m W x y (j + i) = dhigh m W x y j + rsum (fun k => dprod m W x y k / 2 ^ 32) j i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [← Nat.add_assoc, dhigh_succ, ih]; simp only [rsum]; omega_arith

/-- The invariant after `i` more products, from the sums they add. -/
theorem DotI.step {s0 t u : State} {W : Addr} {L x y n S H j : Nat} (I : DotI s0 W L x y n S H j t) (i : Nat)
    (hi : j + i ≤ n) (ws : Ws u W L)
    (esi : (u.gpr .esi).toNat = (t.gpr .esi + BitVec.ofNat 32 (4 * i)).toNat)
    (edi : (u.gpr .edi).toNat = (t.gpr .edi + BitVec.ofNat 32 (4 * i)).toNat)
    (cnt : u.gpr .ebp = t.gpr .ebp - BitVec.ofNat 32 (4 * i)) (h4 : 4 * n < 2 ^ 32)
    (sums : Sums (u.xmm .xmm0) (u.xmm .xmm1) (S + dsum s0.mem W x y j + rsum (dprod s0.mem W x y) j i)
      (H + dhigh s0.mem W x y j + rsum (fun k => dprod s0.mem W x y k / 2 ^ 32) j i))
    (keep : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .edi → r ≠ .ebp → u.gpr r = t.gpr r) (rd : u.rd = t.rd)
    (wr : u.wr = t.wr) (mem : u.mem = t.mem) (mcdt : u.mcdt = t.mcdt) (x6 : u.xmm .xmm6 = t.xmm .xmm6)
    (x7 : u.xmm .xmm7 = t.xmm .xmm7) : DotI s0 W L x y n S H (j + i) u := by
  have hn := I.ws.nowrap
  refine ⟨hi, ws, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, by rw [rd, I.keep.2.1], by rw [wr, I.keep.2.2]⟩,
    by rw [mem, I.mem], by rw [mcdt, I.mcdt], by rw [x6, I.x6], by rw [x7, I.x7]⟩
  · rw [PtrAt, esi, ptr_add I.esi, toNat_ofNat_lt (by omega_arith)]; omega_arith
  · rw [PtrAt, edi, ptr_add I.edi, toNat_ofNat_lt (by omega_arith)]; omega_arith
  · rw [cnt, I.cnt, sub_ofNat (by omega_arith)]; congr 1; omega_arith
  · refine sums.of_eq ?_ ?_
    · rw [dsum_add]; omega_arith
    · rw [dhigh_add]; omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [keep r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2]; exact I.keep.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])

theorem rsum_four (f : Nat → Nat) (j : Nat) : rsum f j 4 = f j + f (j + 1) + f (j + 2) + f (j + 3) := by
  simp only [rsum, Nat.add_zero, Nat.zero_add]

theorem rsum_two (f : Nat → Nat) (j : Nat) : rsum f j 2 = f j + f (j + 1) := by
  simp only [rsum, Nat.add_zero, Nat.zero_add]

/-- The addresses of a number's word `j`, `d` bytes on. -/
theorem ea_w {t : State} {W : Addr} {L : Nat} (hw : Ws t W L) {r : Reg} {x j : Nat} (hp : PtrAt t W r (x + 4 * j))
    {d : Nat} (hd : x + 4 * j + d < L) : t.ea (at_ r d) = off W (x + 4 * j + d) := ea_ptr hw hp hd

/-- Four products, the loop's body, while a fifth word follows. -/
theorem quad_ok {s0 t : State} {W : Addr} {L x y n S H j : Nat} (E : DotEnv s0 L x y n H)
    (I : DotI s0 W L x y n S H j t) (hj : j + 5 ≤ n) :
    WP isa (.block quadBody) t fun u =>
      DotI s0 W L x y n S H (j + 4) u ∧ u.cf = some (decide (4 * (n - (j + 4)) < 20)) := by
  have xr := E.xr.resolve_left (by omega_arith)
  have yr := E.yr.resolve_left (by omega_arith)
  have hm : 0 < t.mcdt := I.mcdt ▸ E.mcdt
  have ex0 := ea_w I.ws I.esi (d := 0) (by omega_arith)
  have ey0 := ea_w I.ws I.edi (d := 0) (by omega_arith)
  rw [quadBody]
  obtain ⟨t1, run1, o1, a1, b1⟩ := quadLastMul_run t hm
    (by rw [ex0]; exact ws_read I.ws (by omega_arith)) (by rw [ey0]; exact ws_read I.ws (by omega_arith))
  refine WP.block_append (WP.of_runBlock ⟨t1, run1, ?_⟩)
  refine wp_advCmp fun u esi edi ebp oth cf mem rd wr mcdt xmm => ?_
  have hl := dhigh_le s0.mem W x y j
  have hH := E.hH
  have s1 := quadLast_sums I.sums (by omega_arith) a1 b1
  rw [ex0, ey0, Nat.add_zero, Nat.add_zero, off_4, off_4, off_8, off_8, off_12, off_12, I.mem, pw_d0,
    pw_d _ _ _ _ _ 8 (j + 2) (by omega_arith), pw_d _ _ _ _ _ 4 (j + 1) (by omega_arith),
    pw_d _ _ _ _ _ 12 (j + 3) (by omega_arith)] at s1
  have I' := I.step 4 (by omega_arith) (I.ws.of_wr (by rw [wr, o1.wr])) (by rw [esi, o1.gpr]; rfl) (by rw [edi, o1.gpr]; rfl)
    (by rw [ebp, o1.gpr]; rfl) E.hn (by rw [xmm, rsum_four, rsum_four]; refine s1.of_eq ?_ ?_ <;> omega_arith)
    (fun r h0 h1 h2 h3 => by rw [oth r h1 h2 h3, o1.gpr]) (by rw [rd, o1.rd]) (by rw [wr, o1.wr])
    (by rw [mem, o1.mem]) (by rw [mcdt, o1.mcdt]) (by rw [xmm, o1.x6]) (by rw [xmm, o1.x7])
  refine ⟨I', ?_⟩
  rw [cf, ← ebp, I'.cnt, toNat_ofNat_lt (by have := E.hn; omega_arith)]; rfl

/-- The last four products. -/
theorem quadLast_ok {s0 t : State} {W : Addr} {L x y n S H j : Nat} (E : DotEnv s0 L x y n H)
    (I : DotI s0 W L x y n S H j t) (hj : j + 4 ≤ n) :
    WP isa (.block quadLast) t (DotI s0 W L x y n S H (j + 4)) := by
  have xr := E.xr.resolve_left (by omega_arith)
  have yr := E.yr.resolve_left (by omega_arith)
  have hm : 0 < t.mcdt := I.mcdt ▸ E.mcdt
  have ex0 := ea_w I.ws I.esi (d := 0) (by omega_arith)
  have ey0 := ea_w I.ws I.edi (d := 0) (by omega_arith)
  rw [quadLast]
  obtain ⟨t1, run1, o1, a1, b1⟩ := quadLastMul_run t hm
    (by rw [ex0]; exact ws_read I.ws (by omega_arith)) (by rw [ey0]; exact ws_read I.ws (by omega_arith))
  refine WP.block_append (WP.of_runBlock ⟨t1, run1, ?_⟩)
  refine wp_adv fun u esi edi ebp oth mem rd wr mcdt xmm => ?_
  have hl := dhigh_le s0.mem W x y j
  have hH := E.hH
  have s1 := quadLast_sums I.sums (by omega_arith) a1 b1
  rw [ex0, ey0, Nat.add_zero, Nat.add_zero, off_8, off_8, off_4, off_4, off_12, off_12, I.mem, pw_d0,
    pw_d _ _ _ _ _ 8 (j + 2) (by omega_arith), pw_d _ _ _ _ _ 4 (j + 1) (by omega_arith),
    pw_d _ _ _ _ _ 12 (j + 3) (by omega_arith)] at s1
  exact I.step 4 (by omega_arith) (I.ws.of_wr (by rw [wr, o1.wr])) (by rw [esi, o1.gpr]; rfl) (by rw [edi, o1.gpr]; rfl)
    (by rw [ebp, o1.gpr]; rfl) E.hn (by rw [xmm, rsum_four, rsum_four]; refine s1.of_eq ?_ ?_ <;> omega_arith)
    (fun r h0 h1 h2 h3 => by rw [oth r h1 h2 h3, o1.gpr]) (by rw [rd, o1.rd]) (by rw [wr, o1.wr])
    (by rw [mem, o1.mem]) (by rw [mcdt, o1.mcdt]) (by rw [xmm, o1.x6]) (by rw [xmm, o1.x7])

/-- Two products. -/
theorem twin_ok {s0 t : State} {W : Addr} {L x y n S H j : Nat} (E : DotEnv s0 L x y n H)
    (I : DotI s0 W L x y n S H j t) (hj : j + 2 ≤ n) :
    WP isa (.block pair) t (DotI s0 W L x y n S H (j + 2)) := by
  have xr := E.xr.resolve_left (by omega_arith)
  have yr := E.yr.resolve_left (by omega_arith)
  have hm : 0 < t.mcdt := I.mcdt ▸ E.mcdt
  have ex0 := ea_w I.ws I.esi (d := 0) (by omega_arith)
  have ey0 := ea_w I.ws I.edi (d := 0) (by omega_arith)
  rw [pair]
  obtain ⟨t1, run1, o1, a1, b1⟩ := pairMul_run t hm
    (by rw [ex0]; exact ws_read I.ws (by omega_arith)) (by rw [ey0]; exact ws_read I.ws (by omega_arith))
  refine WP.block_append (WP.of_runBlock ⟨t1, run1, ?_⟩)
  refine wp_adv fun u esi edi ebp oth mem rd wr mcdt xmm => ?_
  have hl := dhigh_le s0.mem W x y j
  have hH := E.hH
  have s1 := pair_sums I.sums (by omega_arith) a1 b1
  rw [ex0, ey0, Nat.add_zero, Nat.add_zero, off_4, off_4, I.mem, pw_d0,
    pw_d _ _ _ _ _ 4 (j + 1) (by omega_arith)] at s1
  exact I.step 2 (by omega_arith) (I.ws.of_wr (by rw [wr, o1.wr])) (by rw [esi, o1.gpr]; rfl) (by rw [edi, o1.gpr]; rfl)
    (by rw [ebp, o1.gpr]; rfl) E.hn (by rw [xmm, rsum_two, rsum_two]; refine s1.of_eq ?_ ?_ <;> omega_arith)
    (fun r h0 h1 h2 h3 => by rw [oth r h1 h2 h3, o1.gpr]) (by rw [rd, o1.rd]) (by rw [wr, o1.wr])
    (by rw [mem, o1.mem]) (by rw [mcdt, o1.mcdt]) (by rw [xmm, o1.x6]) (by rw [xmm, o1.x7])

/-- What `dot` leaves: the sums of the products `j < n`, and what stays. -/
structure DotPost (s0 : State) (W : Addr) (x y n S H : Nat) (u : State) : Prop where
  sums : Sums (u.xmm .xmm0) (u.xmm .xmm1) (S + dsum s0.mem W x y n) (H + dhigh s0.mem W x y n)
  keep : Keeps [.eax, .esi, .edi, .ebp] s0 u
  mem : u.mem = s0.mem
  mcdt : u.mcdt = s0.mcdt
  x6 : u.xmm .xmm6 = s0.xmm .xmm6
  x7 : u.xmm .xmm7 = s0.xmm .xmm7

/-- The last product. -/
theorem one_ok {s0 t : State} {W : Addr} {L x y n S H j : Nat} (E : DotEnv s0 L x y n H)
    (I : DotI s0 W L x y n S H j t) (hj : j + 1 = n) :
    WP isa (.block single) t (DotPost s0 W x y n S H) := by
  have xr := E.xr.resolve_left (by omega_arith)
  have yr := E.yr.resolve_left (by omega_arith)
  have hm : 0 < t.mcdt := I.mcdt ▸ E.mcdt
  have ex0 := ea_w I.ws I.esi (d := 0) (by omega_arith)
  have ey0 := ea_w I.ws I.edi (d := 0) (by omega_arith)
  obtain ⟨u, run, mu, rdu, wru, mcu, gu, u6, u7, a, b⟩ :=
    single_run t hm (by rw [ex0]; exact ws_read I.ws (by omega_arith)) (by rw [ey0]; exact ws_read I.ws (by omega_arith))
  refine WP.of_runBlock ⟨u, run, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have hl := dhigh_le s0.mem W x y j
    have hH := E.hH
    have s1 := single_sums I.sums (by omega_arith) a b
    rw [ex0, ey0, I.mem] at s1
    refine s1.of_eq ?_ ?_
    · rw [← hj, dsum_succ, ← Nat.add_assoc]; simp only [dprod, w32, Nat.add_zero]
    · rw [← hj, dhigh_succ, ← Nat.add_assoc]; simp only [dprod, w32, Nat.add_zero]
  · rw [gu r (by intro h; simp [h] at hr)]; exact I.keep.1 r hr
  · rw [rdu]; exact I.keep.2.1
  · rw [wru]; exact I.keep.2.2
  · rw [mu, I.mem]
  · rw [mcu, I.mcdt]
  · rw [u6, I.x6]
  · rw [u7, I.x7]

theorem DotI.done {s0 t : State} {W : Addr} {L x y n S H : Nat} (I : DotI s0 W L x y n S H n t) :
    DotPost s0 W x y n S H t := ⟨I.sums, I.keep, I.mem, I.mcdt, I.x6, I.x7⟩

/-- The invariant through an instruction that changes only flags. -/
theorem DotI.of_same {s0 t t' : State} {W : Addr} {L x y n S H j : Nat} (I : DotI s0 W L x y n S H j t)
    (hg : t'.gpr = t.gpr) (hm : t'.mem = t.mem) (hr : t'.rd = t.rd) (hw : t'.wr = t.wr) (hc : t'.mcdt = t.mcdt)
    (hx : t'.xmm = t.xmm) : DotI s0 W L x y n S H j t' := by
  refine ⟨I.hi, I.ws.of_wr hw, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [PtrAt, hg]; exact I.esi
  · rw [PtrAt, hg]; exact I.edi
  · rw [hg]; exact I.cnt
  · rw [hx]; exact I.sums
  · rw [hg]; exact I.keep.1 r hr
  · rw [hr]; exact I.keep.2.1
  · rw [hw]; exact I.keep.2.2
  · rw [hm]; exact I.mem
  · rw [hc]; exact I.mcdt
  · rw [hx]; exact I.x6
  · rw [hx]; exact I.x7

/-- `cmp ebp, c` on the invariant: CF is `4 (n - j) < c`. -/
theorem wp_cmpCnt {s0 t : State} {W : Addr} {L x y n S H j : Nat} (I : DotI s0 W L x y n S H j t) (hn : 4 * n < 2 ^ 32)
    {c : Nat} (hc : c < 2 ^ 32) {rest : List Instr} {Q : State → Prop}
    (k : ∀ u, DotI s0 W L x y n S H j u → isa.eval .ae u = some (!decide (4 * (n - j) < c)) →
      WP isa (.block rest) u Q) :
    WP isa (.block (.alu .cmp .ebp (.imm (BitVec.ofNat 32 c)) :: rest)) t Q :=
  wp_cmpX rfl fun u f c1 _ m1 x1 => k u (I.of_same f.gpr f.mem f.rd f.wr m1 x1) (by
    show u.cf.map _ = _
    rw [c1, I.cnt, toNat_ofNat_lt (by omega_arith), toNat_ofNat_lt hc]; rfl)

theorem eval_b_of_ae {u : State} {b : Bool} (h : isa.eval .ae u = some (!b)) : isa.eval .b u = some b := by
  change u.cf.map (!·) = some (!b) at h
  show u.cf = some b
  cases hc : u.cf with
  | none => rw [hc] at h; cases h
  | some v => rw [hc, Option.map_some, Option.some.injEq] at h; rw [Bool.not_inj h]

/-- Four products at a time while at least five words remain. -/
theorem quads_ok {s0 t : State} {W : Addr} {L x y n S H j : Nat} (E : DotEnv s0 L x y n H)
    (I : DotI s0 W L x y n S H j t) (hc : isa.eval .ae t = some (!decide (4 * (n - j) < 20))) :
    WP isa (.ite .ae (.loop (.block quadBody) .ae) (.block [])) t
      fun u => ∃ j, DotI s0 W L x y n S H j u ∧ n < j + 5 := by
  have hi := I.hi
  by_cases h5 : n < j + 5
  · exact WP.ite false (by rw [hc, decide_eq_true (by omega_arith)]; rfl)
      (fun h => absurd h (by decide)) fun _ => WP.block_nil ⟨j, I, h5⟩
  refine WP.ite true (by rw [hc, decide_eq_false (by omega_arith)]; rfl) (fun _ => ?_)
    (fun h => absurd h (by decide))
  refine WP.loop (M := isa) (fun m u => ∃ j, m = n - j ∧ j + 5 ≤ n ∧ DotI s0 W L x y n S H j u) ?_ (n - j) t
    ⟨j, rfl, by omega_arith, I⟩
  rintro m u ⟨j, rfl, hj, J⟩
  refine WP.mono (quad_ok E J hj) fun v ⟨J', cv⟩ => ?_
  have hv : isa.eval .ae v = some (!decide (4 * (n - (j + 4)) < 20)) := by
    show v.cf.map _ = _; rw [cv]; rfl
  by_cases h : n < j + 4 + 5
  · exact .inl ⟨by rw [hv, decide_eq_true (by omega_arith)]; rfl, j + 4, J', h⟩
  · exact .inr ⟨by rw [hv, decide_eq_false (by omega_arith)]; rfl, n - (j + 4), by omega_arith, j + 4, rfl, by omega_arith, J'⟩

/-- `dot`: the products `X_j Y_j`, `j < n`, added to the sums, for
`esi = W + x`, `edi = W + y` and `ebp = 4 n`. -/
theorem dot_ok {s0 : State} {W : Addr} {L x y n S H : Nat} (E : DotEnv s0 L x y n H) (hw : Ws s0 W L)
    (hx : PtrAt s0 W .esi x) (hy : PtrAt s0 W .edi y) (hbp : s0.gpr .ebp = BitVec.ofNat 32 (4 * n))
    (hs : Sums (s0.xmm .xmm0) (s0.xmm .xmm1) S H) :
    WP isa dot s0 (DotPost s0 W x y n S H) := by
  have hn := E.hn
  have I0 : DotI s0 W L x y n S H 0 s0 := ⟨Nat.zero_le _, hw, by simpa using hx, by simpa using hy,
    by simpa using hbp, by simpa [dsum, dhigh, rsum] using hs, Keeps.refl _ _, rfl, rfl, rfl, rfl⟩
  simp only [dot, seqs]
  refine WP.seq (wp_cmpCnt I0 hn (c := 20) (by decide) fun t1 I1 c1 => WP.block_nil ?_)
  refine WP.seq (WP.mono (quads_ok E I1 c1) fun t2 ⟨j, I2, h2⟩ => ?_)
  refine WP.seq (wp_cmpCnt I2 hn (c := 16) (by decide) fun t3 I3 c3 => WP.block_nil ?_)
  refine WP.seq (WP.mono (Q := fun u => ∃ j, DotI s0 W L x y n S H j u ∧ n < j + 4) ?_
    fun t4 ⟨j, I4, h4⟩ => ?_)
  · by_cases h4 : n < j + 4
    · exact WP.ite true (by rw [eval_b_of_ae c3, decide_eq_true (by omega_arith)])
        (fun _ => WP.block_nil ⟨j, I3, h4⟩) (fun h => absurd h (by decide))
    · exact WP.ite false (by rw [eval_b_of_ae c3, decide_eq_false (by omega_arith)]) (fun h => absurd h (by decide))
        (fun _ => WP.mono (quadLast_ok E I3 (by omega_arith)) fun u J => ⟨j + 4, J, by have := I3.hi; omega_arith⟩)
  refine WP.seq (wp_cmpCnt I4 hn (c := 8) (by decide) fun t5 I5 c5 => WP.block_nil ?_)
  refine WP.seq (WP.mono (Q := fun u => ∃ j, DotI s0 W L x y n S H j u ∧ n < j + 2) ?_ fun t6 ⟨j, I6, h6⟩ => ?_)
  · by_cases h2 : n < j + 2
    · exact WP.ite false (by rw [c5, decide_eq_true (by omega_arith)]; rfl) (fun h => absurd h (by decide))
        fun _ => WP.block_nil ⟨j, I5, h2⟩
    · exact WP.ite true (by rw [c5, decide_eq_false (by omega_arith)]; rfl)
        (fun _ => WP.mono (twin_ok E I5 (by omega_arith)) fun u J => ⟨j + 2, J, by have := I5.hi; omega_arith⟩)
        (fun h => absurd h (by decide))
  refine WP.seq (wp_cmpCnt I6 hn (c := 4) (by decide) fun t7 I7 c7 => WP.block_nil ?_)
  have := I7.hi
  by_cases h1 : n = j
  · subst h1
    exact WP.ite false (by rw [c7, decide_eq_true (by omega_arith)]; rfl) (fun h => absurd h (by decide))
      fun _ => WP.block_nil I7.done
  · exact WP.ite true (by rw [c7, decide_eq_false (by omega_arith)]; rfl) (fun _ => one_ok E I7 (by omega_arith))
      (fun h => absurd h (by decide))

end VG.Proof.Mont.X86.Sse2
