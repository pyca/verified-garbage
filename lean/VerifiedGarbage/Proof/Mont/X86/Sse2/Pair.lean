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

/-! # The products of the `pmuludq` kernel

`quadLastMul` (four products), `pairMul` (two) and `single`
(one), stated on the state they leave (`SseOnly`: only `xmm0` to `xmm5`
change, and `eax` for `single`) and on the sums' lanes (`Sums`): the
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
theorem mcdt_setFlags (s : State) (a b c d : Option Bool) : (s.setFlags a b c d).mcdt = s.mcdt := rfl
theorem mcdt_arithFlags (s : State) (x : BitVec 32) (c o : Bool) : (arithFlags s x c o).mcdt = s.mcdt := rfl

/-- Only `xmm0` to `xmm5` changed. -/
structure SseOnly (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  cf : t.cf = s.cf
  zf : t.zf = s.zf
  mcdt : t.mcdt = s.mcdt
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

theorem word_mul_lt (x y : BitVec 32) : x.toNat * y.toNat < 2 ^ 64 := by
  have := Nat.mul_lt_mul'' x.isLt y.isLt; simpa using this

/-- The product of the words at `a` and `b`. -/
def pw (m : Mem) (a b : Addr) : Nat := (m.readW a 32).toNat * (m.readW b 32).toNat

theorem pw_lt (m : Mem) (a b : Addr) : pw m a b < 2 ^ 64 := word_mul_lt _ _

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

theorem add_ofNat_add (a : Addr) (d e : Nat) : a + BitVec.ofNat 64 d + BitVec.ofNat 64 e = a + BitVec.ofNat 64 (d + e) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## `quadLastMul` -/

theorem quadLastMul_run (s : State) (hm : 0 < s.mcdt)
    (h1 : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi 0)) 16) (h2 : InRegions (s.rd ++ s.wr) (s.ea (at_ .edi 0)) 16) :
    ∃ t, runBlock isa quadLastMul s = some t ∧ SseOnly s t ∧
      t.xmm .xmm0 = XBinOp.eval .paddq (XBinOp.eval .paddq (s.xmm .xmm0)
        (pmuludq (s.mem.readW (s.ea (at_ .esi 0)) 128) (s.mem.readW (s.ea (at_ .edi 0)) 128)))
        (pmuludq (shufDwords (s.mem.readW (s.ea (at_ .esi 0)) 128) 0x31)
          (shufDwords (s.mem.readW (s.ea (at_ .edi 0)) 128) 0x31)) ∧
      t.xmm .xmm1 = XBinOp.eval .paddq (XBinOp.eval .paddq (s.xmm .xmm1) (XShiftOp.eval .psrlq
        (pmuludq (s.mem.readW (s.ea (at_ .esi 0)) 128) (s.mem.readW (s.ea (at_ .edi 0)) 128)) 32))
        (XShiftOp.eval .psrlq (pmuludq (shufDwords (s.mem.readW (s.ea (at_ .esi 0)) 128) 0x31)
          (shufDwords (s.mem.readW (s.ea (at_ .edi 0)) 128) 0x31)) 32) := by
  simp only [quadLastMul, acc, List.cons_append, List.nil_append, runBlock_cons, exec, State.load128, h1, h2,
    Option.map_some, runStep_some, XOp.exec, ↓reduceIte, Option.some.injEq, exists_eq_left',
    rd_setXmm, wr_setXmm, mem_setXmm, ea_setXmm, mcdt_setXmm, hm, xmm_setXmm, reduceCtorEq, runBlock_nil]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [xmm_setXmm, reduceCtorEq, ↓reduceIte, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm,
      cf_setXmm, zf_setXmm, mcdt_setXmm]

theorem dword_shuf31_0 (a : BitVec 128) : dword (shufDwords a 0x31) 0 = dword a 1 := by
  rw [dword_shufDwords _ _ (by decide)]; rfl

theorem dword_shuf31_2 (a : BitVec 128) : dword (shufDwords a 0x31) 2 = dword a 3 := by
  rw [dword_shufDwords _ _ (by decide)]; rfl

/-- The four products of `quadLastMul`, for `esi` at `x` and `edi` at `y`. -/
theorem quadLast_sums {s t : State} {S H : Nat} (hs : Sums (s.xmm .xmm0) (s.xmm .xmm1) S H)
    (hH : H + 4 * 2 ^ 32 < 2 ^ 64) {x y : Addr}
    (h0 : t.xmm .xmm0 = XBinOp.eval .paddq (XBinOp.eval .paddq (s.xmm .xmm0)
      (pmuludq (s.mem.readW x 128) (s.mem.readW y 128)))
      (pmuludq (shufDwords (s.mem.readW x 128) 0x31) (shufDwords (s.mem.readW y 128) 0x31)))
    (h1 : t.xmm .xmm1 = XBinOp.eval .paddq (XBinOp.eval .paddq (s.xmm .xmm1) (XShiftOp.eval .psrlq
      (pmuludq (s.mem.readW x 128) (s.mem.readW y 128)) 32))
      (XShiftOp.eval .psrlq (pmuludq (shufDwords (s.mem.readW x 128) 0x31) (shufDwords (s.mem.readW y 128) 0x31)) 32)) :
    Sums (t.xmm .xmm0) (t.xmm .xmm1)
      (S + pw s.mem x y + pw s.mem (x + 8) (y + 8) + pw s.mem (x + 4) (y + 4) + pw s.mem (x + 12) (y + 12))
      (H + pw s.mem x y / 2 ^ 32 + pw s.mem (x + 8) (y + 8) / 2 ^ 32 + pw s.mem (x + 4) (y + 4) / 2 ^ 32 +
        pw s.mem (x + 12) (y + 12) / 2 ^ 32) := by
  have a1 := hs.addMul (u := s.mem.readW x 128) (v := s.mem.readW y 128) (by omega)
  have q0 := Nat.div_lt_iff_lt_mul (k := 2 ^ 32) (x := (dword (s.mem.readW x 128) 0).toNat *
    (dword (s.mem.readW y 128) 0).toNat) (y := 2 ^ 32) (by decide) |>.2 (by have := word_mul_lt (dword (s.mem.readW x 128) 0) (dword (s.mem.readW y 128) 0); omega)
  have q2 := Nat.div_lt_iff_lt_mul (k := 2 ^ 32) (x := (dword (s.mem.readW x 128) 2).toNat *
    (dword (s.mem.readW y 128) 2).toNat) (y := 2 ^ 32) (by decide) |>.2 (by have := word_mul_lt (dword (s.mem.readW x 128) 2) (dword (s.mem.readW y 128) 2); omega)
  have a2 := a1.addMul (u := shufDwords (s.mem.readW x 128) 0x31) (v := shufDwords (s.mem.readW y 128) 0x31) (by omega)
  rw [h0, h1]
  rw [dword_shuf31_0, dword_shuf31_0, dword_shuf31_2, dword_shuf31_2] at a2
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
  simp only [pairMul, acc, List.cons_append, List.nil_append, runBlock_cons, exec, State.load64, h1, h2,
    Option.map_some, runStep_some, XOp.exec, ↓reduceIte, Option.some.injEq, exists_eq_left',
    rd_setXmm, wr_setXmm, mem_setXmm, ea_setXmm, mcdt_setXmm, hm, xmm_setXmm, reduceCtorEq, runBlock_nil]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
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
      t.xmm .xmm6 = s.xmm .xmm6 ∧ t.xmm .xmm7 = s.xmm .xmm7 ∧
      t.xmm .xmm0 = XBinOp.eval .paddq (s.xmm .xmm0)
        (singleP (s.mem.readW (s.ea (at_ .esi 0)) 32) (s.mem.readW (s.ea (at_ .edi 0)) 32)) ∧
      t.xmm .xmm1 = XBinOp.eval .paddq (s.xmm .xmm1) (XShiftOp.eval .psrlq
        (singleP (s.mem.readW (s.ea (at_ .esi 0)) 32) (s.mem.readW (s.ea (at_ .edi 0)) 32)) 32) := by
  have ea2 : ∀ v : BitVec 32, (s.setReg .eax v).ea (at_ .edi 0) = s.ea (at_ .edi 0) := fun _ => rfl
  have ea2' : ∀ (v : BitVec 32) (x : BitVec 128),
      ((s.setReg .eax v).setXmm .xmm2 x).ea (at_ .edi 0) = s.ea (at_ .edi 0) := fun _ _ => rfl
  simp only [single, acc, List.cons_append, List.nil_append, runBlock_cons, exec, readSrc, State.load32, h1,
    Option.map_some, runStep_some, XOp.exec, ↓reduceIte, Option.some.injEq, exists_eq_left',
    rd_setXmm, wr_setXmm, mem_setXmm, rd_setReg, wr_setReg, mem_setReg, ea2', h2, mcdt_setXmm, mcdt_setReg, hm,
    xmm_setXmm, xmm_setReg, reduceCtorEq, runBlock_nil, gpr_setXmm, gpr_setReg_self]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, trivial, trivial, rfl, rfl⟩
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
