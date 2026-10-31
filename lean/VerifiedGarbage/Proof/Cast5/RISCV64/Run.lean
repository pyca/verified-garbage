module

public import VerifiedGarbage.Impl.Cast5.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Run
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
public import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# CAST5 on RISC-V: running blocks

`c5run [facts]` runs a block of the CAST5 code symbolically (`crun`), with
the code's register names unfolded. The code's 32-bit values live in the
low words of registers: `lo` is that word, and the `lo_*` lemmas take it
through the operations the code uses.
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64

open VG VG.RISCV64 VG.Impl.Cast5.RISCV64

theorem accReg_0 : accReg 0 = .s4 := rfl
theorem accReg_1 : accReg 1 = .s5 := rfl
theorem accReg_2 : accReg 2 = .s6 := rfl
theorem accReg_3 : accReg 3 = .s7 := rfl
theorem idxReg_0 : idxReg 0 = .s0 := rfl
theorem idxReg_1 : idxReg 1 = .s1 := rfl
theorem idxReg_2 : idxReg 2 = .s2 := rfl
theorem idxReg_3 : idxReg 3 = .s3 := rfl

theorem read_four (m : Mem) (a : Addr) : m.read a 4 = m.readW a 32 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

/-- Steps a block of the CAST5 code. -/
syntax "c5run" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| c5run) => `(tactic| c5run [])
  | `(tactic| c5run [$ls,*]) => `(tactic|
      crun [List.cons_append, List.nil_append, false_implies, tbl, ep, tmp, wd, vI, vKr, msk, mov,
        sch, rnd, dat, cnt, wkE, xL, xR, km, left, typ, key, klen, out, wkK, dst, stp, hlv, accReg_0,
        accReg_1, accReg_2, accReg_3, idxReg_0, idxReg_1, idxReg_2, idxReg_3, $ls,*])

/-! ## Low words -/

/-- The low word of a register. -/
abbrev lo (x : BitVec 64) : BitVec 32 := x.setWidth 32

theorem lo_and (x y : BitVec 64) : lo (x &&& y) = lo x &&& lo y := lo32_and x y
theorem lo_or (x y : BitVec 64) : lo (x ||| y) = lo x ||| lo y := lo32_or x y
theorem lo_xor (x y : BitVec 64) : lo (x ^^^ y) = lo x ^^^ lo y := lo32_xor x y
theorem lo_add (x y : BitVec 64) : lo (x + y) = lo x + lo y := lo32_add x y
theorem lo_sub (x y : BitVec 64) : lo (x - y) = lo x - lo y := lo32_sub x y
theorem lo_ext (x : BitVec 32) : lo (x.setWidth 64) = x := lo32_ext x
theorem lo_sext (x : BitVec 32) : lo (sext32 x) = x := lo32_sext x

end VG.Proof.Cast5.RISCV64
