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
      crun [List.cons_append, List.nil_append, false_implies, tbl, num, ep, tmp, wd, vI, vKr, msk, mov,
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

/-! ## The scan's mask -/

/-- The mask of a lookup: all ones iff the index `x` is `j`. -/
theorem mask_eq {x : BitVec 64} (hx : x.toNat < 256) {j : Nat} (hj : j < 256) :
    ((x ^^^ BitVec.ofNat 64 j) - 1#64).sshiftRight 63 =
      if x = BitVec.ofNat 64 j then BitVec.allOnes 64 else 0 := by
  by_cases h : x = BitVec.ofNat 64 j
  · rw [ite_eq_left h, h, BitVec.xor_self]
    decide
  · rw [ite_eq_right h]
    obtain ⟨z, hz⟩ : ∃ z, x ^^^ BitVec.ofNat 64 j = z := ⟨_, rfl⟩
    have hzl : z.toNat < 256 := by
      rw [← hz, BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact Nat.xor_lt_two_pow (n := 8) hx hj
    have hz0 : z ≠ 0 := fun e => h (by
      rw [e] at hz
      have := congrArg (· ^^^ BitVec.ofNat 64 j) hz
      simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at this
      rw [this]; exact BitVec.eq_of_getLsbD_eq (by simp))
    have hz1 : z.toNat ≠ 0 := fun e => hz0 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    rw [hz]
    have hs : (z - 1#64).toNat < 2 ^ 63 := by
      rw [BitVec.toNat_sub, show (1#64).toNat = 1 from rfl]
      omega
    rw [BitVec.sshiftRight_eq_of_msb_false (BitVec.msb_eq_false_iff_two_mul_lt.mpr (by omega))]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hs

end VG.Proof.Cast5.RISCV64
