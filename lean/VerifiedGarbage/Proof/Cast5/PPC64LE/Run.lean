module

public import VerifiedGarbage.Impl.Cast5.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-!
# CAST5 on PPC64LE: running blocks

`c5run [facts]` runs a block of the CAST5 code symbolically (`crun`),
keeping 32-bit loads as `Mem.readW` and byte loads as the byte, as IDEA's
`irun` (`Proof/Idea/PPC64LE/Round.lean`), with the code's register names
unfolded. The code's 32-bit values live in the low words of registers: `lo`
is that word, and the `lo_*` lemmas take it through the operations the code
uses.
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append]
  simp

theorem read_four (m : Mem) (a : Addr) : m.read a 4 = m.readW a 32 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem read_eight (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem write_eight (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem write_four (m : Mem) (a : Addr) (v : BitVec 32) : m.write a 4 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem accReg_0 : accReg 0 = .r18 := rfl
theorem accReg_1 : accReg 1 = .r19 := rfl
theorem accReg_2 : accReg 2 = .r20 := rfl
theorem accReg_3 : accReg 3 = .r21 := rfl
theorem idxReg_0 : idxReg 0 = .r14 := rfl
theorem idxReg_1 : idxReg 1 = .r15 := rfl
theorem idxReg_2 : idxReg 2 = .r16 := rfl
theorem idxReg_3 : idxReg 3 = .r17 := rfl

/-- Steps a block of the CAST5 code. -/
syntax "c5run" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| c5run) => `(tactic| c5run [])
  | `(tactic| c5run [$ls,*]) => `(tactic|
      crun [List.cons_append, List.nil_append, ↓read_one, ↓read_four, ↓read_eight, write_eight,
        write_four, false_implies, zero, tbl, c255, num, ep, tmp, wd, vI, vKr, msk, mov, sch, rnd, dat,
        cnt, wkE, xL, xR, km, left, typ, key, klen, out, wkK, dst, stp, halves, accReg_0, accReg_1, accReg_2, accReg_3,
        idxReg_0, idxReg_1, idxReg_2, idxReg_3, BitVec.or_self, addrX, $ls,*])

/-! ## Low words -/

/-- The low word of a register. -/
abbrev lo (x : BitVec 64) : BitVec 32 := x.setWidth 32

theorem lo_and (x y : BitVec 64) : lo (x &&& y) = lo x &&& lo y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem lo_or (x y : BitVec 64) : lo (x ||| y) = lo x ||| lo y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem lo_xor (x y : BitVec 64) : lo (x ^^^ y) = lo x ^^^ lo y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem lo_add (x y : BitVec 64) : lo (x + y) = lo x + lo y := lo32_add x y

theorem lo_sub (x y : BitVec 64) : lo (x - y) = lo x - lo y := lo32_sub x y

theorem lo_ext (x : BitVec 32) : lo (x.setWidth 64) = x := lo32_ext x

/-! ## The scan's mask -/

/-- The mask of a lookup: all ones iff the index `x` is `j`. -/
theorem mask_eq {x : BitVec 64} (hx : x.toNat < 256) {j : Nat} (hj : j < 256) :
    0#64 - ((x ^^^ BitVec.ofNat 64 j) - 1#64) >>> 63 =
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
    have hs : (z - 1#64) >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow,
        show (1#64).toNat = 1 from rfl, show (0 : BitVec 64).toNat = 0 from rfl]
      omega
    rw [hs]
    rfl

end VG.Proof.Cast5.PPC64LE
