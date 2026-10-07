import VerifiedGarbage.Impl.Weierstrass.X86.Inv
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Divstep.Word32Bits

/-! # Register arithmetic for a 32-bit word divstep -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86

def pairRight (left right odd swap : BitVec 32) : BitVec 32 :=
  right + (((left ^^^ swap) - swap) &&& odd)

theorem pairRegs_ok (s : State) :
    WP isa (.block pairRegs) s fun u =>
      u.gpr .eax = pairRight (s.gpr .ebx) (s.gpr .eax) (s.gpr .ecx) (s.gpr .edx) ∧
      u.gpr .ebx = s.gpr .ebx +
        (pairRight (s.gpr .ebx) (s.gpr .eax) (s.gpr .ecx) (s.gpr .edx) &&& s.gpr .edx) ∧
      Keeps [.eax, .ebx, .ebp] s u ∧ u.mem = s.mem := by
  apply WP.of_runBlock
  simp only [pairRegs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left',
    pairRight]
  refine ⟨trivial, trivial, ⟨?_, rfl, rfl⟩, rfl⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    hr.1, hr.2.1, hr.2.2, ↓reduceIte]

def oddMask (g : BitVec 32) : BitVec 32 := 0 - (g &&& 1)
def swapMask (d g : BitVec 32) : BitVec 32 := ((d >>> 31) - 1) &&& oddMask g
def nextDelta (d g : BitVec 32) : BitVec 32 := ((d ^^^ swapMask d g) - swapMask d g) + 2

theorem maskRegs_ok (s : State) :
    WP isa (.block maskRegs) s fun u =>
      u.gpr .ecx = oddMask (s.gpr .eax) ∧
      u.gpr .edx = swapMask (s.gpr .edx) (s.gpr .eax) ∧
      u.gpr .eax = nextDelta (s.gpr .edx) (s.gpr .eax) ∧
      Keeps [.eax, .ebx, .ecx, .edx] s u ∧ u.mem = s.mem := by
  apply WP.of_runBlock
  simp only [maskRegs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    execShift, Option.bind_some, Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left',
    oddMask, swapMask, nextDelta, and_self, show 1 ≤ (31 : Nat) ∧ 31 ≤ 31 by decide,
    show (31 : Nat) ≠ 1 by decide]
  refine ⟨trivial, trivial, trivial, ⟨?_, rfl, rfl⟩, rfl⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
    hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ↓reduceIte]

end VG.Proof.Weierstrass.X86.Inv
