module

import VerifiedGarbage.Proof.Ct.RISCV64Scrub
import VerifiedGarbage.Proof.Ct.PPC64LE.Scrub

/-!
# A result register the calling convention forbids is not admitted

Regression tests for #6302: code whose result has the right bits for its
contract, but leaves the rest of the result register other than the calling
convention requires (`Abi.retExt`), does not meet `RetAbi`, which every
artifact proves (`VerifiedScrubbed`). Each is stated of `vg_ct_eq`'s
contract, whose result is a `u32`, from a state its precondition admits (the
one its proof gives, `Verified`'s third part).
-/

namespace VG.Test.RetAbi

/-- RISC-V: `a0 = 0x1_0000_0000`, a `u32` result of 0 with bit 32 set, as in
the issue's reproduction, where the compiled caller read it as unequal-is-equal.
The psABI requires the upper half to copy bit 31 (0). -/
def rvBad : Prog RISCV64.isa := .block [.li .a0 1, .shift .sll .d .a0 .a0 32]

theorem riscv64_upper_half_rejected :
    ¬ RetAbi RISCV64.target rvBad (Spec.Ct.eqContract RISCV64.abi) := by
  intro h
  obtain ⟨s, hs⟩ := Proof.Ct.RISCV64Scrub.eq_scrubbed.verified.2.2
  have he : Exec RISCV64.isa rvBad s [] ((s.write .a0 1).write .a0 (1 <<< 32)) := .block rfl
  have := h .u32 _ rfl rfl s _ _ hs he
  have e : ((s.write .a0 1).write .a0 (1 <<< 32)).gpr .a0 = (1 <<< 32 : BitVec 64) := by
    simp [RISCV64.State.write]
  change ((s.write .a0 1).write .a0 (1 <<< 32)).gpr .a0 =
    ((((s.write .a0 1).write .a0 (1 <<< 32)).gpr .a0).setWidth 32).signExtend 64 at this
  rw [e] at this
  exact absurd this (by decide)

/-- PPC64LE: `r3 = 0x8000_0000_0000_0000`, a `u32` result of 0 with bit 63 set.
ELFv2 requires the upper half zero. -/
def ppcBad : Prog PPC64LE.isa := .block [.li .r3 1, .lsl .r3 .r3 63]

theorem ppc64le_upper_half_rejected :
    ¬ RetAbi PPC64LE.target ppcBad (Spec.Ct.eqContract PPC64LE.abi) := by
  intro h
  obtain ⟨s, hs⟩ := Proof.Ct.PPC64LE.Scrub.eq_scrubbed.verified.2.2
  have he : Exec PPC64LE.isa ppcBad s [] ((s.write .r3 1).write .r3 (1 <<< 63)) := .block rfl
  have := h .u32 _ rfl rfl s _ _ hs he
  have e : ((s.write .r3 1).write .r3 (1 <<< 63)).gpr .r3 = (1 <<< 63 : BitVec 64) := by
    simp [PPC64LE.State.write]
  change ((s.write .r3 1).write .r3 (1 <<< 63)).gpr .r3 =
    ((((s.write .r3 1).write .r3 (1 <<< 63)).gpr .r3).setWidth 32).setWidth 64 at this
  rw [e] at this
  exact absurd this (by decide)

end VG.Test.RetAbi
