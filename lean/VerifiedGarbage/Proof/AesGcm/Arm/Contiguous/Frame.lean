module

public import VerifiedGarbage.Impl.AesGcm.Arm.Contiguous
public import VerifiedGarbage.Proof.AesGcm.Arm.ArgSlots
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Gcm.Arm.Lit
meta import VerifiedGarbage.Proof.Gcm.Arm.Lit

/-! The two-pointer seal prepares a fixed six-word frame in A32 or Thumb-2. -/

@[expose] public section
namespace VG.Proof.AesGcm.Arm.Contiguous

open VG VG.Arm VG.Arm.Scrub VG.Impl.AesGcm.Arm.Contiguous

def slots : Args.Slots where
  count := 6
  bytes := 2592
  index j := ([0, 1, 3, 4, 5, 2] : List Nat)[j]!
  indexLt := by
    intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases this with h|h|h|h|h|h <;> subst h <;> decide
  header := by decide
  imm := by decide
  small := by decide

theorem frameArgs_run {u : State} (L : Args.Layout slots u) :
    ∃ t, execBlock isa frameArgs u = some (t, slots.frameTrace u.sp) ∧ Args.Ready slots u t :=
  Args.frameArgs_run L

theorem codeOk : CodeOk sealContiguous 2608 := by lit_decide

end VG.Proof.AesGcm.Arm.Contiguous
