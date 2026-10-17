module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivPdPrefix
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Exact public-operation stack arguments and retained status -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

def pdArgument (g : PrivGeometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.sources 1 | 1 => BitVec.ofNat 32 g.exponentLength
  | 2 => g.temporary | 3 => BitVec.ofNat 32 g.length
  | 4 => g.workspace | _ => BitVec.ofNat 32 g.scratchLength

theorem pdPrefixMem_arguments (g : PrivGeometry) (s : State) (j : Nat) (hj : j < 6) :
    (pdPrefixMem g s).readW (off (State.addr g.stack) (4 * j)) 32 = pdArgument g j := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · unfold pdPrefixMem pdArgument
    rw [outside_read32 (writeW32_outside _ _ (d := 20) _ (by decide)) (d := 0) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 16) _ (by decide)) (d := 0) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 12) _ (by decide)) (d := 0) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 8) _ (by decide)) (d := 0) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 4) _ (by decide)) (d := 0) (by decide) (by decide),
      Mem.readW_writeW_self32]
    rfl
  · unfold pdPrefixMem pdArgument
    rw [outside_read32 (writeW32_outside _ _ (d := 20) _ (by decide)) (d := 4) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 16) _ (by decide)) (d := 4) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 12) _ (by decide)) (d := 4) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 8) _ (by decide)) (d := 4) (by decide) (by decide),
      Mem.readW_writeW_self32]
    rfl
  · unfold pdPrefixMem pdArgument
    rw [outside_read32 (writeW32_outside _ _ (d := 20) _ (by decide)) (d := 8) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 16) _ (by decide)) (d := 8) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 12) _ (by decide)) (d := 8) (by decide) (by decide),
      Mem.readW_writeW_self32]
    rfl
  · unfold pdPrefixMem pdArgument
    rw [outside_read32 (writeW32_outside _ _ (d := 20) _ (by decide)) (d := 12) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 16) _ (by decide)) (d := 12) (by decide) (by decide),
      Mem.readW_writeW_self32]
    rfl
  · unfold pdPrefixMem pdArgument
    rw [outside_read32 (writeW32_outside _ _ (d := 20) _ (by decide)) (d := 16) (by decide) (by decide),
      Mem.readW_writeW_self32]
    rfl
  · unfold pdPrefixMem pdArgument
    rw [Mem.readW_writeW_self32]
    rfl

theorem pdPrefixMem_status (g : PrivGeometry) (s : State) :
    (pdPrefixMem g s).readW (off (State.addr g.stack) oR3) 32 = s.gpr .r0 := by
  unfold pdPrefixMem
  rw [outside_read32 (writeW32_outside _ _ (d := 20) _ (by decide)) (d := oR3) (by decide) (by decide),
    outside_read32 (writeW32_outside _ _ (d := 16) _ (by decide)) (d := oR3) (by decide) (by decide),
    outside_read32 (writeW32_outside _ _ (d := 12) _ (by decide)) (d := oR3) (by decide) (by decide),
    outside_read32 (writeW32_outside _ _ (d := 8) _ (by decide)) (d := oR3) (by decide) (by decide),
    outside_read32 (writeW32_outside _ _ (d := 4) _ (by decide)) (d := oR3) (by decide) (by decide),
    outside_read32 (writeW32_outside _ _ (d := 0) _ (by decide)) (d := oR3) (by decide) (by decide),
    Mem.readW_writeW_self32]
end VG.Proof.Rsa.Arm
