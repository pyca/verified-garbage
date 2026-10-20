module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Mont.X86.Exponent
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Fixed-width shifts require only the public workspace pointer -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

theorem shiftWord_ct (out : Nat) (last : Bool) :
    RelCT isa (VG.X86.Taint.Agree (τr [.edi])) (.block (shiftWord out last))
      (VG.X86.Taint.Agree (τr [.edi])) := by
  apply erased_relCT (.block (shiftWord out last)) (.block (shiftWord 0 last)) (.block []) (by cases last <;> rfl) rfl rfl
  cases last <;> rfl

theorem shiftExponent_ct (words out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.edi])) (.block (shiftExponent words out))
      (VG.X86.Taint.Agree (τr [.edi])) := by
  induction words generalizing out with
  | zero => exact RelCT.nil (fun _ _ h => h)
  | succ n ih => exact RelCT.block_append (RelCT.seq (shiftWord_ct out _) (ih (out + 4)))
end VG.Proof.Dsa.X86.Generation
