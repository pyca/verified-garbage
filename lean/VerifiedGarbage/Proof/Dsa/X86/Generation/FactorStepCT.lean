module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.ShiftCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorCTState
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Factor
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.ShiftCT

/-! # A factor step has a fixed access sequence, independently of its low bit -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem factorStep_ct (n : Nat) :
    RelCT isa (Two (FactorAt n)) (factorStep n) (fun _ _ => True) := by
  have tail : RelCT isa (VG.X86.Taint.Agree (τr [.edi])) (.block (factorTest n)) (fun _ _ => True) :=
    RelCT.taint (A := taint) (τr [.edi]) (fun _ _ h => h) (hc := .block []) (by
      exact (congrArg Option.isSome (VG.Proof.Mont.X86.Dynamic.check_of_erase_eq
        (.block (factorTest n)) (.block (factorTest 1)) (τr [.edi]) (.block []) rfl rfl rfl)).trans (by rfl))
  refine (RelCT.seq (shiftExponent_ct (2 * n) (slot n 8)) tail).mono ?_ (fun _ _ h => h)
  rintro s t ⟨p, hs, ht⟩
  apply agree_regs
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact BitVec.eq_of_toNat_eq (hs.1.edi_toNat.trans ht.1.edi_toNat.symm)
end VG.Proof.Dsa.X86.Generation
