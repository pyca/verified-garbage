module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.MontgomerySetup
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Impl.Dsa.X86.Generation.MontgomerySetup
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! Public constant initialization and the short fixed doubling schedule. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Dsa.X86

private def startHint : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (τr [.edi]) (contextStart 4)

private theorem startCheck :
    (VG.Taint.check taint (τr [.edi]) (contextStart 4) startHint).map (taint.le (τr [.edi])) =
      some true := by taint_decide

theorem montgomery_start_ct (n : Nat) : RelCT isa (VG.X86.Taint.Agree (τr [.edi]))
    (contextStart n) (VG.X86.Taint.Agree (τr [.edi])) :=
  erased_relCT _ (contextStart 4) startHint (by kernel_rfl)
    (by decide +kernel) (by decide +kernel) startCheck

private def zeroHint : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (τr [.edi]) (zerosW 0 1)

private theorem zeroCheck :
    (VG.Taint.check taint (τr [.edi]) (zerosW 0 1) zeroHint).map (taint.le (τr [.edi])) =
      some true := by taint_decide

private theorem constant_store_ct (j v : Nat) : RelCT isa (VG.X86.Taint.Agree (τr [.edi]))
    (.block [.mov .eax (.imm (BitVec.ofNat 32 v)), .store (VG.Impl.Mont.X86.sc j) .eax])
    (VG.X86.Taint.Agree (τr [.edi])) := by
  exact erased_relCT _
    (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc 0) .eax])
    (.block []) (by kernel_rfl) (by decide +kernel) (by decide +kernel)
    (by taint_decide)

theorem montgomery_constant_ct (k o x : Nat) : RelCT isa (VG.X86.Taint.Agree (τr [.edi]))
    (setConstW k o x) (VG.X86.Taint.Agree (τr [.edi])) := by
  unfold setConstW
  refine RelCT.seq (erased_relCT _ (zerosW 0 1) zeroHint (by kernel_rfl)
    (by decide +kernel) (by decide +kernel) zeroCheck) ?_
  apply blockFlatMap_relCT
  intro j
  split
  · exact VG.X86.RelCT.nil (fun _ _ h => h)
  · exact constant_store_ct _ _

private def doubleHint : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (τr [.edi])
    (.seq (.block [.mov .esi (.imm 1)]) (doubleLoop (contextMod 4) (slot 4 2) (slot 4 4)))

private theorem doubleCheck :
    (VG.Taint.check taint (τr [.edi])
      (.seq (.block [.mov .esi (.imm 1)]) (doubleLoop (contextMod 4) (slot 4 2) (slot 4 4)))
      doubleHint).map (taint.le (τr [.edi])) = some true := by taint_decide

theorem montgomery_seed_ct (n bits : Nat) : RelCT isa (VG.X86.Taint.Agree (τr [.edi]))
    (montgomerySeed n bits) (VG.X86.Taint.Agree (τr [.edi])) := by
  unfold montgomerySeed
  refine RelCT.seq (montgomery_constant_ct _ _ _) ?_
  exact erased_relCT _
    (.seq (.block [.mov .esi (.imm 1)]) (doubleLoop (contextMod 4) (slot 4 2) (slot 4 4)))
    doubleHint (by kernel_rfl) (by decide +kernel) (by decide +kernel) doubleCheck

end VG.Proof.Dsa.X86.Generation
