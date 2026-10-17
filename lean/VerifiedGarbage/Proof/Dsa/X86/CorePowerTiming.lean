module

public import VerifiedGarbage.Proof.Dsa.X86.ArithmeticHeadTiming
public import VerifiedGarbage.Proof.Dsa.X86.CoreStoreTiming

/-! # Constant-time complete modular exponentiation calls -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem powerTail_relCT (n len expWords output : Nat) (he : 0 < expWords) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.seq (exponentiate n expWords) (Core.store len output))
      (VG.X86.Taint.Agree (workspaceTaint true)) :=
  RelCT.seq (checkedProgramChange (σ := workspaceTaint false) (exponentiate_check n expWords he) rfl)
    (coreStore_workspace_relCT len output)

theorem corePower_relCT (base : Addr) (size len expLen output : Nat) (modulus : Field) (a b : Pointer)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) (he : 0 < expLen) :
    RelCT isa (ArithmeticAgree base size len expLen modulus a b)
      (Core.power len expLen modulus a b output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold Core.power
  dsimp only
  apply RelCT.assoc
  apply RelCT.seq (arithmeticHead_relCT base size len expLen modulus a b hz h4 hmax hw4)
  exact (powerTail_relCT _ len _ output (by omega)).mono
    (fun _ _ h => taint.le_sound (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
    (fun _ _ h => h)

end VG.Proof.Dsa.X86
