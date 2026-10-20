module
public import VerifiedGarbage.Proof.Dsa.X86.ArithmeticHeadTiming

import VerifiedGarbage.Proof.Dsa.X86.ArithmeticTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreStoreTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Complete modular products have secret-independent execution traces -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem coreProductMod_relCT (base : Addr) (size len output : Nat) (modulus : Field) (a b : Pointer)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (ArithmeticAgree base size len len modulus a b)
      (Core.productMod len modulus a b output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold Core.productMod
  dsimp only
  apply RelCT.assoc
  apply RelCT.seq (arithmeticHead_relCT base size len len modulus a b hz h4 hmax hw4)
  exact (RelCT.seq (ordinaryMul_relCT _) (coreStore_workspace_relCT len output)).mono
    (fun _ _ h => taint.le_sound (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
    (fun _ _ h => h)

theorem coreSum_relCT (base : Addr) (size len output : Nat) (a b : Pointer)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (ArithmeticAgree base size len len .q a b)
      (Core.sum len a b output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold Core.sum
  dsimp only
  apply RelCT.assoc
  refine RelCT.seq (arithmeticHead_relCT base size len len .q a b hz h4 hmax hw4) ?_
  refine RelCT.seq (ordinaryAdd_relCT _) ?_
  exact (coreStore_workspace_relCT len output).mono
    (fun _ _ h => taint.le_sound (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
    (fun _ _ h => h)

end VG.Proof.Dsa.X86
