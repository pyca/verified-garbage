module

public import VerifiedGarbage.Impl.Mont.X86.PreparedSquare
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Verified
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! # The emitted prepared multiplier fits the round's nested call budget -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86

theorem compact_noSp : NoSp VG.Impl.Mont.X86.PreparedSquare.dispatch :=
  .of_all (by decide +kernel)

theorem compact_stack : stackUse VG.Impl.Mont.X86.PreparedSquare.dispatch ≤ 16 := by decide +kernel

end VG.Proof.MillerRabin.X86
