module

public import VerifiedGarbage.Impl.Mont.X86.Sse2
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Mont.X86.Sse2.Shape

/-! # The emitted prepared multiplier fits the round's nested call budget -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86

theorem compact_noSp : NoSp VG.Impl.Mont.X86.Sse2.preparedBody := VG.Proof.Mont.X86.Sse2.preparedBody_NoSp

theorem compact_stack : stackUse VG.Impl.Mont.X86.Sse2.preparedBody ≤ 56 := by
  rw [VG.Proof.Mont.X86.Sse2.preparedBody_stack]

end VG.Proof.MillerRabin.X86
