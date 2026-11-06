module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSizes
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallArgs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallValid
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySaved
import VerifiedGarbage.Proof.Mont.X86.Compact.Restore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySized
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpBase
import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
import VerifiedGarbage.Proof.Framework.X86.Call

/-! # Callable native key assembly restores all cdecl registers and the return address -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86

theorem BodyOutcome.keep {E : Environment} {m : Mem} {s t : State} (R : BodyOutcome E m s)
    (eax : t.gpr .eax = s.gpr .eax) (memory : t.mem = s.mem) : BodyOutcome E m t := by
  simpa only [BodyOutcome, WrittenCore, eax, memory] using R

end VG.Proof.RsaKeyGen.X86.Key
