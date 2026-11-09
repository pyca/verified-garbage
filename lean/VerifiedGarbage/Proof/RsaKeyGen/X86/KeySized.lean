module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExport
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDerive
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent

/-! # Complete native import, derivation and masked export at every supported width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def BodyOutcome (E : Environment) (m : Mem) (t : State) : Prop :=
  WrittenCore E.outputs
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 2).base (E.outputRegion 2).len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 3).base (E.outputRegion 3).len)) t

end VG.Proof.RsaKeyGen.X86.Key
