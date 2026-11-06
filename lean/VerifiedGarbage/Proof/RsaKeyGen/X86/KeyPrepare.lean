module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyReady
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLcmFrame
import VerifiedGarbage.Impl.Rsa.X86.Inverse
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
import VerifiedGarbage.Spec.Rsa

/-! # The native factor, LCM, and private-inverse stages compose -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def prepareArrays : List Nat := [aPa, aQa, aPm, aQm, aPhi, aHalf, aU, aV, aDen, aL, aD]

end VG.Proof.RsaKeyGen.X86.Key
