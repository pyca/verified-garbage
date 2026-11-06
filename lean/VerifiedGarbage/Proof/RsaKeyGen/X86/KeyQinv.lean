module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.Rsa.X86.KeyScalar
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
import VerifiedGarbage.Impl.Rsa.X86.Inverse
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Rsa.X86.InvLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseLoad
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent

/-! # The CRT coefficient uses a prime-width native inverse -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def safePrime (p : Nat) : Nat := if p % 2 = 1 ∧ 3 ≤ p then p else 3
def qinvArrays : List Nat := [aDen, aQi]

end VG.Proof.RsaKeyGen.X86.Key
