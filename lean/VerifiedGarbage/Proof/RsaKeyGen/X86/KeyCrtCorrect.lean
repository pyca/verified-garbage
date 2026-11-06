module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEvenFrame
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
import VerifiedGarbage.Impl.Rsa.X86.Inverse
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
import Aesop.BuiltinRules
/-! # Compute both CRT exponents with safe fixed-schedule division -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyDivisor.lean`, which only this module imported.
section


end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def crtArrays : List Nat := [aDen, aU, aDp, aDq]
def crtDivisor (x : Nat) : Nat := if x = 0 then 1 else x

end VG.Proof.RsaKeyGen.X86.Key
