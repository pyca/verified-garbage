module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGcdFrame
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEven
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Impl.Rsa.X86.Inverse
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
/-! # Complete native GCD stage for the RSA LCM -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def canonU (u v : Nat) : Nat := if v % 2 = 0 then v else u
def canonV (u v : Nat) : Nat := if v % 2 = 0 then u else v

end VG.Proof.RsaKeyGen.X86.Key
