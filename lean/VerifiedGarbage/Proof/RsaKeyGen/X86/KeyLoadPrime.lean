module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoad
import VerifiedGarbage.Proof.RsaKeyGen.FrameOutside
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Import a prime in native words without reading uninitialized padding -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def loadPrimeRanges (n k out : Nat) : List (Nat × Nat) := [(arr n 0, 4 * k), (arr n out, S n)]

end VG.Proof.RsaKeyGen.X86.Key
