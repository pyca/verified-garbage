module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.InvStep
import VerifiedGarbage.Proof.Rsa.X86.KeySub
public import VerifiedGarbage.Impl.Rsa.X86.Inverse

/-! # Initialize the native inverse's Euclidean bank and negated modulus -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot

structure InverseReady (B : Addr) (n a m : Nat) (s : State) : Prop where
  modulus : num s.mem B n aM = m
  negated : num s.mem B n aNM + m = 2 ^ (32 * n)
  zero : num s.mem B n aZero = 0
  initial : bank s.mem B n 0 = (a, m, 1, 0)

end VG.Proof.RsaKeyGen.X86.Key
