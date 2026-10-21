module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

/-! # The quotient, remainder, and tiny inverse ready for native assembly -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

structure OddPrepared (B : Addr) (n e L : Nat) (s : State) : Prop where
  exponent : val32 s.mem B kEv 2 = e
  lcm : num s.mem B n aL = L
  quotient : num s.mem B n aU = L / e
  remainder : num s.mem B n aV = L % e
  one : num s.mem B n aOne = 1
  coefficient : num s.mem B 2 3 < e
  congruence : (e : Int) ∣ (num s.mem B 2 3 : Int) * (L % e) - Nat.gcd (L % e) e
  mask : slot s.mem B kOk = (if 2 ≤ L ∧ Nat.gcd (L % e) e = 1 then 1 else 0)

end VG.Proof.RsaKeyGen.X86.Key
