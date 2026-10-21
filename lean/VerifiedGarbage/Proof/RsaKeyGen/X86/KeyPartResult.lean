module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyQinv
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCrtCorrect
public import VerifiedGarbage.Spec.Rsa
public import Init.Data.Nat.Coprime
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

/-! # The computed key components before masked external export -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def keyPartArrays : List Nat := [aDen, aQi, aU, aDp, aDq, aN]

structure KeyPartResult (B : Addr) (n : Nat) (m : Mem) (t : State) : Prop where
  modulus : num t.mem B n aN = num m B n aPa * num m B n aQa
  dp : num t.mem B n aDp = num m B n aD % crtDivisor (num m B n aPm)
  dq : num t.mem B n aDq = num m B n aD % crtDivisor (num m B n aQm)
  qiBound : num t.mem B n aQi < safePrime (num m B n aPa)
  qiCongruence : (safePrime (num m B n aPa) : Int) ∣
    (num t.mem B n aQi : Int) * num m B n aQa - Nat.gcd (num m B n aQa) (safePrime (num m B n aPa))
  mask : slot t.mem B kOk = (if slot m B kOk = 1 ∧
    Nat.gcd (num m B n aQa) (safePrime (num m B n aPa)) = 1 ∧
    2 ^ (32 * n - 1) ≤ num m B n aPa * num m B n aQa ∧
    num m B n aPa % 2 = 1 ∧ num m B n aQa % 2 = 1 ∧
    Spec.Rsa.exponentValid (val32 m B kEv 2) = true then 1 else 0)
  status : slot t.mem B kStatus = slot t.mem B kOk

end VG.Proof.RsaKeyGen.X86.Key
