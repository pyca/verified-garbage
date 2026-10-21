module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpBase
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! # Native key arithmetic preserves ESP through every phase and exponent branch -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyNoSp
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Impl.RsaKeyGen.X86.Key

theorem primes_noSp (n : Nat) : NoSp (primes n) := by
  apply NoSp.of_all
  simp only [primes, order, decTo, primeProduct, seqs, Code.allInstrs,
    checked (sub3 _ _ _ _), checked (sel _ _ _ _ _), checked (copy _ _ _), checked (eqS _ _ _ _ _),
    checked (product _ _ _ _ _ _)]
  rfl

theorem lcm_noSp (n : Nat) : NoSp (lcmPart n) := by
  apply NoSp.of_all
  simp only [lcmPart, twos, twoStep, halveStep, halfIf, gcdPart, oddSecond, oddModulus, gcdFrom,
    seqs, Code.allInstrs, checked (copy _ _ _), checked (sel _ _ _ _ _), checked (half _ _),
    checked (sub3 _ _ _ _), checked (constArray _ _ _), checked (inverseFrom _ _ _),
    checked (widenCopy _ _ _ _), checked (divisionFrom _ _ _ _ _)]
  rfl

theorem dSelect_noSp (n : Nat) : NoSp (dSelect n) := by
  apply NoSp.of_all
  simp only [dSelect, dZero, dOne, dEven, dOdd, dOddPrepare, dOddFinish, gcdIsOne,
    lAtLeastTwo, oddModulus, complement, correction, correctionNumerator, dProduct,
    seqs, Code.allInstrs, checked (copy _ _ _), checked (eqS _ _ _ _ _), checked (sel _ _ _ _ _),
    checked (sub3 _ _ _ _), checked (constArray _ _ _), checked (inverseFrom _ _ _),
    checked (widenCopy _ _ _ _), checked (divisionFrom _ _ _ _ _), checked (product _ _ _ _ _ _)]
  rfl

theorem keyPart_noSp (n : Nat) : NoSp (keyPart n) := by
  apply NoSp.of_all
  simp only [keyPart, qinvPart, crtPart, nPart, finalMask, divisorOf, oddModulus, gcdIsOne,
    primeProduct, withFlag, andFlag, exponentAtLeastThree,
    seqs, Code.allInstrs, checked (eqS _ _ _ _ _), checked (sel _ _ _ _ _),
    checked (sub3 _ _ _ _), checked (constArray _ _ _), checked (inverseFrom _ _ _),
    checked (widenCopy _ _ _ _), checked (divisionFrom _ _ _ _ _), checked (product _ _ _ _ _ _)]
  rfl

theorem derive_noSp (n : Nat) : NoSp (deriveLoaded n) := by
  apply NoSp.of_all
  simp only [deriveLoaded, prepareLoaded, smallMask, retry, seqs, Code.allInstrs,
    checked (primes_noSp n), checked (lcm_noSp n), checked (dSelect_noSp n), checked (keyPart_noSp n),
    checked (constArray _ _ _), checked (sub3 _ _ _ _)]
  rfl

end VG.Proof.RsaKeyGen.X86.KeyNoSp
