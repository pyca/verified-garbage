module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome
import Mathlib.Tactic.IntervalCases

/-! # The native output order is the shared RSA key's field order -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def keyField (key : Spec.RsaKeyGen.Key) : Nat → Nat
  | 0 => key.n
  | 1 => key.d
  | 2 => key.p
  | 3 => key.q
  | 4 => key.dP
  | 5 => key.dQ
  | _ => key.qInv

theorem assembled_field (B : Addr) (n : Nat) (m : Mem) {i : Nat} (hi : i < 7) :
    num m B n (outputIndex i) = keyField (assembledKey B n m) i := by
  interval_cases i <;> rfl

end VG.Proof.RsaKeyGen.X86.Key
