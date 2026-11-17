module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDerive
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDSelectTiming
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyFinal
import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInputPair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyReady
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPrepare
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLcmFrame
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputMap
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Spec.RsaKeyGen
import Mathlib.Data.Nat.Basic

/-! ### `RsaKeyGen.X86.KeyRetryFlag`, which this module and modules that import it used -/

section

/-! # The secret native retry comparison equals the released shared result -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/Retry.lean`, which only this module imported.
section

/-! # The released retry status identifies exactly the small private inverse -/

section
namespace VG.Proof.RsaKeyGen
open VG

theorem keyFromPrimes_retry_iff (nlen e p q : Nat) :
    Spec.RsaKeyGen.keyFromPrimes nlen e p q = .inr () ↔
      ∃ d, Spec.Rsa.inverse e (Nat.lcm (max p q - 1) (min p q - 1)) = some d ∧ d ≤ 2 ^ (nlen / 2) := by
  have sorted : (if p < q then (q, p) else (p, q)) = (max p q, min p q) := by
    by_cases order : p < q
    · simp only [order, ite_true, Nat.max_eq_right (Nat.le_of_lt order), Nat.min_eq_left (Nat.le_of_lt order)]
    · simp only [order, ite_false, Nat.max_eq_left (by omega : q ≤ p), Nat.min_eq_right (by omega : q ≤ p)]
  unfold Spec.RsaKeyGen.keyFromPrimes
  rw [sorted]
  dsimp only
  cases inv : Spec.Rsa.inverse e (Nat.lcm (max p q - 1) (min p q - 1)) with
  | none => simp
  | some d =>
    dsimp only
    by_cases small : d ≤ 2 ^ (nlen / 2)
    · simp [small]
    · rw [ite_eq_right small]
      cases other : Spec.Rsa.inverse (min p q) (max p q) with
      | none => simp [small]
      | some qi =>
        dsimp only
        split <;> simp [small]

end VG.Proof.RsaKeyGen
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem KeyReady.retry_iff {B : Addr} {n e p q : Nat} {m : Mem} (R : KeyReady B n e p q m) :
    (slot m B kOk = 1 ∧ num m B n aD ≤ 2 ^ (16 * n)) ↔
      Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q = .inr () := by
  rw [VG.Proof.RsaKeyGen.keyFromPrimes_retry_iff, show 32 * n / 2 = 16 * n by omega_using [], R.inverse]
  by_cases zero : slot m B kOk = 0
  · simp only [zero, ite_true, reduceCtorEq, false_and, exists_false]
  · have one : slot m B kOk = 1 := by have := R.bit; omega_using [zero, this]
    simp [one]

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyWritePortTiming`, which this module and modules that import it used -/

section

/-! # Masked key output uses only public pointers and byte lengths in its trace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def OutputPair (E : Environment) (s t : State) : Prop :=
  InputPair E s t ∧ VG.X86.Taint.Agree (workspaceTaint true) s t ∧
    slot s.mem E.base kOk ≤ 1 ∧ slot t.mem E.base kOk ≤ 1

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyImportedPair`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyLoadInputs`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyCorePair`, which this module and modules that import it used -/

section

/-! # Two secret factor pairs reach the retry comparison with the same public state -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyPrepareTiming.lean`, which only this module imported.
section

/-! # Sorted factors and LCM feed only the public exponent into control flow -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure Preparation (B : Addr) (Z n k e : Nat) (s : State) : Prop where
  workspace : Ws s B Z n 32
  pBound : num s.mem B n aPa < 2 ^ (32 * k)
  qBound : num s.mem B n aQa < 2 ^ (32 * k)
  zero : num s.mem B n aZero = 0
  one : num s.mem B n aOne = 1
  exponent : val32 s.mem B kEv 2 = e
  loaded : num s.mem B n aE = e

end VG.Proof.RsaKeyGen.X86.Key
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Key

structure CoreStart (B : Addr) (Z n k e p q : Nat) (s : State) : Prop extends Preparation B Z n k e s where
  pValue : num s.mem B n aPa = p
  qValue : num s.mem B n aQa = q

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # The complete native input prefix initializes the arithmetic and imports its original inputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def inputExponent (E : Environment) (m : Mem) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len)
def inputPrime (E : Environment) (m : Mem) (i : Nat) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion i).base (E.outputRegion i).len)

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Secret input snapshots are imported into native arithmetic with matching public state -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86

structure SizedStart (E : Environment) (e p q p' q' : Nat) (s t : State) : Prop where
  inputs : InputPair E s t
  leftExponent : inputExponent E s.mem = e
  rightExponent : inputExponent E t.mem = e
  leftP : inputPrime E s.mem 2 = p
  leftQ : inputPrime E s.mem 3 = q
  rightP : inputPrime E t.mem 2 = p'
  rightQ : inputPrime E t.mem 3 = q'

structure ImportedPair (E : Environment) (e p q p' q' : Nat) (s t : State) : Prop where
  inputs : InputPair E s t
  left : CoreStart E.base E.size E.n E.k e p q s
  right : CoreStart E.base E.size E.n E.k e p' q' t
  agree : VG.X86.Taint.Agree (workspaceTaint true) s t

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Completed numeric key derivation retains the public output environment and a boolean validity mask -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem core_mask_bit {B : Addr} {n e p q : Nat} {m : Mem} (R : CoreOutcome B n e p q m) :
    slot m B kOk ≤ 1 := by
  unfold CoreOutcome at R
  split at R <;> omega

end VG.Proof.RsaKeyGen.X86.Key
