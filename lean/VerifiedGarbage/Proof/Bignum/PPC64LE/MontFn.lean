module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontSave
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Bignum.Minv32
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words32

/-!
# Montgomery multiplication on PPC64LE: the function

`vg_rsa_mont_mul(ws = r3, ws_len = r4, o = r5, a = r6, b = r7, scratch = r8)`
saves the nonvolatile registers in the scratch buffer, runs the arithmetic
(`core_ok`) and restores them. `numAt_eq`: a number of the working space
as the proofs read it.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE VG.Impl.Bignum
open VG.Proof.Rsa.Mont (numAt wOf wordAt Layout Operand Keeps arrAt aM minvWord)

/-- A number of the working space is its `2 w` digits. -/
theorem numAt_eq (m : Mem) (B : Addr) (w j : Nat) : numAt m B w j = val32 m B (slot w j) (2 * w) := by
  rw [← wordsVal_eq_val32, ← read_eq_wordsVal]; rfl

end VG.Proof.Bignum.PPC64LE
