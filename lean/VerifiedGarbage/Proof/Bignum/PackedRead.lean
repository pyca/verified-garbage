module
public import VerifiedGarbage.Proof.Mont.Words

import VerifiedGarbage.Proof.Bignum.ByteWords
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Relate packed RSA limbs to whole little-endian reads -/

@[expose] public section
namespace VG.Proof.Bignum
open VG VG.Proof.Mont

theorem wordsVal_read (m : Mem) (base : Addr) (d n : Nat) :
    wordsVal m base d n = (m.read (off base d) (8 * n)).toNat := by
  rw [wordsVal_eq_val32, ← read_eq_val32]
  rw [show 4 * (2 * n) = 8 * n by omega]

end VG.Proof.Bignum
