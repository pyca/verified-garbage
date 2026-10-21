module

import VerifiedGarbage.Proof.RsaKeyGen.X86.LowPairFirst
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.RsaKeyGen.X86.LowPairStep

/-! # Native halves read by the masked scan form the original 64-bit word -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG VG.Proof.Mont

theorem pairAt_word (m : Mem) (base : Addr) (src : Nat) :
    (pairAt m base src).2 ++ (pairAt m base src).1 = word m base src := by
  rw [word, VG.Proof.Rc2.Word32.read64_pair, VG.Offset.add_add]
  rfl

theorem pairAt_zero_iff (m : Mem) (base : Addr) (src : Nat) :
    pairAt m base src = (0#32, 0#32) ↔ word m base src = 0#64 := by
  constructor
  · intro h
    rw [← pairAt_word, h]
    rfl
  · intro h
    have value := congrArg BitVec.toNat h
    rw [word_eq_w32] at value
    change w32 m base src + 2 ^ 32 * w32 m base (src + 4) = 0 at value
    have low : w32 m base src = 0 := by omega
    have high : w32 m base (src + 4) = 0 := by omega
    exact Prod.ext (BitVec.eq_of_toNat_eq low) (BitVec.eq_of_toNat_eq high)

end VG.Proof.RsaKeyGen.X86.LowPair
