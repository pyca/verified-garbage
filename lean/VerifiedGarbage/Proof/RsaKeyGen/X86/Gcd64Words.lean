module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Shift

/-! # The GCD banks represent the same 64-bit pairs as the register reduction -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.Proof.Mont

theorem val32_two (m : Mem) (base : Addr) (offset : Nat) :
    val32 m base offset 2 = (word m base offset).toNat := by
  rw [word_eq_w32]
  simp only [val32, Nat.mul_zero, Nat.add_zero]

theorem append_pair (low high : BitVec 32) : (high ++ low).toNat = Mod64.pair low high := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt, Nat.shiftLeft_eq]
  unfold Mod64.pair
  omega

theorem val32_write_pair (m : Mem) (base : Addr) (offset : Nat) (low high : BitVec 32) :
    val32 (m.writeW (off base offset) (high ++ low)) base offset 2 = Mod64.pair low high := by
  rw [val32_two]
  change ((m.writeW (off base offset) (high ++ low)).readW (off base offset) 64).toNat = _
  rw [Mem.readW_writeW_self64, append_pair]

end VG.Proof.RsaKeyGen.X86.Gcd64
