module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEven
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace

/-! # Form a secret modulus-validity bit from a borrow and parity -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem odd_mask (b x : BitVec 32) (bit : b.toNat ≤ 1) :
    (((1 : BitVec 32) - b) &&& x &&& (1 : BitVec 32)).toNat =
      if b.toNat = 0 then x.toNat % 2 else 0 := by
  rcases VG.Proof.Rsa.KeyBits32.bit_cases bit with hb | hb
  · rw [hb]
    change (((1 : BitVec 32) &&& x) &&& (1 : BitVec 32)).toNat = x.toNat % 2
    rw [BitVec.and_comm (1 : BitVec 32) x, BitVec.and_assoc, BitVec.and_self]
    exact VG.Proof.Rsa.KeyBits32.bv_and_one x
  · rw [hb]
    change ((0#32 &&& x) &&& (1 : BitVec 32)).toNat = 0
    simp only [BitVec.zero_and, BitVec.toNat_zero]

end VG.Proof.RsaKeyGen.X86.Key
