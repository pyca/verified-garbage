module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace

/-! # The secret selection bit for a common RSA LCM halving -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem num_parity (m : Mem) (B : Addr) {n : Nat} (positive : 0 < n) (j : Nat) :
    num m B n j % 2 = w32 m B (arr n j) % 2 := by
  cases n with
  | zero => omega
  | succ n => exact VG.Proof.Mont.X86.Dynamic.val32_parity m B (arr (n + 1) j) n

theorem even_bit (x y : BitVec 32) :
    (((x ||| y) &&& (1 : BitVec 32)) ^^^ (1 : BitVec 32)).toNat =
      if x.toNat % 2 = 0 ∧ y.toNat % 2 = 0 then 1 else 0 := by
  rw [BitVec.and_or_distrib_right]
  have bx : (x &&& (1 : BitVec 32)).toNat ≤ 1 := by
    rw [VG.Proof.Rsa.KeyBits32.bv_and_one]
    omega
  have by' : (y &&& (1 : BitVec 32)).toNat ≤ 1 := by
    rw [VG.Proof.Rsa.KeyBits32.bv_and_one]
    omega
  rw [VG.Proof.Rsa.KeyBits32.bv_nor_bits bx by',
    VG.Proof.Rsa.KeyBits32.bv_and_one, VG.Proof.Rsa.KeyBits32.bv_and_one]

end VG.Proof.RsaKeyGen.X86.Key
