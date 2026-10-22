module

public import VerifiedGarbage.Proof.RsaPss.X86.Hash
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes
meta import VerifiedGarbage.Proof.RsaPss.X86.Hash
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes

/-! # RSASSA-PSS on x86: the SHA-512 family

SHA-384, SHA-512, SHA-512/224 and SHA-512/256. Their length field is 128
bits, whose high 64 are zero for the messages RSASSA-PSS hashes
(`len512`). -/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86

theorem ext128 {x : Nat} (hx : x < 2 ^ 64) (i : Nat) :
    (BitVec.ofNat 128 x).extractLsb' (8 * i) 8 = if i < 8 then (BitVec.ofNat 64 x).extractLsb' (8 * i) 8 else 0 := by
  apply BitVec.eq_of_toNat_eq
  split
  · simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : x < 2 ^ 128), Nat.mod_eq_of_lt hx]
  · simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : x < 2 ^ 128), Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
    rfl

/-- The 128-bit length field of a message shorter than `2^29` bytes. -/
theorem len512 (n : Nat) (hn : n < 2 ^ 29) :
    Proof.Sha512.md.lenBytes n = List.replicate 8 0 ++ Proof.MdStream.bytes64 true (BitVec.ofNat 64 (8 * n)) := by
  show Proof.Sha512.lenField _ = _
  unfold Proof.Sha512.lenField Proof.MdStream.bytes64
  simp only [ite_true, ext128 (show 8 * n < 2 ^ 64 by omega)]
  simp [List.range_succ]

theorem sha384Certs : Certs (shapeOf Proof.Pbkdf2.Md.X86.sha384M) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    NoSp.of_all (by decide +kernel)⟩ <;> exact ⟨_, by taint_decide⟩

/-- SHA-384, as RSASSA-PSS on x86 uses it. -/
def sha384 : PssHash where
  H := Proof.Pbkdf2.Md.X86.sha384M
  ok := Proof.Pbkdf2.Md.X86.sha384Ok
  len := len512
  L8 := by decide
  L16 := by decide
  NLB := by decide
  G := Spec.Mgf1.sha384
  hash _ := rfl
  glen := rfl
  one := by decide
  certs := Certs.of_shape sha384Certs

theorem sha512Certs : Certs (shapeOf Proof.Pbkdf2.Md.X86.sha512M') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    NoSp.of_all (by decide +kernel)⟩ <;> exact ⟨_, by taint_decide⟩

/-- SHA-512, as RSASSA-PSS on x86 uses it. -/
def sha512 : PssHash where
  H := Proof.Pbkdf2.Md.X86.sha512M'
  ok := Proof.Pbkdf2.Md.X86.sha512Ok'
  len := len512
  L8 := by decide
  L16 := by decide
  NLB := by decide
  G := Spec.Mgf1.sha512
  hash _ := rfl
  glen := rfl
  one := by decide
  certs := Certs.of_shape sha512Certs

theorem sha512_224Certs : Certs (shapeOf Proof.Pbkdf2.Md.X86.sha512_224M) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    NoSp.of_all (by decide +kernel)⟩ <;> exact ⟨_, by taint_decide⟩

/-- SHA-512/224, as RSASSA-PSS on x86 uses it. -/
def sha512_224 : PssHash where
  H := Proof.Pbkdf2.Md.X86.sha512_224M
  ok := Proof.Pbkdf2.Md.X86.sha512_224Ok
  len := len512
  L8 := by decide
  L16 := by decide
  NLB := by decide
  G := Spec.Mgf1.sha512_224
  hash _ := rfl
  glen := rfl
  one := by decide
  certs := Certs.of_shape sha512_224Certs

theorem sha512_256Certs : Certs (shapeOf Proof.Pbkdf2.Md.X86.sha512_256M) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    NoSp.of_all (by decide +kernel)⟩ <;> exact ⟨_, by taint_decide⟩

/-- SHA-512/256, as RSASSA-PSS on x86 uses it. -/
def sha512_256 : PssHash where
  H := Proof.Pbkdf2.Md.X86.sha512_256M
  ok := Proof.Pbkdf2.Md.X86.sha512_256Ok
  len := len512
  L8 := by decide
  L16 := by decide
  NLB := by decide
  G := Spec.Mgf1.sha512_256
  hash _ := rfl
  glen := rfl
  one := by decide
  certs := Certs.of_shape sha512_256Certs

end VG.Proof.RsaPss.X86
