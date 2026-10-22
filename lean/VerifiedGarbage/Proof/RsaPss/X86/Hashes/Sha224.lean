module

public import VerifiedGarbage.Proof.RsaPss.X86.Hash
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha224
public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
meta import VerifiedGarbage.Proof.RsaPss.X86.Hash
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha224
meta import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface

/-! # RSASSA-PSS on x86: SHA-224, with any SHA-256 backend -/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86
open VG.Proof.Sha256.X86.Variants (Backend)

/-- SHA-224's shape: its sizes and digest code. -/
def sha224Shape : Impl.Pbkdf2.Md.X86.Hash :=
  ⟨⟨64, 0, 28, 0, 0, "", .block [], "", .block [], "", .block []⟩, 32, 8, true, 0, "", .block [],
    Impl.Sha256.X86.Stream.params.out⟩

theorem sha224Certs : Certs sha224Shape := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    NoSp.of_all (by decide +kernel)⟩ <;> exact ⟨_, by taint_decide⟩

/-- SHA-224 with the SHA-256 backend `v`, as RSASSA-PSS on x86 uses it. -/
def sha224 (v : Backend) : PssHash where
  H := v.M224
  ok := Proof.Pbkdf2.Md.X86.sha224Ok v.stream v.cmpN v.comp
  len _ _ := rfl
  L8 := Nat.le_refl _
  L16 := by show 8 ≤ 16; decide
  NLB := by show 32 + 8 ≤ 64; decide
  G := Spec.Mgf1.sha224
  hash _ := rfl
  glen := rfl
  one := by show 28 + 5 + 8 ≤ 64; decide
  certs := Certs.of_shape (show Certs sha224Shape from sha224Certs)

end VG.Proof.RsaPss.X86
