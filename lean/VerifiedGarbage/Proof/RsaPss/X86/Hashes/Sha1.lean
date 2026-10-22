module

public import VerifiedGarbage.Proof.RsaPss.X86.Hash
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha1
public import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
meta import VerifiedGarbage.Proof.RsaPss.X86.Hash
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha1
meta import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface

/-! # RSASSA-PSS on x86: SHA-1, with any backend -/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86
open VG.Proof.Sha1.X86.Variants (Backend)

/-- SHA-1's shape: its sizes and digest code. -/
def sha1Shape : Impl.Pbkdf2.Md.X86.Hash :=
  ⟨⟨64, 0, 20, 0, 0, "", .block [], "", .block [], "", .block []⟩, 20, 8, true, 0, "", .block [],
    Impl.Sha1.X86.Stream.params.out⟩

theorem sha1Certs : Certs sha1Shape := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    NoSp.of_all (by decide +kernel)⟩ <;> exact ⟨_, by taint_decide⟩

/-- SHA-1 with the backend `v`, as RSASSA-PSS on x86 uses it. -/
def sha1 (v : Backend) : PssHash where
  H := v.M
  ok := Proof.Pbkdf2.Md.X86.sha1Ok v.stream v.cmpN v.comp
  len _ _ := rfl
  L8 := Nat.le_refl _
  L16 := by show 8 ≤ 16; decide
  NLB := by show 20 + 8 ≤ 64; decide
  G := Spec.Mgf1.sha1
  hash _ := rfl
  glen := rfl
  one := by show 20 + 5 + 8 ≤ 64; decide
  certs := Certs.of_shape (show Certs sha1Shape from sha1Certs)

end VG.Proof.RsaPss.X86
