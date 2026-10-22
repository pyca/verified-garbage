module

public import VerifiedGarbage.Proof.RsaPss.X86.Hash
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes
meta import VerifiedGarbage.Proof.RsaPss.X86.Hash
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes

/-! # RSASSA-PSS on x86: MD5 -/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86

theorem md5Certs : Certs (shapeOf Proof.Pbkdf2.Md.X86.md5M) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    NoSp.of_all (by decide +kernel)⟩ <;> exact ⟨_, by taint_decide⟩

/-- MD5, as RSASSA-PSS on x86 uses it. -/
def md5 : PssHash where
  H := Proof.Pbkdf2.Md.X86.md5M
  ok := Proof.Pbkdf2.Md.X86.md5Ok
  len _ _ := rfl
  L8 := Nat.le_refl _
  L16 := by decide
  NLB := by decide
  G := Spec.Mgf1.md5
  hash _ := rfl
  glen := rfl
  one := by decide
  certs := Certs.of_shape md5Certs

end VG.Proof.RsaPss.X86
