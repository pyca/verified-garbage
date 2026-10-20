module

public import VerifiedGarbage.Proof.RsaPss.Arm.Hash
public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Sha256
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Sha256.Arm.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Sha1.Arm.Lit
import VerifiedGarbage.Proof.Sha512.Arm.Lit
meta import VerifiedGarbage.Proof.RsaPss.Arm.Hash
meta import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Sha256
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Sha256.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Sha1.Arm.Lit
meta import VerifiedGarbage.Proof.Sha512.Arm.Lit

/-! # RSASSA-PSS on ARMv7: SHA-256 -/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm

/-- SHA-256, as RSASSA-PSS on ARMv7 uses it. -/
def sha256 : PssHash where
  H := ⟨Proof.Pbkdf2.Md.Arm.sha256Md, Impl.Sha256.Arm.Stream.params.len⟩
  ok := Proof.Pbkdf2.Md.Arm.sha256MdOK
  len := Proof.Sha256.Arm.Stream.shape.len
  lenAll _ _ := trivial
  G := Spec.Mgf1.sha256
  hash _ := rfl
  glen := rfl
  outCk := by exact ⟨_, by taint_decide⟩
  lenCk := by exact ⟨_, by taint_decide⟩
  one := by decide

end VG.Proof.RsaPss.Arm
