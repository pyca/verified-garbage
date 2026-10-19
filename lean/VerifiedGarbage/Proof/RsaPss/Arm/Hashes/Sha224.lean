module

public import VerifiedGarbage.Proof.RsaPss.Arm.Hash
public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Sha224
meta import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Sha224
meta import VerifiedGarbage.Proof.RsaPss.Arm.Hash
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Md5.Arm.Shared
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Instances
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Sha1.Arm.Shared
import VerifiedGarbage.Proof.Sha256.Arm.Shared
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Common
import VerifiedGarbage.Proof.Sha256.Scratch
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Proof.Sha512.Arm.Shared
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Hmac.Common
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.Md5.Arm.Shared
meta import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Instances
meta import VerifiedGarbage.Proof.Pbkdf2.Memory
meta import VerifiedGarbage.Proof.Sha1.Arm.Shared
meta import VerifiedGarbage.Proof.Sha256.Arm.Shared
meta import VerifiedGarbage.Proof.Sha256.Arm.Stream.Common
meta import VerifiedGarbage.Proof.Sha256.Scratch
meta import VerifiedGarbage.Proof.Sha256.StateMem
meta import VerifiedGarbage.Proof.Sha512.Arm.Shared

/-! # RSASSA-PSS on ARMv7: SHA-224 -/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm

/-- SHA-224, as RSASSA-PSS on ARMv7 uses it. -/
def sha224 : PssHash where
  H := ⟨Proof.Pbkdf2.Md.Arm.sha224Md, Impl.Sha256.Arm.Stream.params.len⟩
  ok := Proof.Pbkdf2.Md.Arm.sha224MdOK
  len := Proof.Sha256.Arm.Stream.shape.len
  lenAll _ _ := trivial
  G := Spec.Mgf1.sha224
  hash _ := rfl
  glen := rfl
  outCk := by exact ⟨_, by taint_decide⟩
  lenCk := by exact ⟨_, by taint_decide⟩
  one := by decide

end VG.Proof.RsaPss.Arm
