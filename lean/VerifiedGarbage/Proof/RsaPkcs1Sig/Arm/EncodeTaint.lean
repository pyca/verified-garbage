module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Encode
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Encode
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # EMSA-PKCS1-v1_5 encoding on ARMv7: the taint analysis

`encode` is constant time when the buffer, the hash value's address, the
hash function's number and the lengths are public: the hash value is only
copied. -/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm

theorem encode_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .r2, .r3, .lr]) encode hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.RsaPkcs1Sig.Arm
