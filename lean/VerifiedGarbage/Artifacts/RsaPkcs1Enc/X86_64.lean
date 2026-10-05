import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCT
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees

/-! # RSAES-PKCS1-v1_5 encryption (RFC 8017 §7.2.1) on x86-64 -/

namespace VG.Artifacts.RsaPkcs1Enc.X86_64

open VG.Proof.RsaPkcs1Enc.X86_64 (pubImpl encStack enc_verified enc_spSafe)

def artifacts : List Artifact := [
  { Spec.RsaPkcs1Enc.encryptApi with
    target := X86_64.target
    doc := Spec.RsaPkcs1Enc.encryptApi.doc
      (notes := ["This implementation builds `EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` in its frame, finding \
        whether `PS` has a zero byte without a branch, and calls `" ++ pubImpl.name ++ "` on it, \
        which checks `n` and `e`. If `PS` had a zero byte, it then sets `out` to zeros and the \
        result to 0 under a mask, and overwrites the frame's `EM` with zeros either way."])
    code := Impl.RsaPkcs1Enc.X86_64.Encrypt.code pubImpl.name pubImpl.code
    contract := Spec.RsaPkcs1Enc.encryptContract X86_64.abi encStack
    stack := encStack
    verified := enc_verified pubImpl
    spSafe := enc_spSafe pubImpl }]

end VG.Artifacts.RsaPkcs1Enc.X86_64
