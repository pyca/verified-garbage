module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCT
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSAES-PKCS1-v1_5 encryption (RFC 8017 §7.2.1) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.X86_64

open VG.Proof.RsaPkcs1Enc.X86_64 (pubImpl encStack enc_verified enc_spSafe)

def artifacts : List Artifact := [
  Spec.RsaPkcs1Enc.encryptApi.artifact X86_64.target {
    notes := ["This implementation builds `EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` in its frame, finding \
        whether `PS` has a zero byte without a branch, and calls `" ++ pubImpl.name ++ "` on it, \
        which checks `n` and `e`. If `PS` had a zero byte, it then sets `out` to zeros and the \
        result to 0 under a mask, and overwrites the frame's `EM` with zeros either way."]
    code := Impl.RsaPkcs1Enc.X86_64.Encrypt.code pubImpl.name pubImpl.code
    stack := encStack
    verified := enc_verified pubImpl
    spSafe := enc_spSafe pubImpl }]

end VG.Artifacts.RsaPkcs1Enc.X86_64
