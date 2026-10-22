module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcVerified

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86

It uses 1132 bytes of stack: the push of the registers (16 bytes), its
frame (1072 bytes) and the 44 bytes of the call of
`vg_rsa_public_precomputed_checked`.
-/

@[expose] public section
namespace VG.Artifacts.RsaPkcs1Enc.X86
open VG.Proof.RsaPkcs1Sig.X86.Ver (baseline)

def artifacts : List Artifact := [
  Spec.RsaPkcs1Enc.encryptPrecomputedApi.artifact VG.X86.target {
    notes := ["This implementation builds \
      `EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` in its frame, finding whether `PS` has a zero byte without a \
      branch, and calls `" ++ baseline.name ++ "` on it with the cached modulus values. It then sets `out` \
      to zeros and the result to 0 under a mask if `PS` had a zero byte, without branching on the public \
      operation's result, and overwrites the frame's `EM` with zeros either way."]
    code := Impl.RsaPkcs1Enc.X86.Precomputed.code baseline.name baseline.code
    stack := Proof.RsaPkcs1Enc.X86.Pc.stackBytes
    verified := Proof.RsaPkcs1Enc.X86.Pc.code_verified baseline
    spSafe := Proof.RsaPkcs1Enc.X86.Pc.code_sp baseline }]

end VG.Artifacts.RsaPkcs1Enc.X86
