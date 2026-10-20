module

public import VerifiedGarbage.Proof.MlKem1024.Arm.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.Arm.KeyGenCT
public import VerifiedGarbage.Proof.MlKem1024.Arm.EncapsCT
public import VerifiedGarbage.Proof.MlKem1024.Arm.DecapsCT
public import VerifiedGarbage.Proof.MlKem1024.Arm.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.Arm.Decompress
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM-1024 (FIPS 203) on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.MlKem1024.Arm

def artifacts : List Artifact := [
  Spec.MlKem1024.compressEncodeApi.artifact Arm.target {
    code := Impl.MlKem1024.Arm.compressEncode1024
    verified := Proof.MlKem1024.Arm.CompressEncode.verified },
  Spec.MlKem1024.decodeDecompressApi.artifact Arm.target {
    code := Impl.MlKem1024.Arm.decodeDecompress1024
    verified := Proof.MlKem1024.Arm.Decompress.verified },
  Spec.MlKem1024.checkEkApi.artifact Arm.target {
    code := Impl.MlKem1024.Arm.checkEk1024
    verified := Proof.MlKem1024.Arm.CheckEk.verified },
  Spec.MlKem1024.keyGenApi.artifact Arm.target {
    notes := ["The function saves `r4`–`r11` and its return address in `scratch`; the 8 bytes of stack \
        below the stack pointer hold the stack arguments of the SHA-3 functions it calls."]
    code := Impl.MlKem1024.Arm.keygen1024
    stack := 8
    verified := Proof.MlKem1024.Arm.KeyGen.verified },
  Spec.MlKem1024.encapsApi.artifact Arm.target {
    notes := ["The function saves `r4`–`r11` and its return address in `scratch`, and copies `m` into it; \
        the 8 bytes of stack below the stack pointer hold the stack arguments of the SHA-3 functions it calls."]
    code := Impl.MlKem1024.Arm.encaps1024
    stack := 8
    verified := Proof.MlKem1024.Arm.Encaps.verified },
  Spec.MlKem1024.decapsApi.artifact Arm.target {
    notes := ["The function saves `r4`–`r11`, its return address and `key` in `scratch`, and copies `ct` \
        into it; the 8 bytes of stack below the stack pointer hold the stack arguments of the SHA-3 functions it \
        calls."]
    code := Impl.MlKem1024.Arm.decaps1024
    stack := 8
    verified := Proof.MlKem1024.Arm.Decaps.verified }]

end VG.Artifacts.MlKem1024.Arm
