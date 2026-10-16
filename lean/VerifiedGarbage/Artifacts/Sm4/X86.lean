module

public import VerifiedGarbage.Proof.Sm4.X86.KeyVerified
public import VerifiedGarbage.Proof.Sm4.X86.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86.Lit

/-! # SM4 artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Sm4.X86

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact X86.target {
    notes := ["Baseline IA-32: the key schedule's rounds bitsliced in general-purpose registers, eight copies of the key at a time, through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."]
    code := Impl.StackScratch.X86.withStackScratchWiped 1448 2 358 Impl.Sm4.X86.expandKey
    stack := 1448
    verified := Proof.Sm4.X86.expandKey_framed },
  Spec.Sm4.ecbEncryptApi.artifact X86.target {
    notes := ["Baseline IA-32: eight blocks at a time, bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."]
    code := Impl.StackScratch.X86.withStackScratchWiped 1452 3 358 (Impl.Sm4.X86.ecb .encrypt)
    stack := 1452
    verified := Proof.Sm4.X86.ecb_framed .encrypt },
  Spec.Sm4.ecbDecryptApi.artifact X86.target {
    notes := ["Baseline IA-32: eight blocks at a time, bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."]
    code := Impl.StackScratch.X86.withStackScratchWiped 1452 3 358 (Impl.Sm4.X86.ecb .decrypt)
    stack := 1452
    verified := Proof.Sm4.X86.ecb_framed .decrypt }]

end VG.Artifacts.Sm4.X86
