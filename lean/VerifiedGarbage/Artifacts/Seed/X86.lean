module

public import VerifiedGarbage.Proof.Seed.X86.KeyVerified
public import VerifiedGarbage.Proof.Seed.X86.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86.Lit

/-! # SEED artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Seed.X86

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact X86.target {
    notes := ["Baseline IA-32: the 32 inputs of `G` from the key words in the working space, then `G` of eight at a time, bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups."]
    code := Impl.StackScratch.X86.withStackScratchWiped 840 2 206 Impl.Seed.X86.expandKey
    stack := 840
    verified := Proof.Seed.X86.expandKey_framed },
  Spec.Seed.ecbEncryptApi.artifact X86.target {
    notes := ["Baseline IA-32: eight blocks at a time, each `G` of a round bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups."]
    code := Impl.StackScratch.X86.withStackScratchWiped 844 3 206 (Impl.Seed.X86.ecb .encrypt)
    stack := 844
    verified := Proof.Seed.X86.ecb_framed .encrypt },
  Spec.Seed.ecbDecryptApi.artifact X86.target {
    notes := ["Baseline IA-32: eight blocks at a time, each `G` of a round bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups."]
    code := Impl.StackScratch.X86.withStackScratchWiped 844 3 206 (Impl.Seed.X86.ecb .decrypt)
    stack := 844
    verified := Proof.Seed.X86.ecb_framed .decrypt }]

end VG.Artifacts.Seed.X86
