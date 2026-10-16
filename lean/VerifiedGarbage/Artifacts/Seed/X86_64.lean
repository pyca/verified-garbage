module

public import VerifiedGarbage.Proof.Seed.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86_64.Lit

/-! # SEED artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Seed.X86_64

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact X86_64.target {
    notes := ["Baseline x86-64: the 32 inputs of `G` from 64-bit rotations of the key, then `G` of sixteen at a time, bitsliced in general-purpose registers through the AES S-box circuit."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1064 .rdx 132 Impl.Seed.X86_64.expandKey
    stack := 1064
    verified := Proof.Seed.X86_64.expandKey_framed },
  Spec.Seed.ecbEncryptApi.artifact X86_64.target {
    notes := ["Baseline x86-64: sixteen blocks at a time, each `G` of a round bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1064 .rcx 132 Impl.Seed.X86_64.encrypt
    stack := 1064
    verified := Proof.Seed.X86_64.encrypt_framed },
  Spec.Seed.ecbDecryptApi.artifact X86_64.target {
    notes := ["Baseline x86-64: sixteen blocks at a time, each `G` of a round bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1064 .rcx 132 Impl.Seed.X86_64.decrypt
    stack := 1064
    verified := Proof.Seed.X86_64.decrypt_framed }]

end VG.Artifacts.Seed.X86_64
