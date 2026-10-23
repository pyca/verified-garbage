module

public import VerifiedGarbage.Proof.Seed.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.PPC64LE.Lit

/-! # SEED artifacts on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Seed.PPC64LE

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact PPC64LE.target {
    notes := ["The 32 inputs of `G` from 64-bit rotations of the key, then `G` of sixteen at a time, \
        bitsliced in general-purpose registers through the AES S-box circuit, with no table lookups. \
        The working space (1040 bytes, our caller's r14-r31 among them) is on the stack, zeroed \
        before returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1072 .r5 130 Impl.Seed.PPC64LE.expandKey
    stack := 1072
    verified := Proof.Seed.PPC64LE.expandKey_framed },
  Spec.Seed.ecbEncryptApi.artifact PPC64LE.target {
    notes := ["Sixteen blocks at a time, each round's `G` of all of them bitsliced in general-purpose registers \
        through the AES S-box circuit, with no table lookups. The working space (1040 bytes, our \
        caller's r14-r31 among them) is on the stack, zeroed before returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1072 .r6 130 (Impl.Seed.PPC64LE.ecb .encrypt)
    stack := 1072
    verified := Proof.Seed.PPC64LE.ecb_framed .encrypt },
  Spec.Seed.ecbDecryptApi.artifact PPC64LE.target {
    notes := ["Sixteen blocks at a time, each round's `G` of all of them bitsliced in general-purpose registers \
        through the AES S-box circuit, with no table lookups. The working space (1040 bytes, our \
        caller's r14-r31 among them) is on the stack, zeroed before returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1072 .r6 130 (Impl.Seed.PPC64LE.ecb .decrypt)
    stack := 1072
    verified := Proof.Seed.PPC64LE.ecb_framed .decrypt }]

end VG.Artifacts.Seed.PPC64LE
