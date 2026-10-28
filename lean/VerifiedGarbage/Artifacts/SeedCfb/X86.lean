module

public import VerifiedGarbage.Proof.Seed.X86.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86.FbLit

/-! # SEED-CFB128 artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.X86

/-- How the functions compute SEED, and the mode. -/
def note : String :=
  "Baseline IA-32: one block at a time, through `vg_seed_encrypt_blocks`, called on \
  the block with the first 1088 bytes of the working space, its arguments pushed in a frame (20 bytes of stack \
  with the return address). The mode is the generic CFB of `Impl/Modes/X86/`, whose data pointer and steps \
  left wait in `esi` and `ebp` across the call."

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact X86.target {
    notes := [note]
    code := Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 Impl.Seed.X86.cfbEncrypt
    stack := 1188
    verified := Proof.Seed.X86.Fb.cfbEncrypt_framed },
  Spec.Seed.cfbDecryptApi.artifact X86.target {
    notes := [note]
    code := Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 Impl.Seed.X86.cfbDecrypt
    stack := 1188
    verified := Proof.Seed.X86.Fb.cfbDecrypt_framed }]

end VG.Artifacts.SeedCfb.X86
