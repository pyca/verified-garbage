module

public import VerifiedGarbage.Proof.Camellia.X86_64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CFB128 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.X86_64

/-- How the functions compute Camellia, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time (each block's input depends on the block before), encrypted bitsliced in \
  general-purpose registers (the S-boxes as Boolean circuits), with no table lookups, in a batch of eight of which \
  the other seven are unused; the subkeys are prepared once per call, inline, and each batch is a call of \
  `vg_camellia_crypt_prepared`. The mode is the generic CFB of `Impl/Modes/X86_64/`, \
  over Camellia's ECB core."

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact X86_64.target {
    notes := [note]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbEncrypt
    stack := 3288
    verified := Proof.Camellia.X86_64.cfbEncrypt_framed },
  Spec.Camellia.cfbDecryptApi.artifact X86_64.target {
    notes := [note]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbDecrypt
    stack := 3288
    verified := Proof.Camellia.X86_64.cfbDecrypt_framed }]

end VG.Artifacts.CamelliaCfb.X86_64
