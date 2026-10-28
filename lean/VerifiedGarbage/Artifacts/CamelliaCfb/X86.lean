module

public import VerifiedGarbage.Proof.Camellia.X86.FbVerified
import VerifiedGarbage.Proof.Camellia.X86.FbLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CFB128 artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.X86

/-- How the functions compute Camellia, and the mode. -/
def note : String :=
  "Baseline IA-32: one block at a time, encrypted bitsliced in general-purpose registers, the S-boxes as \
  Boolean circuits, with no table lookups, in a batch of eight of which the other seven are unused; the table \
  of bitsliced subkeys is built once per call, inline, and each batch is a call of \
  `vg_camellia_crypt_prepared`, its arguments in a frame on the stack. The mode is the generic CFB of `Impl/Modes/X86/`, over \
  Camellia's ECB core."

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact X86.target {
    notes := [note]
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbEncrypt
    stack := 2772
    verified := Proof.Camellia.X86.Fb.cfbEncrypt_framed },
  Spec.Camellia.cfbDecryptApi.artifact X86.target {
    notes := [note]
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbDecrypt
    stack := 2772
    verified := Proof.Camellia.X86.Fb.cfbDecrypt_framed }]

end VG.Artifacts.CamelliaCfb.X86
