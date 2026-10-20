module

public import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit

/-! # Triple DES-CFB64 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.X86_64

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time, through the scalar block function (`vg_triple_des_encrypt_block`'s \
  code, inlined), with Boolean S-box circuits and no table lookups; the schedule is copied into the working \
  space once per call. The mode is the generic CFB of `Impl/Modes/X86_64/`."

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact X86_64.target {
    notes := [note]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbEncrypt
    stack := 984
    verified := Proof.TripleDes.X86_64.cfbEncrypt_framed },
  Spec.TripleDes.cfbDecryptApi.artifact X86_64.target {
    notes := [note]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbDecrypt
    stack := 984
    verified := Proof.TripleDes.X86_64.cfbDecrypt_framed }]

end VG.Artifacts.TripleDesCfb.X86_64
