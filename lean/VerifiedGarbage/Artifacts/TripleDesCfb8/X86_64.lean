module

public import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit

/-! # Triple DES-CFB8 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.X86_64

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time, through the scalar block function (`vg_triple_des_encrypt_block`'s \
  code, inlined), with Boolean S-box circuits and no table lookups; the schedule is copied into the working \
  space once per call. The mode is the generic CFB8 of `Impl/Modes/X86_64/`."

def artifacts : List Artifact := [
  Spec.TripleDes.cfb8EncryptApi.artifact X86_64.target {
    notes := [note]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfb8Encrypt
    stack := 984
    verified := Proof.TripleDes.X86_64.cfb8Encrypt_framed },
  Spec.TripleDes.cfb8DecryptApi.artifact X86_64.target {
    notes := [note]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfb8Decrypt
    stack := 984
    verified := Proof.TripleDes.X86_64.cfb8Decrypt_framed }]

end VG.Artifacts.TripleDesCfb8.X86_64
