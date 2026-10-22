module

public import VerifiedGarbage.Proof.Sm4.X86.Ctr32Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Frame
import VerifiedGarbage.Proof.Sm4.X86.Ctr32Lit

/-! # SM4-GCM on baseline x86 (32-bit): its counter mode and key setup

The functions that call GHASH are registered for each of its
implementations in `Generic/Sm4Gcm/X86/Sm4Gcm.lean`. -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.X86

def artifacts : List Artifact := [
  Spec.Sm4.ctr32Api.artifact X86.target {
    notes := ["Baseline IA-32: `vg_sm4_ctr`'s code (in-place XOR, with each counter block encrypted by the bitsliced SM4 core in general-purpose registers, with no table lookups; the round keys' table built once per call, by `vg_sm4_prepare_keys`, and each batch encrypted by `vg_sm4_crypt_prepared`, one block per batch of eight used) with GCM's `inc₃₂` on the counter: only its last 32-bit word, byte-swapped, incremented and swapped back."]
    code := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ctr32
    stack := 1516
    verified := Proof.Sm4.X86.Ctr32.ctr32_framed },
  Spec.Sm4.Gcm.initApi.artifact X86.target {
    notes := ["This implementation calls `vg_sm4_expand_key` for the key schedule, then `vg_sm4_ctr32` for the hash subkey, with the arguments it keeps in the working space."]
    code := Impl.StackScratch.X86.withStackScratch 2576 2 Impl.Sm4Gcm.X86.init
    stack := 4112
    verified := Proof.Sm4Gcm.X86.init_framed
    spSafe := Proof.AesGcm.X86.withStackScratch_spSafe Proof.Sm4Gcm.X86.init_spSafe }]

end VG.Artifacts.Sm4Gcm.X86
