module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Impl.Scrypt.X86_64.Salsa
import VerifiedGarbage.Impl.Scrypt.X86_64.BlockMix
public import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix
import VerifiedGarbage.Proof.Scrypt.X86_64.FusedVerified
public import VerifiedGarbage.Proof.Scrypt.X86_64.DirectFill
import VerifiedGarbage.Proof.Scrypt.X86_64.Salsa
public import VerifiedGarbage.Proof.Scrypt.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# scrypt (RFC 7914): Salsa20/8, scryptBlockMix and scryptROMix on x86-64
-/

@[expose] public section

namespace VG.Artifacts.Scrypt.X86_64

def artifacts : List Artifact := [
  Spec.Scrypt.salsaApi.artifact X86_64.target {
    notes := ["The scalar rounds interleave four independent quarter-round chains."]
    code := Impl.Scrypt.X86_64.salsa
    verified := Proof.Scrypt.X86_64.salsa_verified },
  Spec.Scrypt.blockMixApi.artifact X86_64.target {
    notes := ["The fused scalar BlockMix loop retains Salsa20/8 state between input blocks."]
    code := Impl.Scrypt.X86_64.blockMixFused
    stack := 8
    verified := Proof.Scrypt.X86_64.BlockMix.Fused.blockMix_verified },
  Spec.Scrypt.roMixApi.artifact X86_64.target {
    notes := ["ROMix uses SSE2 memory loops, direct table filling, and a fused scalar BlockMix loop."]
    code := Impl.Scrypt.X86_64.roMixDirect
    stack := 16
    verified := Proof.Scrypt.X86_64.RoMix.DirectFill.roMix_verified }]

end VG.Artifacts.Scrypt.X86_64
