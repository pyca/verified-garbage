module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Impl.Poly1305.AArch64.Radix64
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Blocks
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Finalize
public import VerifiedGarbage.Proof.Poly1305.AArch64.Init
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Update
public import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Update
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Lit
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Frame
import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Finish
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Poly1305 (RFC 8439 §2.5) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Poly1305.AArch64

def artifacts : List Artifact := [
  Spec.Poly1305.initApi.artifact AArch64.target {
    code := Impl.Poly1305.AArch64.init
    verified := Proof.Poly1305.AArch64.init_verified },
  Spec.Poly1305.blocksApi.artifact AArch64.target {
    code := Impl.Poly1305.AArch64.Radix64.blocks
    verified := Proof.Poly1305.AArch64.Radix64.blocks_verified },
  Spec.Poly1305.updateApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 128 .x4 Impl.Poly1305.AArch64.Radix64.update
    stack := 128
    verified := Proof.Poly1305.AArch64.Radix64.update_framed },
  Spec.Poly1305.updateApi.artifact AArch64.target {
    suffix := "_neon"
    notes := ["This implementation absorbs the whole blocks of data of at \
      least 128 bytes four at a time in NEON (AdvSIMD), and the rest one at a time. It is faster than \
      `vg_poly1305_update` on Apple's cores, and slower on Arm's Neoverse N2, whose two vector pipelines \
      the multiplications saturate."]
    code := Impl.StackScratch.AArch64.withStackScratch 128 .x4 Impl.Poly1305.AArch64.Vector.update
    stack := 128
    verified := Proof.Poly1305.AArch64.Vector.update_framed },
  Spec.Poly1305.finalizeApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 128 .x3 Impl.Poly1305.AArch64.Radix64.finalize
    stack := 128
    verified := Proof.Poly1305.AArch64.Radix64.finalize_framed },
  Spec.Poly1305.finalizeScratchApi.artifact AArch64.target {
    code := Impl.Poly1305.AArch64.Radix64.finalize
    verified := Proof.Poly1305.AArch64.Radix64.finalize_verified }]

end VG.Artifacts.Poly1305.AArch64
