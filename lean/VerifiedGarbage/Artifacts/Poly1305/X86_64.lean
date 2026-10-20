module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Init
import VerifiedGarbage.Proof.Poly1305.X86_64.Lit
public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Blocks
public import VerifiedGarbage.Proof.Poly1305.X86_64.Frame
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Lit
import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Lit

/-!
# Poly1305 (RFC 8439 §2.5) on x86-64

`vg_poly1305_update` calls an implementation of `vg_poly1305_blocks`, and is
in the generic file `Generic/Poly1305Blocks/X86_64/Poly1305.lean`, emitted
once for each.
-/

@[expose] public section

namespace VG.Artifacts.Poly1305.X86_64

def artifacts : List Artifact := [
  Spec.Poly1305.initApi.artifact X86_64.target {
    code := Impl.Poly1305.X86_64.init
    verified := Proof.Poly1305.X86_64.init_verified },
  Spec.Poly1305.blocksApi.artifact X86_64.target {
    code := Impl.Poly1305.X86_64.blocks
    verified := Proof.Poly1305.X86_64.blocks_verified },
  Spec.Poly1305.blocksApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["With AVX2: four blocks at a time, in four \
      interleaved Horner evaluations, once there are at least 32 blocks; fewer, and the last \
      `n mod 4`, with `vg_poly1305_blocks`. It sets MXCSR to Intel's value for data \
      operand-independent timing (`0x1FBF`) around its `vpmuludq`s, and restores it."]
    code := Impl.Poly1305.X86_64.Avx2.blocksAvx2
    stack := 8
    verified := Proof.Poly1305.X86_64.Avx2.blocksAvx2_verified
    features := ["avx", "avx2"] },
  Spec.Poly1305.blocksApi.artifact X86_64.target {
    suffix := "_avx512"
    notes := ["With AVX-512F: eight blocks at a time, in eight \
      interleaved Horner evaluations in the quadwords of `zmm` registers, once there are at least 40 \
      blocks; fewer with `vg_poly1305_blocks_avx2`, and the last `n mod 8` with `vg_poly1305_blocks`. \
      It sets MXCSR to Intel's value for data operand-independent timing (`0x1FBF`) around its \
      `vpmuludq`s, and restores it."]
    code := Impl.Poly1305.X86_64.Avx512.blocksAvx512
    stack := 16
    verified := Proof.Poly1305.X86_64.Avx512.blocksAvx512_verified
    features := ["avx", "avx512f", "avx2"] },
  Spec.Poly1305.blocksApi.artifact X86_64.target {
    suffix := "_ifma"
    notes := ["With AVX-512 IFMA: eight blocks at a time, in eight \
      interleaved Horner evaluations in the quadwords of `zmm` registers, as three limbs of 44 bits \
      multiplied with `vpmadd52luq` and `vpmadd52huq`, once there are at least 28 blocks; fewer with \
      `vg_poly1305_blocks_avx2`, and the last `n mod 8` with `vg_poly1305_blocks`. It sets MXCSR to \
      Intel's value for data operand-independent timing (`0x1FBF`) around its multiply-adds, and \
      restores it."]
    code := Impl.Poly1305.X86_64.Ifma.blocksIfma
    stack := 16
    verified := Proof.Poly1305.X86_64.Ifma.blocksIfma_verified
    features := ["avx", "avx512f", "avx2", "avx512ifma"] },
  Spec.Poly1305.finalizeApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 136 .rcx Impl.Poly1305.X86_64.finalize
    stack := 136
    verified := Proof.Poly1305.X86_64.finalize_framed },
  Spec.Poly1305.finalizeScratchApi.artifact X86_64.target {
    code := Impl.Poly1305.X86_64.finalize
    verified := Proof.Poly1305.X86_64.finalize_verified }]

end VG.Artifacts.Poly1305.X86_64
