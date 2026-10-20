module

import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.Lit
public import VerifiedGarbage.Proof.Gcm.X86_64.Ghash
public import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Ghash
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Ok
public import VerifiedGarbage.Proof.Framework.Registration

/-! # GHASH on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Gcm.X86_64

def artifacts : List Artifact := [
  Spec.Gcm.ghashApi.artifact X86_64.target {
    notes := ["The carry-less products are computed with integer multiplications (`mul`) of \
        operands with \"holes\" (every fourth bit), which keep the carries away from the bits of \
        the result, as in BearSSL's `ghash_ctmul64` (Thomas Pornin, MIT licence): three 64-bit \
        products per block (Karatsuba) by `x⁻¹ · H`, computed once, and a reduction by shifts \
        and XORs, in GCM's bit-reflected order."]
    code := Impl.Gcm.X86_64.ghash
    verified := Proof.Gcm.X86_64.ghash_verified },
  Spec.Gcm.ghashApi.artifact X86_64.target {
    suffix := "_pclmul"
    notes := ["Uses PCLMULQDQ: four blocks at a time, with `H²`, `H³` and `H⁴` computed on \
        each call."]
    code := Impl.Gcm.X86_64.Pclmul.ghash
    verified := Proof.Gcm.X86_64.Pclmul.ghash_verified
    features := ["pclmulqdq", "ssse3"] },
  Spec.Gcm.ghashApi.artifact X86_64.target {
    suffix := "_vpclmul"
    notes := ["Uses VPCLMULQDQ: with eight blocks or more, eight blocks at a time, two in each \
        256-bit register, with `H²` to `H⁸` computed on each call and one reduction per eight \
        blocks; the blocks left go four and then one at a time with PCLMULQDQ, as in \
        `vg_ghash_pclmul`."]
    code := Impl.Gcm.X86_64.Vpclmul.ghash
    verified := Proof.Gcm.X86_64.Vpclmul.ghash_verified
    features := ["avx", "avx2", "pclmulqdq", "ssse3", "vpclmulqdq"] },
  Spec.Gcm.prepareApi.artifact X86_64.target {
    suffix := "_vpclmul"
    notes := ["Uses VPCLMULQDQ: `H'`–`H'¹⁶` as the stitched loops on 256-bit registers compute \
        them, two in each register, already prepared, then each pair times `H'¹⁶` twice, eight \
        independent multiplications at a time, for `H'¹⁷`–`H'⁴⁸`. No calls and no stack."]
    code := Impl.Gcm.X86_64.Prepare.prepare
    verified := Proof.Gcm.X86_64.Prepare.prepare_verified
    features := ["avx", "avx2", "pclmulqdq", "ssse3", "vpclmulqdq"] },
  Spec.Gcm.prepareApi.artifact X86_64.target {
    suffix := "_pclmul_avx"
    notes := ["Uses PCLMULQDQ on 128-bit registers: `H'`–`H'⁸` as the eight-block loops compute \
        them, already prepared, then each times `H'⁸` five times, eight independent \
        multiplications at a time, for `H'⁹`–`H'⁴⁸`. No calls and no stack."]
    code := Impl.Gcm.X86_64.PrepareAvx.prepare
    verified := Proof.Gcm.X86_64.PrepareAvx.prepare_verified
    features := ["avx", "pclmulqdq"] }]

end VG.Artifacts.Gcm.X86_64
