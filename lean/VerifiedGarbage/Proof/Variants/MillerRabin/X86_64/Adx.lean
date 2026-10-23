module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnSpecialized
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxMont
public import VerifiedGarbage.Proof.Bignum.X86_64.Template

/-!
# The BMI2/ADX shared Miller–Rabin round: the variant's code and proofs

The variant `VG.Variants.MillerRabin.X86_64.Adx.variant`
(`Variants/MillerRabin/X86_64/Adx.lean`), with the proofs its interface asks
for. Its callers multiply by calls of `vg_rsa_mont_mul_adx`, rather than
each inlining its unrolled code.
-/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.X86_64.Adx

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

def variant : RoundImpl where
  mont := Mont.fnAdx
  inlineMont := Mont.fnAdxSpecialized
  inlineDepth := by
    intro o a b
    unfold Mont.fnAdxSpecialized
    change (Impl.Bignum.X86_64.MontFnSpecialized.mm o a b).x86_64Depth = 0
    unfold Impl.Bignum.X86_64.MontFnSpecialized.mm
      Impl.Bignum.X86_64.MontFnSpecialized.body Impl.Bignum.X86_64.MontFnSpecialized.tiled
    split <;> rfl
  inlineSafe := by
    intro o a b
    change (Impl.Bignum.X86_64.MontFnSpecialized.mm o a b).allInstrs
      (fun i => !loadsMxcsr i && !isa.writesSp i) = true
    unfold Impl.Bignum.X86_64.MontFnSpecialized.mm
      Impl.Bignum.X86_64.MontFnSpecialized.body Impl.Bignum.X86_64.MontFnSpecialized.tiled
    split <;> rfl
  mm := Impl.Bignum.X86_64.MontFn.call "vg_rsa_mont_mul_adx" Impl.Bignum.X86_64.MontFn.mulAdx
  mmOk := call_inlineOk (by decide +kernel)
  mmInline _ _ _ := rfl
  mxSafe := by decide +kernel
  spSafe := by decide +kernel
  depth := by decide +kernel
  arithDepth := by intro o a b; rfl
  arithSafe := by intro o a b; rfl
  suffix := "_adx"
  features := ["bmi2", "adx"]

end VG.Proof.Variants.MillerRabin.X86_64.Adx
