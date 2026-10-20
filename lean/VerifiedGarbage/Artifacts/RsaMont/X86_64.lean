module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxVerified
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery multiplication in the RSA working space, as a function, on x86-64 -/

@[expose] public section

namespace VG.Artifacts.RsaMont.X86_64

def artifacts : List Artifact := [
  Spec.Rsa.Mont.mulApi.artifact X86_64.target {
    notes := ["Baseline x86-64: coarsely integrated operand scanning (CIOS) on 64-bit words, the \
        accumulator in array 2, then a subtraction of `m` into array 3 selected by a mask, as the \
        RSA functions' Montgomery multiplication. It uses no stack: it keeps `rbx`, `rbp` and \
        `r12`–`r15` in `xmm0`–`xmm2` and restores them through the first words of arrays 2 and 3, \
        which hold them on return."]
    code := Impl.Bignum.X86_64.MontFn.mulBase
    verified := Proof.Bignum.X86_64.MontFn.fn_verified },
  Spec.Rsa.Mont.mulApi.artifact X86_64.target {
    suffix := "_adx"
    notes := ["For `w` a multiple of 8 (below 2^30 + 8), BMI2 and ADX: the product by \
        8-by-8 tiles of `mulx` with two carry chains (`adcx`, `adox`), or, when `a = b`, the square \
        by triangular tiles computing each cross product once; then a word-by-word reduction and \
        the selected subtraction of `m`, eight words per iteration, with the borrow and the mask \
        moved between `rbp` and the carry flag once per eight words and the selection by `cmovb`. \
        Other sizes take `vg_rsa_mont_mul`'s code. The tiles read \
        their operands' addresses from header words 16–18, which the function sets from `o`, `a` \
        and `b` and, with words 19–21, restores before it returns. It uses no stack: it keeps \
        `rbx`, `rbp` and `r12`–`r15` in `xmm0`–`xmm2`."]
    code := Impl.Bignum.X86_64.MontFn.mulAdx
    verified := Proof.Bignum.X86_64.MontFn.fnAdx_verified
    features := ["bmi2", "adx"] },
  Spec.Rsa.Mont.mulLazyApi.artifact X86_64.target {
    notes := ["Baseline x86-64: `vg_rsa_mont_mul`'s code. Its subtraction of `m` when it does not \
        borrow leaves a result below `2^(64 w)` for any operands below `2^(64 w)`."]
    code := Impl.Bignum.X86_64.MontFn.mulBase
    verified := Proof.Bignum.X86_64.MontFn.fnLazy_verified },
  Spec.Rsa.Mont.mulLazyApi.artifact X86_64.target {
    suffix := "_adx"
    notes := ["For `w` a multiple of 8 (below 2^30 + 8), BMI2 and ADX: `vg_rsa_mont_mul_adx`'s tiles \
        and reduction, then, in one pass, the subtraction of `m` masked by the reduction's top word \
        (four words of `m` masked per group, with the borrow moved between `rbp` and the carry flag \
        once per group), rather than a subtraction and a selection. Other sizes take \
        `vg_rsa_mont_mul`'s code. It uses no stack: it keeps `rbx`, `rbp` and `r12`–`r15` in \
        `xmm8`–`xmm13`."]
    code := Impl.Bignum.X86_64.MontFn.mulAdxLazy
    verified := Proof.Bignum.X86_64.MontFn.fnAdxLazy_verified
    features := ["bmi2", "adx"] }]

end VG.Artifacts.RsaMont.X86_64
