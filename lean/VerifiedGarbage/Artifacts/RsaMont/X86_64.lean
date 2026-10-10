import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxVerified

/-! # Montgomery multiplication in the RSA working space, as a function, on x86-64 -/

namespace VG.Artifacts.RsaMont.X86_64

def artifacts : List Artifact := [
  { Spec.Rsa.Mont.mulApi with
    target := X86_64.target
    doc := Spec.Rsa.Mont.mulApi.doc
      (notes := ["Baseline x86-64: coarsely integrated operand scanning (CIOS) on 64-bit words, the \
        accumulator in array 2, then a subtraction of `m` into array 3 selected by a mask, as the \
        RSA functions' Montgomery multiplication. It uses no stack: it keeps `rbx`, `rbp` and \
        `r12`–`r15` in `xmm0`–`xmm2` and restores them through the first words of arrays 2 and 3, \
        which hold them on return."])
    code := Impl.Bignum.X86_64.MontFn.mulBase
    contract := Spec.Rsa.Mont.mulContract X86_64.abi
    verified := Proof.Bignum.X86_64.MontFn.fn_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Rsa.Mont.mulApi with
    target := X86_64.target
    name := "vg_rsa_mont_mul_adx"
    doc := Spec.Rsa.Mont.mulApi.doc
      (notes := ["For `w` a multiple of 8 (below 2^30 + 8), BMI2 and ADX: the product by \
        8-by-8 tiles of `mulx` with two carry chains (`adcx`, `adox`), or, when `a = b`, the square \
        by triangular tiles computing each cross product once; then the reduction by a row per \
        word, each row adding the word's multiple of `m` by blocks of eight words with the same \
        two carry chains, and \
        the selected subtraction of `m`, eight words per iteration, with the borrow and the mask \
        moved between `rbp` and the carry flag once per eight words and the selection by `cmovb`. \
        Other sizes take `vg_rsa_mont_mul`'s code. The tiles read \
        their operands' addresses from header words 16–18, which the function sets from `o`, `a` \
        and `b` and, with words 19–21, restores before it returns. It uses no stack: it keeps \
        `rbx`, `rbp` and `r12`–`r15` in `xmm0`–`xmm2`."])
    code := Impl.Bignum.X86_64.MontFn.mulAdx
    contract := Spec.Rsa.Mont.mulContract X86_64.abi
    verified := Proof.Bignum.X86_64.MontFn.fnAdx_verified
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.RsaMont.X86_64
