import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified

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
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.RsaMont.X86_64
