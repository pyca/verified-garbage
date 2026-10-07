import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.P521Field.X86_64.Sqr

/-! # P-521's field multiplication and squaring on x86-64, with BMI2 and ADX -/

namespace VG.Artifacts.P521Field.X86_64

def artifacts : List Artifact := [
  { Spec.P521.mulMontApi with
    target := X86_64.target
    name := "vg_p521_mul_mont_adx"
    doc := Spec.P521.mulMontApi.doc (notes := ["The product by rows with BMI2's `mulx` and \
      ADX's `adcx` and `adox` (two carry chains at once), its low words in `out`, then \
      `2^521 = 1` (mod p) and a final subtraction of `p`. The function saves `rbx`, `rbp` and \
      `r12`–`r15` on the stack."])
    code := Impl.P521Field.X86_64.mulCode
    contract := Spec.P521.mulMontContract X86_64.abi 48
    stack := 48
    verified := Proof.P521Field.X86_64.mul_verified
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.P521.sqrMontApi with
    target := X86_64.target
    name := "vg_p521_sqr_mont_adx"
    doc := Spec.P521.sqrMontApi.doc (notes := ["The products of two different words by rows \
      with BMI2's `mulx` and ADX's `adcx` and `adox`, doubled and the squares added, its low \
      words in `out`, then `2^521 = 1` (mod p) and a final subtraction of `p`. The function \
      saves `rbp` and `r12`–`r15` on the stack."])
    code := Impl.P521Field.X86_64.sqrCode
    contract := Spec.P521.sqrMontContract X86_64.abi 40
    stack := 40
    verified := Proof.P521Field.X86_64.sqr_verified
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.P521Field.X86_64
