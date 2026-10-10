import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.X448.X86_64
import VerifiedGarbage.Proof.X448.X86_64.Pow223Verified
import VerifiedGarbage.Proof.X448.X86_64.Lit

/-! # Curve448's addition chain, in radix `2^64`, on x86-64 -/

namespace VG.Artifacts.Gf448R64.X86_64

def artifacts : List Artifact := [
  { Spec.X448.Field64.pow223Api with
    target := X86_64.target
    doc := Spec.X448.Field64.pow223Api.doc (notes := ["Uses baseline integer instructions. The \
      function saves `rbx`, `rbp` and `r12`–`r15` at bytes 1472–1519 of `ws`, in its own working \
      space, and runs X448's addition chain (`Proof/X448/Invert.lean`) on slot 12 with X448's \
      field multiplications: seven 64-bit words multiplied with `mul` by columns (squares \
      computing each cross product once) into the words at byte 1536, reduced with \
      `2^448 = 2^224 + 1` (mod p), the runs of squarings as loops counted by `rbx`."])
    code := Impl.X448.X86_64.pow223Fn
    contract := Spec.X448.Field64.pow223Contract X86_64.abi
    verified := Proof.X448.X86_64.pow223_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Gf448R64.X86_64
