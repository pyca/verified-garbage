module

public import VerifiedGarbage.Proof.Ecdh.X86_64.Secp256k1.CheckVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# secp256k1's check of a public point on x86-64

`vg_secp256k1_check_point` (`Spec/Weierstrass/CheckPoint.lean`), which ECDH and
verification call. A generic file (see `TCB/Emit.lean`) over secp256k1's group law and inversions
`h`, the variant `Variants/Secp256k1/X86_64/Law.lean`, whose inversions'
soundness the proofs of the configuration take.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.X86_64.CheckPointSecp256k1

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64.Secp256k1.Check

/-- What the function runs. -/
def note (adx : Bool) : String :=
  "The function keeps `rbx`, `rbp` and `r12`–`r15` in `xmm0` to `xmm5` while it runs. It \
  compares `x` and `y` with `p` by subtraction with borrow, takes them into Montgomery's form \
  and computes `y² - (x³ + a x + b)` modulo `p` " ++
  (if adx then "by rows of BMI2's `mulx` with ADX's two carry chains (`adcx`, `adox`)"
    else "by `mul` and word-by-word Montgomery reduction") ++
  ", and selects the point by masks; nothing depends on the numbers but through masks."

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.Secp256k1.curve) : List Artifact :=
  [false].map fun adx =>
    C.checkApi.artifact X86_64.target {
      suffix := (if adx then "_adx" else "")
      notes := [note adx]
      code := code adx
      verified := verified h.inv adx
      features := if adx then ["bmi2", "adx"] else [] }

end VG.Generic.Secp256k1.X86_64.CheckPointSecp256k1
