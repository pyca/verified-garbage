module

public import VerifiedGarbage.Proof.Ecdh.X86_64.BrainpoolP384r1.CheckVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# brainpoolP384r1's check of a public point on x86-64

`vg_brainpoolp384r1_check_point` (`Spec/Weierstrass/CheckPoint.lean`), which ECDH and
verification call. A generic file (see `TCB/Emit.lean`) over brainpoolP384r1's group law and inversions
`h`, the variant `Variants/BrainpoolP384r1/X86_64/Law.lean`, whose inversions'
soundness the proofs of the configuration take.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.X86_64.CheckPointBrainpoolP384r1

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64.BrainpoolP384r1.Check

/-- What the function runs. -/
def note : String :=
  "The function keeps `rbx`, `rbp` and `r12`–`r15` in `xmm0` to `xmm5` while it runs. It \
  compares `x` and `y` with `p` by subtraction with borrow, takes them into Montgomery's form \
  and computes `y² - (x³ + a x + b)` modulo `p` by `mul` and word-by-word Montgomery reduction, \
  and selects the point by masks; nothing depends on the numbers but through masks."

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP384r1.curve) : List Artifact :=
  [C.checkApi.artifact X86_64.target {
      notes := [note]
      code := code
      verified := verified h.inv }]

end VG.Generic.BrainpoolP384r1.X86_64.CheckPointBrainpoolP384r1
