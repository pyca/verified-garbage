module
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.InverseCfgLit

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.InverseVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.InverseLit
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-521's inversions modulo `p` and `n` on x86-64

`vg_p521_inv_mod_p` and `vg_p521_inv_mod_n` (`Spec/Weierstrass/Inverse.lean`),
which the signature, the public key derivation, verification and ECDH call,
and their `_adx` forms with BMI2's and ADX's products. A generic file (see
`TCB/Emit.lean`) over P-521's group law and inversions `h`, the variant
`Variants/P521/X86_64/Law.lean`, whose inversions' soundness the proofs take.
-/

@[expose] public section

namespace VG.Generic.P521.X86_64.InverseP521

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P521.Inverse

/-- What the functions run. -/
def note (adx : Bool) (mod : String) : String :=
  "The function keeps `rbx`, `rbp` and `r12`–`r15` in bytes 2224 to 2295 of `ws` (slot 30) while \
  it runs, and computes the inverse modulo `" ++ mod ++ "` by Bernstein and Yang's divsteps, in \
  batches of 59 (23 batches for nine words), each run on the low words of `f` and `g` packed into \
  64-bit registers and applied to `f`, `g` and the numbers `d`, `e` by the batch's matrix, in its \
  working area at bytes 5056 to 5695, then multiplies by a constant (`2^(5 B) R³ mod " ++ mod ++
  "`) to return to Montgomery form, by the signature's Montgomery multiplication modulo `" ++ mod ++
  "`" ++ (if adx then ", with BMI2 and ADX" else "") ++
  "; nothing depends on the numbers but through masks and `cmov`."

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P521.curve) : List Artifact :=
  ([false, true].map fun adx =>
    C.invPApi.artifact X86_64.target {
      suffix := (if adx then "_adx" else "")
      notes := [note adx "p"]
      code := (cfg adx).invFn (cfg adx).pPowI
      verified := p_verified h.inv adx
      features := if adx then ["bmi2", "adx"] else [] }) ++
  ([false].map fun adx =>
    C.invNApi.artifact X86_64.target {
      suffix := (if adx then "_adx" else "")
      notes := [note adx "n"]
      code := (cfg adx).invFn (cfg adx).nPowI
      verified := n_verified h.inv adx
      features := [] })

end VG.Generic.P521.X86_64.InverseP521
