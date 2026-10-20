module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.InverseVerified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.InverseLit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-192's inversions modulo `p` and `n` on x86-64

`vg_p192_inv_mod_p` and `vg_p192_inv_mod_n` (`Spec/Weierstrass/Inverse.lean`),
which the signature, the public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-192's group law and inversions `h`, the variant
`Variants/P192/X86_64/Law.lean`, whose inversions' soundness the proofs take.
-/

@[expose] public section

namespace VG.Generic.P192.X86_64.InverseP192

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P192.Inverse

/-- What the functions run. -/
def note (adx : Bool) (mod : String) : String :=
  "The function keeps `rbx`, `rbp` and `r12`–`r15` in `xmm0` to `xmm5` while it runs, and \
  computes the inverse modulo `" ++ mod ++ "` by Bernstein and Yang's divsteps, in batches of 59 \
  (10 batches for four words), each run on the low words of `f` and `g` packed into 64-bit \
  registers and applied to `f`, `g` and the numbers `d`, `e` by the batch's matrix, in its working \
  area at bytes 2296 to 2615, then multiplies by a constant (`2^(5 B) R³ mod " ++ mod ++
  "`) to return to Montgomery form, " ++
  (if adx then "by rows of BMI2's `mulx` with ADX's two carry chains (`adcx`, `adox`)"
    else "by `mul` and word-by-word Montgomery reduction") ++
  "; nothing depends on the numbers but through masks and `cmov`."

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P192.curve) : List Artifact :=
  ([false].map fun adx =>
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
      features := if adx then ["bmi2", "adx"] else [] })

end VG.Generic.P192.X86_64.InverseP192
