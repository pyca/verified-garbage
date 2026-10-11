import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.MulBaseVerified

/-!
# P-384's base point multiplication on x86-64

`vg_p384_mul_base` (`Spec/Weierstrass/MulBase.lean`), which the signature
and the public key derivation call, and its `_adx` form with BMI2's and
ADX's products and AVX2's selection. A generic file (see `TCB/Emit.lean`)
over P-384's group law and inversions `h`, the variant
`Variants/P384/X86_64/Law.lean`: the comb's proof takes the group law, and
the curve's facts (`p384_ok`) its inversions.
-/

namespace VG.Generic.P384.X86_64.MulBaseP384

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P384.MulBase

/-- What the function runs. -/
def note (adx : Bool) : String :=
  "The function keeps `rbx`, `rbp` and `r12`–`r15` in bytes 1456 to 1503 of `ws` (slot 29) while \
  it runs, expands `k` into a table of its bits, one per byte, at bytes 2224 to 2607, and runs the \
  fixed-base comb of `vg_ecdsa_p384_sign" ++ (if adx then "_adx" else "") ++ "`: field elements \
  are six 64-bit words in Montgomery form, multiplied modulo `p` in the code itself (no calls), " ++
  (if adx then "by rows of BMI2's `mulx` with ADX's two carry chains (`adcx`, `adox`)"
    else "by `mul` and word-by-word Montgomery reduction") ++ "; the 55 windows `k_j` of `k`'s \
  bits are digits `k_j - 64` from `-64` to `63`, `[k]G = [64 Σ 2^(7j)]G + Σ [(k_j - 64) 2^(7j)]G`, \
  from 55 tables of `[m 2^(7j)]G` (`m = 1 … 64`, affine, in Montgomery form) in the static \
  `VG_P384_COMB` (330 KB), with no doublings: each entry is selected in constant time by loading \
  every entry of its table, " ++ Proof.Ecdsa.X86_64.P384.selNote adx ++ " the one of the digit's \
  magnitude (or the point at infinity for a zero digit), negated by a mask of its sign, and added \
  by the mixed complete addition formulas of Renes, Costello and Batina for `a = -3` (Algorithm 5: \
  the entry's `Z` is 1), the sum replacing the accumulator unless the digit is zero."

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P384.curve) : List Artifact :=
  [false, true].map fun adx =>
    { C.mulBaseApi with
      name := C.mulBaseApi.name ++ (if adx then "_adx" else "")
      target := X86_64.target
      doc := C.mulBaseApi.doc (notes := [note adx])
      consts := p384.combConsts
      code := (cfg adx).mulBaseFn
      contract := C.mulBaseContract (X86_64.abi.withConsts p384.combConsts)
      verified := mb_verified h.law (Proof.P384.combOk7 h.law) h.inv adx
      spSafe := by cases adx <;> exact Code.all_of_allInstrs (by lit_decide)
      features := if adx then ["bmi2", "adx", "avx", "avx2"] else [] }

end VG.Generic.P384.X86_64.MulBaseP384
