import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.P521.Comb7
import VerifiedGarbage.Impl.EcKey.P521.X86_64
import VerifiedGarbage.Proof.EcKey.X86_64.P521.Verified
import VerifiedGarbage.Proof.EcKey.X86_64.P521.Lit
import VerifiedGarbage.Proof.EcKey.X86_64.P521.VerifiedAdx
import VerifiedGarbage.Proof.EcKey.X86_64.P521.LitAdx

/-!
# P-521 public keys (FIPS 186-5 §A.2) on x86-64

A generic file (see `TCB/Emit.lean`) over P-521's group law and
inversions `h`, the variant
`Variants/P521/X86_64/Law.lean`, for each multiplication modulo `p`: the
baseline's, and BMI2's and ADX's (`_adx`).
-/

namespace VG.Generic.P521.X86_64.EcP521

/-- The function of `Spec.EcKey.P521.publicKeyApi`, multiplying modulo `p` with
BMI2 and ADX (`adx`, `_adx`) or not: its `code`, proven (`hv`), with no
instruction writing `rsp` (`hsp`). -/
def publicKey (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.EcKey.P521.inst.publicKeyContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p521.combConsts)))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true) : Artifact :=
  { Spec.EcKey.P521.publicKeyApi with
    name := Spec.EcKey.P521.publicKeyApi.name ++ (if adx then "_adx" else "")
    target := X86_64.target
    doc := Spec.EcKey.P521.publicKeyApi.doc (notes := ["The function is `vg_ecdsa_p521_sign" ++
      (if adx then "_adx" else "") ++ "`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves its caller's callee-saved registers in `scratch`; field elements are nine 64-bit \
      words in Montgomery form, " ++ Proof.Ecdsa.X86_64.P521.mulNote adx ++ "; `[d]G` is the \
      signature's comb over the 7-bit windows of `d`, from the static `VG_P521_COMB`; and `Z⁻¹` is \
      by divsteps (Bernstein and Yang's safegcd, half-delta form): 23 \
      batches of 59 divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), each \
      giving a matrix of 64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the \
      coefficients `a`, `b` (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 1357 \
      divsteps in all, enough for 576-bit moduli by Bernstein and Yang's bound (which the proof \
      checks); then `f = ±1`, and `Z⁻¹` is `a` times a constant or its negation by `f`'s sign. \
      The number of steps is fixed, so the time does not depend on `Z`. The result (or zeros) is \
      selected by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the \
      pointers."])
    consts := Impl.Ecdsa.X86_64.p521.combConsts
    code
    contract := Spec.EcKey.P521.inst.publicKeyContract
      (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p521.combConsts)
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx"] else [] }

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P521.curve) : List Artifact := [
  publicKey false Impl.EcKey.X86_64.publicKeyP521
    (Proof.EcKey.X86_64.P521.pk_verified h.law (Proof.P521.combOk7 h.law) h.inv) (Code.all_of_allInstrs (by lit_decide)),
  publicKey true Impl.EcKey.X86_64.publicKeyP521Adx
    (Proof.EcKey.X86_64.P521.pk_verified_adx h.law (Proof.P521.combOk7 h.law) h.inv) (Code.all_of_allInstrs (by lit_decide))]

end VG.Generic.P521.X86_64.EcP521
