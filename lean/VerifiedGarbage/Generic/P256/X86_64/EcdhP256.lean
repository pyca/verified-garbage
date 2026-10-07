import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Impl.Ecdh.P256.X86_64
import VerifiedGarbage.Proof.Ecdh.X86_64.Verified
import VerifiedGarbage.Proof.Ecdh.X86_64.Lit
import VerifiedGarbage.Proof.Ecdh.X86_64.VerifiedAdx
import VerifiedGarbage.Proof.Ecdh.X86_64.LitAdx

/-!
# ECDH over P-256 (SP 800-56A) on x86-64

A generic file (see `TCB/Emit.lean`) over P-256's group law,
inversions and prime order `h`, the variant `Variants/P256/X86_64/Law.lean`, for each
multiplication: the baseline's, and BMI2's and ADX's (`_adx`).
-/

namespace VG.Generic.P256.X86_64.EcdhP256

/-- The function of `Spec.Ecdh.P256.exchangeApi`, multiplying with BMI2 and ADX
(`adx`, `_adx`) or not: its `code`, proven (`hv`), with no instruction writing
`rsp` (`hsp`). -/
def exchange (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst X86_64.abi))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true) : Artifact :=
  { Spec.Ecdh.P256.exchangeApi with
    name := Spec.Ecdh.P256.exchangeApi.name ++ (if adx then "_adx" else "")
    target := X86_64.target
    doc := Spec.Ecdh.P256.exchangeApi.doc (notes := ["The function is `vg_ecdsa_p256_sign" ++ (if adx then "_adx" else "") ++ "`'s setup, \
      field arithmetic and inversion, with the peer's point in place of `G`: it saves its \
      caller's callee-saved registers in `scratch`; field elements are four 64-bit words in \
      Montgomery form, " ++ Proof.Ecdsa.X86_64.mulNote adx ++ ". The peer's key is checked without branches (its first byte, both \
      coordinates below `p`, and the curve's equation), and `[d]P` is computed for the peer's \
      point if it is valid, else `G`, so it always runs on a point of the curve. `[d]P` is by \
      signed 5-bit windows in Jacobian coordinates, P-256 having prime order: `d` is recoded as \
      `d + 16 Σ_{j<52} 32^j`, whose 52 5-bit windows less 16 are digits in `[-16, 15]`; a table \
      of `[1 … 16]P`, each entry with its `Z²` and `Z³`, is built in `scratch` by a doubling and \
      mixed additions; then, from the point at infinity, for each digit from the top, five \
      doublings in Jacobian coordinates for `a = -3` (with a halving modulo `p` in place of \
      multiplications by small constants) and the addition of the digit's entry, selected in \
      constant time by loading all sixteen entries, " ++
      (if adx then "32 bytes at a time with AVX2" else "16 bytes at a time") ++
      ", and keeping (by masks) the one of the digit's magnitude, its `y` negated by a mask of its \
      sign, by Jacobian addition with the entry's `Z²` and `Z³`, whose exceptional cases (equal \
      or opposite points) do not arise for `d < n`; the sum is kept, by masks, unless the digit \
      is zero, and the entry in its place where the accumulator is the point at infinity; \
      `Z⁻¹` is by the signature's divsteps. The result (or zeros) is selected by a mask of the \
      checks, `d` in `[1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    code
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst X86_64.abi
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx", "avx", "avx2"] else [] }

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P256.curve) : List Artifact := [
  exchange false Impl.Ecdh.X86_64.exchangeP256
    (Proof.Ecdh.X86_64.ecdh_verified h.law h.inv h.prime) (Code.all_of_allInstrs (by lit_decide)),
  exchange true Impl.Ecdh.X86_64.exchangeP256Adx
    (Proof.Ecdh.X86_64.ecdh_verified_adx h.law h.inv h.prime) (Code.all_of_allInstrs (by lit_decide))]

end VG.Generic.P256.X86_64.EcdhP256
