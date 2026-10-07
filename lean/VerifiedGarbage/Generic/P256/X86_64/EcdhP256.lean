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
      signed 4-bit windows: `d` is recoded as `d + 8 Σ_{j<65} 16^j`, whose 65 nibbles less 8 \
      are digits in `[-8, 7]`; a table of `[1 … 8]P` is built in `scratch` by complete \
      additions; then, from the point at infinity, for each digit from the top, four doublings \
      in Jacobian coordinates (dbl-2001-b, for `a = -3`) and the addition of the digit's entry, \
      selected in constant time by loading all eight entries, 16 bytes at a time, and keeping \
      (`pand`, `por`) the one of the digit's magnitude, and negated by a mask of its sign, by \
      the complete addition formulas of Renes, Costello and Batina for `a = -3` (Algorithm 4); \
      `Z⁻¹` is by the signature's divsteps. The result (or zeros) is selected by a mask of the \
      checks, `d` in `[1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    code
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst X86_64.abi
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx"] else [] }

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P256.curve) : List Artifact := [
  exchange false Impl.Ecdh.X86_64.exchangeP256
    (Proof.Ecdh.X86_64.ecdh_verified h.law h.inv h.prime) (Code.all_of_allInstrs (by lit_decide)),
  exchange true Impl.Ecdh.X86_64.exchangeP256Adx
    (Proof.Ecdh.X86_64.ecdh_verified_adx h.law h.inv h.prime) (Code.all_of_allInstrs (by lit_decide))]

end VG.Generic.P256.X86_64.EcdhP256
