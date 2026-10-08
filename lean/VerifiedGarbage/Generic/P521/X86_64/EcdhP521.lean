import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P521.X86_64
import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Verified
import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Lit
import VerifiedGarbage.Proof.Ecdh.X86_64.P521.VerifiedAdx
import VerifiedGarbage.Proof.Ecdh.X86_64.P521.LitAdx

/-!
# ECDH over P-521 (SP 800-56A) on x86-64

A generic file (see `TCB/Emit.lean`) over P-521's group law and
inversions `h`, the variant
`Variants/P521/X86_64/Law.lean`, for each multiplication modulo `p`: the
baseline's, and BMI2's and ADX's (`_adx`).
-/

namespace VG.Generic.P521.X86_64.EcdhP521

/-- The function of `Spec.Ecdh.P521.exchangeApi`, multiplying modulo `p` with
BMI2 and ADX (`adx`, `_adx`) or not: its `code`, proven (`hv`), with no
instruction writing `rsp` (`hsp`). -/
def exchange (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst X86_64.abi))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true) : Artifact :=
  { Spec.Ecdh.P521.exchangeApi with
    name := Spec.Ecdh.P521.exchangeApi.name ++ (if adx then "_adx" else "")
    target := X86_64.target
    doc := Spec.Ecdh.P521.exchangeApi.doc (notes := ["The function is `vg_ecdsa_p521_sign" ++ (if adx then "_adx" else "") ++ "`'s setup, \
      field arithmetic and inversion, with the peer's point in place of `G`: it saves its \
      caller's callee-saved registers in `scratch`; field elements are nine 64-bit words in \
      Montgomery form, " ++ Proof.Ecdsa.X86_64.P521.mulNote adx ++ ". The peer's key is checked without branches (its first byte, both \
      coordinates below `p`, and the curve's equation), and `[d]P` is computed for the peer's \
      point if it is valid, else `G`, so it always runs on a point of the curve. `[d]P` is by \
      signed 4-bit windows: `d` (below `2^521`) is recoded as `d + 8 Σ_{j<131} 16^j`, whose 131 \
      nibbles less 8 are digits in `[-8, 7]`; a table of `[1 … 8]P` is built in `scratch` by \
      complete additions and stored in Jacobian coordinates; then, from the point at infinity, \
      for each digit from the top, four doublings in Jacobian coordinates (dbl-2001-b, for \
      `a = -3`) and the addition of the digit's entry, selected in constant time by loading all \
      eight entries, 16 bytes at a time (each entry's 27 words as 14 pieces, the last two \
      overlapping by a word), and keeping (`pand`, `por`) the one of the digit's magnitude, and \
      negated by a mask of its sign. For every digit but the last the addition is in Jacobian \
      coordinates (add-1998-cmo-2), whose result is kept unless the accumulator or the entry is \
      the point at infinity (selected by masks of their `Z`): every point of P-521 has order \
      `n`, so the operands are never equal or opposite otherwise; the last digit's is by the \
      complete addition formulas of Renes, Costello and Batina for `a = -3` (Algorithm 4), in \
      projective coordinates. `Z⁻¹` is by the signature's divsteps. The result (or zeros) is selected by a mask of the checks, `d` \
      in `[1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    code
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst X86_64.abi
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx"] else [] }

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P521.curve) : List Artifact := [
  exchange false Impl.Ecdh.X86_64.exchangeP521
    (Proof.Ecdh.X86_64.P521.ecdh_verified h.law h.inv h.prime) (Code.all_of_allInstrs (by lit_decide)),
  exchange true Impl.Ecdh.X86_64.exchangeP521Adx
    (Proof.Ecdh.X86_64.P521.ecdh_verified_adx h.law h.inv h.prime) (Code.all_of_allInstrs (by lit_decide))]

end VG.Generic.P521.X86_64.EcdhP521
