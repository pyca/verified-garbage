module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Impl.Ecdh.P384.X86_64
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.Verified
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.Lit
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.VerifiedAdx
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.LitAdx
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdh.X86_64.P384.LitErase
public import VerifiedGarbage.Proof.Ecdh.X86_64.P384.LitEraseAdx
public import VerifiedGarbage.Spec.Ecdh.P384
public import VerifiedGarbage.Proof.Ecdh.X86_64.P384.Verified
public import VerifiedGarbage.Proof.Ecdh.X86_64.P384.VerifiedAdx
import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.P384.Point
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacField
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacOps
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Proof.Weierstrass.X86_64.DoubleIn
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
public import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJLoop
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJac
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacA
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacStep
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacField
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacOps
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.DoubleIn
import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJLoop
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacStep

/-!
# ECDH over P-384 (SP 800-56A) on x86-64

A generic file (see `TCB/Emit.lean`) over P-384's group law,
inversions and prime order `h`, the variant `Variants/P384/X86_64/Law.lean`, for each
multiplication: the baseline's, and BMI2's and ADX's (`_adx`).
-/

@[expose] public section

namespace VG.Generic.P384.X86_64.EcdhP384

/-- The function of `Spec.Ecdh.P384.exchangeApi`, multiplying with BMI2 and ADX
(`adx`, `_adx`) or not: its `code`, proven (`hv`), with no instruction writing
`rsp` (`hsp`). -/
def exchange (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst X86_64.abi 8))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true := by sp_safe) : Artifact :=
  Spec.Ecdh.P384.exchangeApi.artifact X86_64.target {
    suffix := (if adx then "_adx" else "")
    notes := ["The function is `vg_ecdsa_p384_sign" ++ (if adx then "_adx" else "") ++ "`'s setup, \
      field arithmetic and inversion, with the peer's point in place of `G`: it saves its \
      caller's callee-saved registers in `scratch`; field elements are six 64-bit words in \
      Montgomery form, " ++ Proof.Ecdsa.X86_64.P384.mulNote adx ++ ". The peer's key is checked without branches (its first byte, both \
      coordinates below `p`, and the curve's equation), and `[d]P` is computed for the peer's \
      point if it is valid, else `G`, so it always runs on a point of the curve. `[d]P` is by \
      signed 5-bit windows in Jacobian coordinates, P-384 having prime order: `d` is recoded as \
      `d + 16 Σ_{j<78} 32^j`, whose 78 5-bit windows less 16 are digits in `[-16, 15]`; a table \
      of `[1 … 16]P`, each entry with its `Z²` and `Z³`, is built in `scratch` by a co-Z \
      doubling and co-Z additions (each keeping `P` with the new entry's `Z`); then, from the \
      top digit's entry (the point at infinity for the digit zero), for each further digit, five \
      doublings in place in Jacobian coordinates (dbl-2001-b, for `a = -3`, with the product \
      `2YZ`) and the addition of the digit's entry, selected in constant time by loading all \
      sixteen entries, " ++
      (if adx then "32 bytes at a time with AVX2" else "16 bytes at a time, in two passes") ++
      ", and keeping (by masks) the one of the digit's magnitude, its `y` negated by a mask of its \
      sign, by Jacobian addition with the entry's `Z²` and `Z³`, whose exceptional cases (equal \
      or opposite points) do not arise for `d < n`; the sum is kept, by masks, unless the digit \
      is zero, and the entry in its place where the accumulator is the point at infinity; \
      `Z⁻¹` is the signature's call of `vg_p384_inv_mod_p" ++
      (if adx then "_adx" else "") ++ "`. The result (or zeros) is selected by a mask of the \
      checks, `d` in `[1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code
    stack := 8
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx", "avx", "avx2"] else [] }

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P384.curve) : List Artifact := [
  exchange false Impl.Ecdh.X86_64.exchangeP384
    (Proof.Ecdh.X86_64.P384.ecdh_verified h.law h.inv h.prime),
  exchange true Impl.Ecdh.X86_64.exchangeP384Adx
    (Proof.Ecdh.X86_64.P384.ecdh_verified_adx h.law h.inv h.prime)]

end VG.Generic.P384.X86_64.EcdhP384
