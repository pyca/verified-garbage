module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.MulVerified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd

/-!
# secp256k1's point multiplication on x86-64

`vg_secp256k1_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over secp256k1's group law and inversions `h`, the variant
`Variants/Secp256k1/X86_64/Law.lean`: the ladder's proof takes the group law,
and the curve's facts (`secp256k1_ok`) its inversions.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.X86_64.MulSecp256k1

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.Secp256k1.Mul

/-- What the function runs. -/
def note : String :=
  "The function keeps `rbx`, `rbp` and `r12`–`r15` in `xmm0` to `xmm5` while it runs, expands \
  `k` into a table of its bits, one per byte, at bytes 1504 to 1767, copies `Q` to bytes 992 to \
  1055 (slots 29 and 30), and runs a ladder over the 256 bits of `k`'s four words, from the \
  top: each step doubles the accumulator and adds `Q` by the general complete addition formulas \
  of Renes, Costello and Batina (Algorithm 1, with `a` and `3 b` read from `ws`), and keeps the \
  sum or the double by a mask of the bit. Field elements are four 64-bit words in Montgomery \
  form, multiplied by word-by-word Montgomery multiplication (CIOS) with a final conditional \
  subtraction; nothing depends on `k` or `Q` but through masks."

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.Secp256k1.curve) : List Artifact :=
  [{ C.mulApi with
      target := X86_64.target
      doc := C.mulApi.doc (notes := [note])
      code := secp256k1.mulFn
      contract := C.mulContract X86_64.abi
      verified := mul_verified h.law h.inv
      spSafe := Code.all_of_allInstrs (show mulCode.allInstrs _ = true by lit_decide) }]

end VG.Generic.Secp256k1.X86_64.MulSecp256k1
