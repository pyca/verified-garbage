import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.EcKey.P256.X86
import VerifiedGarbage.Proof.EcKey.X86.CombVerified
import VerifiedGarbage.Proof.EcKey.X86.Lit

/-!
# P-256 public keys (FIPS 186-5 §A.2) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/X86/Law.lean`.
-/

namespace VG.Generic.P256.X86.EcP256

def artifacts (h : Proof.Weierstrass.X86.Inv.HasLawInv Spec.P256.curve) : List Artifact := [
  { Spec.EcKey.P256.publicKeyApi with
    target := X86.target
    doc := Spec.EcKey.P256.publicKeyApi.doc (notes := ["Field elements are eight 32-bit words in \
      Montgomery form. `[d]G` uses a seven-bit signed comb with 37 complete point additions \
      and no doublings, scanning every entry of each static table with SSE2. The function \
      obtains `VG_P256_COMB` with a position-independent four-byte CALL frame and saves \
      callee-saved registers in `scratch`. `Z⁻¹` uses 20 batches of 30 constant-time divsteps. A mask selects the encoded public key or zeros; only addresses affect timing."])
    consts := Impl.Ecdsa.X86.p256Comb.combConsts
    code := Proof.EcKey.X86.pkCombCode
    contract := Spec.EcKey.P256.inst.publicKeyContract
      (X86.abi.withConsts Impl.Ecdsa.X86.p256Comb.combConsts) 4
    stack := 4
    verified := Proof.EcKey.X86.pkComb_verified h.law h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P256.X86.EcP256
