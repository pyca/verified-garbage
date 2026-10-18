module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.AnyVerified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Spec.EcKey.Generic

/-!
# Deterministic ECDSA over brainpoolP512r1 with any hash function on x86-64

brainpoolP512r1 as the proof's curve, with the instance
`Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst` (its curve and bound on candidates; its hash
function is not used): `vg_ecdsa_brainpoolp512r1_rfc6979_sign` meets the
shared contract (`verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP512r1Any

open VG VG.X86_64

/-- The curve and the instance. -/
def any (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.X86_64.InvSounds) : RfcAny :=
  ⟨brainpoolp512r1 hL hI, Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst, rfl, by decide, by decide, rfl⟩

theorem comb_nil : Impl.Ecdsa.X86_64.brainpoolp512r1.combConsts = [] := rfl

theorem held : Abi.constsHeld (fun _ => 0) (fun _ => 0x100000) Impl.Ecdsa.X86_64.brainpoolp512r1.combConsts := by
  rw [comb_nil]; exact fun _ h => by cases h

theorem fits : ∀ c ∈ Impl.Ecdsa.X86_64.brainpoolp512r1.combConsts, 0x100000 + 8 * c.2.length ≤ 2 ^ 64 := by
  rw [comb_nil]; exact fun _ h => by cases h

/-- `vg_ecdsa_brainpoolp512r1_rfc6979_sign` meets the shared contract. -/
theorem verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target (any hL hI).code
      (Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst.signAnyContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.brainpoolp512r1.combConsts)
        408) :=
  (any hL hI).any_verified (fun _ => 0) held fits

end VG.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP512r1Any
