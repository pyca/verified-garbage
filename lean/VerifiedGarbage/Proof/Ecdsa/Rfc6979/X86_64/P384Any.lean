module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.AnyVerified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P384Adx
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P384Sha384
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms

/-!
# Deterministic ECDSA over P-384 with any hash function on x86-64

P-384 as the proof's curve, with BMI2's and ADX's products (`adx`) or not, with the instance
`Spec.Ecdsa.Rfc6979.P384Sha384.inst` (its curve and bound on candidates; its hash
function is not used) and the comb's tables at `0x100000` in the witnesses' memory (`satMem`): `vg_ecdsa_p384_rfc6979_sign` meets the
shared contract (`verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.P384Any

open VG VG.X86_64

open VG.Proof.Ecdsa.X86_64.P384 (p384W_length p384_combConsts satMem satMem_held)

/-- The curve and the instance. -/
def any (adx : Bool) (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcAny :=
  ⟨p384Of adx hL hT hI, Spec.Ecdsa.Rfc6979.P384Sha384.inst, by cases adx <;> rfl, by decide, by decide, rfl⟩

theorem held : Abi.constsHeld satMem (fun _ => 0x100000) Impl.Ecdsa.X86_64.p384.combConsts := by
  rw [p384_combConsts]
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc
  exact satMem_held

theorem fits : ∀ c ∈ Impl.Ecdsa.X86_64.p384.combConsts, 0x100000 + 8 * c.2.length ≤ 2 ^ 64 := by
  rw [p384_combConsts]
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc
  show 0x100000 + 8 * List.length _ ≤ _
  rw [p384W_length]
  decide

/-- `vg_ecdsa_p384_rfc6979_sign`, with BMI2's and ADX's products (`adx`) or not, meets the
shared contract. -/
theorem verified (adx : Bool) (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target (any adx hL hT hI).code
      (Spec.Ecdsa.Rfc6979.P384Sha384.inst.signAnyContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p384.combConsts)
        408) := by
  cases adx
  · exact (any false hL hT hI).any_verified satMem held fits
  · exact (any true hL hT hI).any_verified satMem held fits

end VG.Proof.Ecdsa.Rfc6979.X86_64.P384Any
