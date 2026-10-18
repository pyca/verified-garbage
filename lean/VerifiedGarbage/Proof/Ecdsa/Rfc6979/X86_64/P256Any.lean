module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.AnyVerified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P256Adx
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha256
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd

/-!
# Deterministic ECDSA over P-256 with any hash function on x86-64

P-256 as the proof's curve, with BMI2's and ADX's products (`adx`) or not, with the instance
`Spec.Ecdsa.Rfc6979.P256Sha256.inst` (its curve and bound on candidates; its hash
function is not used) and the comb's tables at `0x100000` in the witnesses' memory (`satMem`): `vg_ecdsa_p256_rfc6979_sign` meets the
shared contract (`verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.P256Any

open VG VG.X86_64

open VG.Proof.Ecdsa.X86_64 (p256W_length p256_combConsts satMem satMem_held)

/-- The curve and the instance. -/
def any (adx : Bool) (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcAny :=
  ⟨p256Of adx hL hT hI, Spec.Ecdsa.Rfc6979.P256Sha256.inst, by cases adx <;> rfl, by decide, by decide, rfl⟩

theorem held : Abi.constsHeld satMem (fun _ => 0x100000) Impl.Ecdsa.X86_64.p256.combConsts := by
  rw [p256_combConsts]
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc
  exact satMem_held

theorem fits : ∀ c ∈ Impl.Ecdsa.X86_64.p256.combConsts, 0x100000 + 8 * c.2.length ≤ 2 ^ 64 := by
  rw [p256_combConsts]
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc
  show 0x100000 + 8 * List.length _ ≤ _
  rw [p256W_length]
  decide

/-- `vg_ecdsa_p256_rfc6979_sign`, with BMI2's and ADX's products (`adx`) or not, meets the
shared contract. -/
theorem verified (adx : Bool) (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target (any adx hL hT hI).code
      (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signAnyContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p256.combConsts)
        408) := by
  cases adx
  · exact (any false hL hT hI).any_verified satMem held fits
  · exact (any true hL hT hI).any_verified satMem held fits

end VG.Proof.Ecdsa.Rfc6979.X86_64.P256Any
