module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.AnyVerified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P224
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P224Sha224
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Spec.EcKey.Generic

/-!
# Deterministic ECDSA over P-224 with any hash function on x86-64

P-224 as the proof's curve, with the instance
`Spec.Ecdsa.Rfc6979.P224Sha224.inst` (its curve and bound on candidates; its hash
function is not used) and the comb's tables at `0x100000` in the witnesses' memory (`satMem`): `vg_ecdsa_p224_rfc6979_sign` meets the
shared contract (`verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.P224Any

open VG VG.X86_64

open VG.Proof.Ecdsa.X86_64.P224 (p224W_length p224_combConsts satMem satMem_held)

/-- The curve and the instance. -/
def any (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcAny :=
  ⟨p224 hL hT hI, Spec.Ecdsa.Rfc6979.P224Sha224.inst, rfl, by decide, by decide, rfl⟩

theorem held : Abi.constsHeld satMem (fun _ => 0x100000) Impl.Ecdsa.X86_64.p224.combConsts := by
  rw [p224_combConsts]
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc
  exact satMem_held

theorem fits : ∀ c ∈ Impl.Ecdsa.X86_64.p224.combConsts, 0x100000 + 8 * c.2.length ≤ 2 ^ 64 := by
  rw [p224_combConsts]
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc
  show 0x100000 + 8 * List.length _ ≤ _
  rw [p224W_length]
  decide

/-- `vg_ecdsa_p224_rfc6979_sign` meets the shared contract. -/
theorem verified (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target (any hL hT hI).code
      (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signAnyContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p224.combConsts)
        408) :=
  (any hL hT hI).any_verified satMem held fits

end VG.Proof.Ecdsa.Rfc6979.X86_64.P224Any
