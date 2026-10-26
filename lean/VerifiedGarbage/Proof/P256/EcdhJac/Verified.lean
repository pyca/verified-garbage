module

import VerifiedGarbage.Proof.P256.EcdhJac.Timing
import VerifiedGarbage.Proof.P256.EcdhJac.Adapter
import VerifiedGarbage.Proof.P256.EcdhJac.Window
import VerifiedGarbage.Proof.P256.EcdhJac.Exchange
import VerifiedGarbage.Proof.P256.EcdhInverse.Inverse
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
public import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
import Mathlib.Data.BitVec
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.P256.EcdhInverse.Update
public import VerifiedGarbage.Proof.Weierstrass.InvToM
public import VerifiedGarbage.Proof.P256.EcdhJac.DbluCertificate
public import VerifiedGarbage.Proof.P256.EcdhJac.OutCertificate
public import VerifiedGarbage.Proof.P256.EcdhTable.Dblu
public import VerifiedGarbage.Proof.P256.EcdhTable.Zaddu
public import VerifiedGarbage.Proof.P256.Linear.WeakCertificate
public import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Ecdh.AArch64.Contract
public import VerifiedGarbage.Proof.Ecdh.AArch64.Lit
public import VerifiedGarbage.Proof.Ecdh.AArch64.MulOk
public import VerifiedGarbage.Proof.P256.EcdhJac.Lit
import Mathlib.Tactic.FieldSimp
import VerifiedGarbage.Proof.Ecdh.AArch64.Verified
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Public ECDH contract and ABI, composed with a separately certified
secret-scalar multiplication. -/

@[expose] public section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Mont

private theorem ungroup {s t : State} {tr}
    (h : Exec isa (Impl.P256.EcdhJac.Frontend.exchange p256 mq Impl.P256.EcdhInverse.inverse) s tr t) :
    Exec isa Impl.P256.EcdhJac.exchange s tr t := by
  cases h with
  | seq a h => cases h with
    | seq b h => cases h with
      | seq c h => cases h with
        | seq d h => cases h with
          | seq m h => cases m with
            | seq p w =>
              simpa only [Impl.P256.EcdhJac.exchange, Impl.P256.EcdhJac.c, List.append_assoc] using
                (Exec.seq a (Exec.seq b (Exec.seq c (Exec.seq d (Exec.seq p (Exec.seq w h))))))

theorem correct_of_mul (hL : Weierstrass.Law Spec.P256.curve)
    (hI : Weierstrass.AArch64.InvSounds) (hm : MulWithInverseOk p256 mq Impl.P256.EcdhInverse.inverse)
    (s : State) (hs : ecdhAArch64.pre s) :
    ∃ tr t,Exec isa Impl.P256.EcdhJac.exchange s tr t ∧
      abiPreserved s t ∧ ecdhAArch64.post s t := by
  obtain ⟨tr,t,he,hsv,hu,hpost⟩ := Frontend.exchangeWith_ok (p256_ok hI) hL hm rfl
    middle_callsKeep middle_keepsUntouched (pre_of hs)
  have ex := ungroup he
  refine ⟨tr,t,ex,⟨?_,Exec.sp ex,Exec.preservedV ex keepsV⟩,post_of hpost⟩
  intro r hr
  by_cases hh : r∈untouched
  · exact hu r hh
  · apply hsv r
    revert hh
    revert r
    decide

theorem verified_of_mul (hL : Weierstrass.Law Spec.P256.curve)
    (hI : Weierstrass.AArch64.InvSounds) (hm : MulWithInverseOk p256 mq Impl.P256.EcdhInverse.inverse) :
    Verified AArch64.target Impl.P256.EcdhJac.exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst AArch64.abi) :=
  Verified.of_correct (correct_of_mul hL hI hm) (constantTime hL hI hm) implies

/-- Width-five Jacobian ECDH satisfies the unchanged public contract. -/
theorem verified (hL : Weierstrass.Law Spec.P256.curve)
    (hI : Weierstrass.AArch64.InvSounds) (hO : Weierstrass.PrimeOrder Spec.P256.curve)
    (hT : Weierstrass.InvToM Spec.P256.curve.p) :
    Verified AArch64.target Impl.P256.EcdhJac.exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst AArch64.abi) :=
  verified_of_mul hL hI (mulWithInverse_of_window (p256_ok hI)
    (W:=EcdhInverse.inverseMemory) (by unfold FixedOk; decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun hs hm hx => EcdhInverse.inverse_ok VG.Proof.P256.p_prime hT
      (invLayP (p256_ok hI)) (by decide) (Weierstrass.unitMod_pow_two (p256_ok hI).p_odd _) hs
      (modOkA_inv (p256_ok hI) hm (.inl rfl) rfl rfl) hx
      (p256_ok hI).inv_p)
    (window_ok hL (p256_ok hI).am3 hO))

end VG.Proof.P256.EcdhJac
