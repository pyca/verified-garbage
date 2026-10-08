import VerifiedGarbage.Proof.P256.EcdhJac.Timing
import VerifiedGarbage.Proof.P256.EcdhJac.Adapter
import VerifiedGarbage.Proof.P256.EcdhJac.Window
import VerifiedGarbage.Proof.Ecdh.AArch64.WithMul

/-! Public ECDH contract and ABI, composed with a separately certified
secret-scalar multiplication. -/
namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64

private theorem ungroup {s t : State} {tr}
    (h : Exec isa (Impl.Ecdh.AArch64.Cfg.exchangeWith p256 mq) s tr t) :
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
    (hI : Weierstrass.AArch64.InvSounds) (hm : MulOk p256 mq)
    (s : State) (hs : ecdhAArch64.pre s) :
    ∃ tr t,Exec isa Impl.P256.EcdhJac.exchange s tr t ∧
      abiPreserved s t ∧ ecdhAArch64.post s t := by
  obtain ⟨tr,t,he,hsv,hu,hpost⟩ := exchangeWith_ok (p256_ok hI) hL hm rfl
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
    (hI : Weierstrass.AArch64.InvSounds) (hm : MulOk p256 mq) :
    Verified AArch64.target Impl.P256.EcdhJac.exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst AArch64.abi) :=
  Verified.of_correct (correct_of_mul hL hI hm) (constantTime hL hI hm) implies

/-- Width-five Jacobian ECDH satisfies the unchanged public contract. -/
theorem verified (hL : Weierstrass.Law Spec.P256.curve)
    (hI : Weierstrass.AArch64.InvSounds) (hO : Weierstrass.PrimeOrder Spec.P256.curve) :
    Verified AArch64.target Impl.P256.EcdhJac.exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst AArch64.abi) :=
  verified_of_mul hL hI (mul_of_window (p256_ok hI) (window_ok hL (p256_ok hI).am3 hO))

end VG.Proof.P256.EcdhJac
