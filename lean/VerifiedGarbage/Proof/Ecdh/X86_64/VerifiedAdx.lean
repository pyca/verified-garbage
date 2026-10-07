import VerifiedGarbage.Proof.Ecdh.X86_64.Verified
import VerifiedGarbage.Proof.Ecdh.X86_64.LitAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx

/-!
# ECDH over P-256 on x86-64 with BMI2 and ADX: `Verified`

As `Verified.lean`, for `p256x` (`p256` multiplying with BMI2 and ADX): the
same curve, so the same precondition and postcondition.
-/

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64
open VG.Proof.Ecdsa.X86_64

-- TODO(WinJac): as `ecdh_x86`, once the Jacobian window method's `MulOk` is proven.
/-
theorem ecdh_x86_adx (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86_64.InvSounds)
    (s : State) (hs : ecdhX86_64.pre s) :
    ∃ t s', Exec isa exchangeP256Adx s t s' ∧ abiPreserved s s' ∧ ecdhX86_64.post s s' :=
  ecdh_x86_of (p256x_ok hI) hL (fun _ h => { pre_of h with }) (fun _ _ => post_of) rfl (by lit_decide)
    (by lit_decide) (by lit_decide) s hs
-/

theorem ecdh_ct_adx : ConstantTime isa ecdhX86_64.pre ecdhX86_64.pub exchangeP256Adx :=
  VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx])
    (fun _ _ _ _ ⟨_, h1, h2, h3, h4⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4)
    (by taint_decide)

-- TODO(WinJac): needs `ecdh_x86_adx`.
/-
theorem ecdh_verified_adx (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target exchangeP256Adx
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst X86_64.abi) :=
  Verified.of_correct (ecdh_x86_adx hL hI) ecdh_ct_adx implies
-/

end VG.Proof.Ecdh.X86_64
