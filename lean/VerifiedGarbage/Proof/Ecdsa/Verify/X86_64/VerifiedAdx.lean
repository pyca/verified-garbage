import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx

/-!
# ECDSA verification over P-256 on x86-64 with BMI2 and ADX: `Verified`

As `Verified.lean`, for `p256x` (`p256` multiplying with BMI2 and ADX): the
same curve, so the same precondition and postcondition.
-/

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64

theorem verify_x86_adx (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s', Exec isa verifyP256Adx s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' :=
  verify_x86_of (p256x_ok hI) hL (p256_tbls hT) (fun _ h => { pre_of h with }) (fun _ _ => id) rfl
    (by lit_decide) (by lit_decide) (by lit_decide) s hs

theorem verify_ct_adx : ConstantTime isa verifyX86_64.pre verifyX86_64.pub verifyP256Adx :=
  VG.Taint.constantTime (A := taintSym ["VG_P256_COMB"]) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx])
    (fun _ _ _ _ ⟨_, h1, h2, h3, h4, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    (by taint_decide)

theorem verify_verified_adx (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target verifyP256Adx
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)) :=
  Verified.of_correct (verify_x86_adx hL hT hI) verify_ct_adx implies

end VG.Proof.Ecdsa.Verify.X86_64
