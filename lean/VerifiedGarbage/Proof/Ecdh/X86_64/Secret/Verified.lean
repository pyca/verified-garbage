import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Main
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.CT
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.P256Layout
import VerifiedGarbage.Proof.Ecdh.X86_64.VerifiedAdx

/-! The secret Jacobian implementations satisfy the unchanged P-256 ECDH contract. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64.Window5
open VG.Proof.Ecdsa.X86_64

theorem correct_of {c : Cfg} {code : Prog isa} (hc : CfgOk c) (hL : Weierstrass.Law c.C)
    (hCurve : c.C=Spec.P256.curve)
    (hLay : SecretLay (Impl.Ecdh.X86_64.Window5.cfg c) size) (hO : Weierstrass.PeerOrder c.C)
    (hpre : ∀ s, ecdhX86_64.pre s → EPre c s) (hpost : ∀ s s', EPost c s s' → ecdhX86_64.post s s')
    (hcode : Impl.Ecdh.X86_64.Window5.exchange c = code)
    (hsp : code.allInstrs (fun i => !Taint.clobbers i .rsp) = true)
    (hnc : code.noCalls = true) (hmx : code.allInstrs (fun i => !loadsMxcsr i) = true) (s : State)
    (hs : ecdhX86_64.pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ ecdhX86_64.post s s' := by
  subst hcode
  obtain ⟨t, s', he, hsv, hpost'⟩ := exchange_ok hc hCurve hLay hL hO (hpre s hs)
  have hsp : ∀ i ∈ instrs (Impl.Ecdh.X86_64.Window5.exchange c), Taint.clobbers i .rsp = false := by
    rw [Code.allInstrs_eq, List.all_eq_true] at hsp
    intro i hi
    simpa using hsp i hi
  have F := (Exec.regions he hnc).2.2
  obtain ⟨-, hwr, -, -, -, -, -, hro, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec hmx he ⟨fun r hr => ?_, ?_⟩, hpost _ _ hpost'⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact Exec.gpr hsp he
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
  · rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hro
      · exact hrs) (by decide)

theorem baseline_correct (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PeerOrder Spec.P256.curve) (s : State) (hs : ecdhX86_64.pre s) :
    ∃ t s',Exec isa exchangeP256 s t s' ∧ abiPreserved s s' ∧ ecdhX86_64.post s s' :=
  correct_of (p256_ok hI) hL rfl p256_layout hO (fun _ => pre_of) (fun _ _ => post_of)
    rfl (by lit_decide) (by lit_decide) (by lit_decide) s hs

theorem adx_correct (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PeerOrder Spec.P256.curve) (s : State) (hs : ecdhX86_64.pre s) :
    ∃ t s',Exec isa exchangeP256Adx s t s' ∧ abiPreserved s s' ∧ ecdhX86_64.post s s' :=
  correct_of (p256x_ok hI) hL rfl p256_adx_layout hO (fun _ h => {pre_of h with}) (fun _ _ => post_of)
    rfl (by lit_decide) (by lit_decide) (by lit_decide) s hs

theorem baseline_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PeerOrder Spec.P256.curve) :
    Verified X86_64.target exchangeP256 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst X86_64.abi) :=
  Verified.of_correct (baseline_correct hL hI hO) baseline_ct implies

theorem adx_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PeerOrder Spec.P256.curve) :
    Verified X86_64.target exchangeP256Adx (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst X86_64.abi) :=
  Verified.of_correct (adx_correct hL hI hO) adx_ct implies

end VG.Proof.Ecdh.X86_64.Secret
