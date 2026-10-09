import VerifiedGarbage.Proof.Ecdh.X86_64.P384.Verified
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.LitEraseAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx
import VerifiedGarbage.Proof.Weierstrass.X86_64.DoubleCms

/-!
# ECDH over P-384 on x86-64 with BMI2 and ADX: `Verified`

As `Verified.lean`, for `p384x` (`p384` multiplying modulo `p` with BMI2 and
ADX): the same curve, so the same precondition and postcondition, with the
doubling whose small multiples are fused (`doubleCms_dblOk`, `mulQJP384Cms_ok`).
-/

namespace VG.Proof.Ecdh.X86_64.P384

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P384

theorem pre_of_x {s : State} (h : ecdhX86_64.pre s) : EPre p384x s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, -, -, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h10, h11⟩

theorem post_of_x {s s' : State} (h : EPost p384x s s') : ecdhX86_64.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .rsi) (s.gpr .rdx) with
    | some z => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 48 = z
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 48 = List.replicate 48 0
  revert h
  generalize hq : ex s.mem (s.gpr .rsi) (s.gpr .rdx) = q
  rw [show Spec.Ecdh.exchange p384x.C (dk p384x s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .rdx) (1 + 2 * p384x.C.len)) = ex s.mem (s.gpr .rsi) (s.gpr .rdx) from rfl, hq]
  rcases q with _ | z <;> exact id

/-- The Jacobian window method with an affine table and the doubling
`doubleCms` computes `[d]P` on P-384, whose field `cms` needs. -/
theorem mulQJP384Cms_ok {c : Cfg} (hc : CfgOk c) (h6 : c.n = 6) (hcC : c.C = Spec.P384.curve)
    (hsp : c.MP'.sparse = true) (hL : Weierstrass.Law c.C) (hO : Weierstrass.PrimeOrder c.C) :
    MulOk c (Impl.Ecdh.X86_64.Cfg.mulQJA c (Impl.Weierstrass.X86_64.doubleCms c.MP' c.rcbSlots)) (mulQJAW c) :=
  mulQJA_ok hc (Or.inr h6) hL hO (Weierstrass.X86_64.doubleCms_dblOk hsp
    (Weierstrass.unitMod_pow_two hc.p_odd _) hL hc.am3) (hcC ▸ n_mod32) (hcC ▸ n_ge64)

theorem ecdh_x86_adx (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve) (s : State) (hs : ecdhX86_64.pre s) :
    ∃ t s', Exec isa exchangeP384Adx s t s' ∧ abiPreserved s s' ∧ ecdhX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := wp_of_inline (c := exchangeP384Adx) (by lit_decide) <|
    exchangeWith_ok (p384x_ok hI) hL
    (mulQJP384Cms_ok (p384x_ok hI) rfl rfl (by decide +kernel) hL hO) (mulQJA_w (p384x_ok hI)) (pre_of_x hs)
  have hsp : ∀ i ∈ instrs exchangeP384Adx, Taint.clobbers i .rsp = false := by
    have h : exchangeP384Adx.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
    rw [Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (by lit_decide)).2.2
  obtain ⟨-, hwr, -, -, -, -, -, hro, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ⟨fun r hr => ?_, ?_⟩, post_of_x hpost⟩
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

theorem ecdh_ct_adx : ConstantTime isa ecdhX86_64.pre ecdhX86_64.pub exchangeP384Adx := by
  refine VG.Taint.constantTime_mapBlocks (c' := exchangeErasedAdx) taintS_eraseInv
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) rfl ?_ rfl (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem ecdh_verified_adx (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve) :
    Verified X86_64.target exchangeP384Adx (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst X86_64.abi) :=
  Verified.of_correct (ecdh_x86_adx hL hI hO) ecdh_ct_adx implies

end VG.Proof.Ecdh.X86_64.P384
