import VerifiedGarbage.Proof.Ecdh.X86_64.P384.Verified
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.LitAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx
import VerifiedGarbage.Proof.P384.X86_64.TaintSumsAdx

/-!
# ECDH over P-384 on x86-64 with BMI2 and ADX: `Verified`

As `Verified.lean`, for `p384x` (`p384` multiplying modulo `p` with BMI2 and
ADX): the same curve, so the same precondition and postcondition.
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

theorem ecdh_x86_adx (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve) (s : State) (hs : ecdhX86_64.pre s) :
    ∃ t s', Exec isa exchangeP384Adx s t s' ∧ abiPreserved s s' ∧ ecdhX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := exchangeWith_ok (p384x_ok hI) hL
    (mulQJP384_ok (p384x_ok hI) rfl rfl hL hO) (mulQJ_w (p384x_ok hI)) (pre_of_x hs)
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
  obtain ⟨_, hc⟩ : ∃ h, (taintS.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) exchangeP384Adx h).isSome = true := by
    taint_decide_sum [Proof.P384.X86_64.ladderGXSum, Proof.P384.X86_64.powPXSum]
  refine VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ hc
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
