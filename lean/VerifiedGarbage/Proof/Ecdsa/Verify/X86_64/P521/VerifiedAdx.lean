import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.LitAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.VerifiedAdx

/-!
# ECDSA verification over P-521 on x86-64 with BMI2 and ADX: `Verified`

As `Verified.lean`, for `p521x` (`p521` multiplying modulo `p` with BMI2 and
ADX): the same curve, so the same precondition and postcondition.
-/

namespace VG.Proof.Ecdsa.Verify.X86_64.P521

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P521

theorem pre_of_x {s : State} (h : verifyX86_64.pre s) : VPre p521x s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p521x_combConsts, p521_constRegions, p521x_C, show p521.C.len = 66 from rfl]; simp only [
    List.cons_append, List.nil_append], h2, h3, h4, h5, h7, ?_⟩
  rw [TblsHeld, p521x_combConsts]
  refine ⟨fun c hc => ?_, fun t ht => ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · simp only [p521_constRegions, List.mem_singleton] at ht; subst ht
    refine ⟨fit, fun r hr => hdw r ?_⟩
    rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    simp [hr]

/-! The facts about every instruction, each its own declaration: the code is
large enough that the three in one would exceed `verify_x86`'s budget. -/

theorem verify_rsp_adx : verifyP521Adx.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide

theorem verify_noCalls_adx : verifyP521Adx.noCalls = true := by lit_decide

theorem verify_mxcsr_adx : verifyP521Adx.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem verify_x86_adx (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s', Exec isa verifyP521Adx s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := verify_ok (p521x_ok hI) hL (p521x_tbls hT) (pre_of_x hs)
  have hsp : ∀ i ∈ instrs verifyP521Adx, Taint.clobbers i .rsp = false := by
    have h := verify_rsp_adx
    rw [Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he verify_noCalls_adx).2.2
  obtain ⟨-, hwr, -, -, -, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec verify_mxcsr_adx he ⟨fun r hr => ?_, ?_⟩, hpost⟩
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
      rintro r rfl
      exact hrs) (by decide)

/-- P-521's comb, as `p521`'s `comb`. -/
abbrev p521Table_adx : CombData := ⟨7, Impl.P521.p521Comb7, Impl.P521.p521Comb7Start, "VG_P521_COMB", false⟩

/-- The taint checks around the comb's public lookups: the comb's own parts,
the code before it and the code after it, whose window method (its table and
loop) is checked by its summaries. -/
theorem verify_checks_adx : VerifyChecks p521x p521Table_adx where
  comb := {
    init := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
    head := VG.Taint.constantTime (A := taintSym ["VG_P521_COMB"]) (Taint.ofRegs [.rdi, .rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
    tail := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rbx, .rdx])
      (fun _ _ _ _ h => h) (by taint_decide) }
  before := VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx])
    (fun _ _ _ _ h => h) (by taint_decide)
  after := by
    obtain ⟨_, hc⟩ : ∃ h, (taintS.check (Taint.ofRegs [.rdi]) (verifySuffix p521x) h).isSome = true := by
      taint_decide_sum [Proof.P521.X86_64.winBuildXVSum, Proof.P521.X86_64.winLoopXVSum]
    exact VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) hc

/-- The shared contract declares all verification input buffers public. -/
theorem verify_public_of_spec_adx {s₁ s₂ : State}
    (pub : (Spec.Ecdsa.P521.inst.verifyContract (X86_64.abi.withConsts p521.combConsts)).pub s₁ s₂) :
    VerifyPublic p521x p521Table_adx s₁ s₂ := by
  sig_pub [Spec.Ecdsa.P521.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P521.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p521_combConsts,
    Abi.withConsts] at pub
  obtain ⟨_, hsy, inputs, h0, h1, h2, h3⟩ := pub
  refine ⟨Taint.agree_ofRegs ?_, hsy, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
    have parts := List.append_inj eqBytes (by simp only [List.length_append, Weierstrass.length_bytesAt])
    have digest := (List.append_inj parts.1 (by simp only [Weierstrass.length_bytesAt])).2
    exact publicU_congr digest parts.2

theorem verify_ct_adx (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    ConstantTime isa
      (Spec.Ecdsa.P521.inst.verifyContract (X86_64.abi.withConsts p521.combConsts)).pre
      (Spec.Ecdsa.P521.inst.verifyContract (X86_64.abi.withConsts p521.combConsts)).pub verifyP521Adx := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact verify_public_ct (p521x_ok hI) hL (p521x_tbls hT) rfl (by decide) verify_checks_adx
    _ _ _ _ _ _ (pre_of_x (implies.pre _ pre₁)) (pre_of_x (implies.pre _ pre₂))
    (verify_public_of_spec_adx pub) e₁ e₂

theorem verify_verified_adx (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target verifyP521Adx
      (Spec.Ecdsa.P521.inst.verifyContract (X86_64.abi.withConsts p521.combConsts)) := by
  refine ⟨fun s hs => ?_, verify_ct_adx hL hT hI, implies.sat⟩
  obtain ⟨t, s', he, ha, hp⟩ := verify_x86_adx hL hT hI s (implies.pre _ hs)
  exact ⟨t, s', he, ha, implies.post s s' hs hp⟩

end VG.Proof.Ecdsa.Verify.X86_64.P521
