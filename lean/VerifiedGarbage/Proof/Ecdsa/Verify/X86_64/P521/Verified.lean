import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Timing
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
import VerifiedGarbage.Proof.P521.X86_64.TaintSums
import VerifiedGarbage.Proof.Framework.X86_64.TaintSym

/-!
# ECDSA verification over P-521 on x86-64: `Verified`

P-521 is a curve the proof supports (`p521_ok`, and `Law` for its group law,
its comb's tables and `InvSounds` for its inversions, which the registration
file supplies: `Proof.P521.law`, `Proof.P521.combOk7` and the variant's
`inv`), so `verify_ok` gives the
contract's postcondition; the callee-saved registers are restored, `rsp` is never
written, and every store is to `scratch`, which the return address is apart
from (`abiPreserved`). The comb reads its table directly at `u`, which the
public digest and signature determine (`pubVerify`), and the projective
comparison needs no inversion of `Z`: `verify_public_ct` relates those
lookups, and taint tracking checks the code before and after the comb
(`verify_checks`, the window method by its summaries).
-/

namespace VG.Proof.Ecdsa.Verify.X86_64.P521

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P521

theorem pre_of {s : State} (h : verifyX86_64.pre s) : VPre p521 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p521_combConsts, p521_constRegions, show p521.C.len = 66 from rfl]; simp only [
    List.cons_append, List.nil_append], h2, h3, h4, h5, h7, ?_⟩
  rw [TblsHeld, p521_combConsts]
  refine ⟨fun c hc => ?_, fun t ht => ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · simp only [p521_constRegions, List.mem_singleton] at ht; subst ht
    refine ⟨fit, fun r hr => hdw r ?_⟩
    rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    simp [hr]

/-! The facts about every instruction, each its own declaration: the code is
large enough that the three in one would exceed `verify_x86`'s budget. -/

theorem verify_rsp : verifyP521.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide

theorem verify_noCalls : verifyP521.noCalls = true := by lit_decide

theorem verify_mxcsr : verifyP521.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem verify_x86 (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s', Exec isa verifyP521 s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := verify_ok (p521_ok hI) hL (p521_tbls hT) (pre_of hs)
  have hsp : ∀ i ∈ instrs verifyP521, Taint.clobbers i .rsp = false := by
    have h := verify_rsp
    rw [Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he verify_noCalls).2.2
  obtain ⟨-, hwr, -, -, -, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec verify_mxcsr he ⟨fun r hr => ?_, ?_⟩, hpost⟩
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
abbrev p521Table : CombData := ⟨7, Impl.P521.p521Comb7, Impl.P521.p521Comb7Start, "VG_P521_COMB", false⟩

/-- The taint checks around the comb's public lookups: the comb's own parts,
the code before it and the code after it, whose window method (its table and
loop) is checked by its summaries. -/
theorem verify_checks : VerifyChecks p521 p521Table where
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
    obtain ⟨_, hc⟩ : ∃ h, (taintS.check (Taint.ofRegs [.rdi]) (verifySuffix p521) h).isSome = true := by
      taint_decide_sum [Proof.P521.X86_64.winBuildVSum, Proof.P521.X86_64.winLoopVSum]
    exact VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) hc

/-- The shared contract declares all verification input buffers public. -/
theorem verify_public_of_spec {s₁ s₂ : State}
    (pub : (Spec.Ecdsa.P521.inst.verifyContract (X86_64.abi.withConsts p521.combConsts)).pub s₁ s₂) :
    VerifyPublic p521 p521Table s₁ s₂ := by
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

theorem verify_ct (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    ConstantTime isa
      (Spec.Ecdsa.P521.inst.verifyContract (X86_64.abi.withConsts p521.combConsts)).pre
      (Spec.Ecdsa.P521.inst.verifyContract (X86_64.abi.withConsts p521.combConsts)).pub verifyP521 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact verify_public_ct (p521_ok hI) hL (p521_tbls hT) rfl (by decide) verify_checks
    _ _ _ _ _ _ (pre_of (implies.pre _ pre₁)) (pre_of (implies.pre _ pre₂))
    (verify_public_of_spec pub) e₁ e₂

theorem verify_verified (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target verifyP521
      (Spec.Ecdsa.P521.inst.verifyContract (X86_64.abi.withConsts p521.combConsts)) := by
  refine ⟨fun s hs => ?_, verify_ct hL hT hI, implies.sat⟩
  obtain ⟨t, s', he, ha, hp⟩ := verify_x86 hL hT hI s (implies.pre _ hs)
  exact ⟨t, s', he, ha, implies.post s s' hs hp⟩

end VG.Proof.Ecdsa.Verify.X86_64.P521
