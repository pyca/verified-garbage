import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Timing
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.TaintSym

/-!
# ECDSA verification over P-256 on x86-64: `Verified`

P-256 is a curve the proof supports (`p256_ok`, and `Law` for its group law,
its comb's tables and `InvSounds` for its inversions, which the
registration file supplies: `Proof.P256.law`, `Proof.P256.combOk7` and the
variant's `inv`), so `verify_ok` gives the contract's
postcondition; the callee-saved registers are restored, `rsp` is never
written, and every store is to `scratch`, which the return address is apart
from (`abiPreserved`). Direct table lookup uses the scalar determined by
the public digest and signature. `verify_public_ct` relates those lookups,
and taint tracking checks the remaining code against the shared contract.
-/

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64

theorem pre_of {s : State} (h : verifyX86_64.pre s) : VPre p256 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p256_combConsts, show p256.C.len = 32 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h7, ?_⟩
  rw [TblsHeld, p256_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    simp [hr]

/-- The verification `code` of a curve `c` (P-256, with either multiplication)
that the proof supports, whose precondition the contract's gives (`hpre`),
never writing `rsp`, calling or loading MXCSR (which its literal decides). -/
theorem verify_x86_of {c : Cfg} {code : Prog isa} (hc : CfgOk c) (hL : Weierstrass.Law c.C) (hT : CombTbls c)
    (hpre : ∀ s, verifyX86_64.pre s → VPre c s) (hpost : ∀ s s', VPost c s s' → verifyX86_64.post s s')
    (hcode : Impl.Ecdsa.Verify.X86_64.Cfg.verify c = code)
    (hsp : code.allInstrs (fun i => !Taint.clobbers i .rsp) = true)
    (hnc : code.noCalls = true) (hmx : code.allInstrs (fun i => !loadsMxcsr i) = true) (s : State)
    (hs : verifyX86_64.pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' := by
  subst hcode
  obtain ⟨t, s', he, hsv, hpost'⟩ := wp_of_inline hnc <| verify_ok hc hL hT (hpre s hs)
  have hsp : ∀ i ∈ instrs (Impl.Ecdsa.Verify.X86_64.Cfg.verify c), Taint.clobbers i .rsp = false := by
    rw [Code.allInstrs_eq, List.all_eq_true] at hsp
    intro i hi
    simpa using hsp i hi
  have F := (Exec.regions he hnc).2.2
  obtain ⟨-, hwr, -, -, -, hrs, -, -⟩ := hs
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
      rintro r rfl
      exact hrs) (by decide)

theorem verify_x86 (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s', Exec isa verifyP256 s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' :=
  verify_x86_of (p256_ok hI) hL (p256_tbls hL hT) (fun _ => pre_of) (fun _ _ => id) rfl (by lit_decide)
    (by lit_decide) (by lit_decide) s hs

def p256Table : CombData := ⟨7,Impl.P256.p256Comb7,Impl.P256.p256Comb7Start,"VG_P256_COMB",true⟩

theorem verify_checks : VerifyChecks p256 p256Table where
  comb := {
    init := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
    head := VG.Taint.constantTime (A := taintSym ["VG_P256_COMB"]) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
    tail := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi,.rbx,.rdx])
      (fun _ _ _ _ h => h) (by taint_decide) }
  before := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    (fun _ _ _ _ h => h) (by taint_decide)
  after := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

/-- The shared contract declares all verification input buffers public. -/
theorem verify_public_of_spec {s₁ s₂ : State}
    (pub : (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)).pub s₁ s₂) :
    VerifyPublic p256 p256Table s₁ s₂ := by
  sig_pub [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p256_combConsts,
    Abi.withConsts] at pub
  obtain ⟨_,hsy,inputs,h0,h1,h2,h3⟩ := pub
  refine ⟨Taint.agree_ofRegs ?_,hsy,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
    have parts := List.append_inj eqBytes (by simp only [List.length_append,Weierstrass.length_bytesAt])
    have digest := (List.append_inj parts.1 (by simp only [Weierstrass.length_bytesAt])).2
    exact publicU_congr digest parts.2

theorem verify_ct (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    ConstantTime isa
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)).pre
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)).pub verifyP256 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact verify_public_ct (p256_ok hI) hL (p256_tbls hL hT) rfl (by decide) verify_checks
    _ _ _ _ _ _ (pre_of (implies.pre _ pre₁)) (pre_of (implies.pre _ pre₂)) (verify_public_of_spec pub) e₁ e₂

theorem verify_verified (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target verifyP256
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)) := by
  refine ⟨fun s hs => ?_,verify_ct hL hT hI,implies.sat⟩
  obtain ⟨t,s',he,ha,hp⟩ := verify_x86 hL hT hI s (implies.pre _ hs)
  exact ⟨t,s',he,ha,implies.post s s' hs hp⟩

end VG.Proof.Ecdsa.Verify.X86_64
