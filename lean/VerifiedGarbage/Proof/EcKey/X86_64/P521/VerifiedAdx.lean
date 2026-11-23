module

public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.VerifiedAdx
import VerifiedGarbage.Proof.Weierstrass.X86_64.CodeErase
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.P521.X86_64.TaintSumsAdx
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.EcKey.X86_64.P521.LitAdx
public import VerifiedGarbage.Impl.EcKey.P521.X86_64
public import VerifiedGarbage.Proof.EcKey.X86_64.P521.Verified
import VerifiedGarbage.Proof.Framework.LitShare
public import VerifiedGarbage.Proof.EcKey.X86_64.Main
import VerifiedGarbage.Proof.EcKey.X86_64.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.LitAdx
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.VerifiedAdx
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CodeErase
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.P521.X86_64.TaintSumsAdx
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.EcKey.X86_64.P521.LitAdx
meta import VerifiedGarbage.Proof.EcKey.X86_64.P521.Verified
meta import VerifiedGarbage.Impl.EcKey.P521.X86_64
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.EcKey.X86_64.Main
meta import VerifiedGarbage.Proof.EcKey.X86_64.P521.Lit
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.LitAdx
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase

/-!
# P-521 public keys on x86-64 with BMI2 and ADX: `Verified`

As `Verified.lean`, for `p521x` (`p521` multiplying modulo `p` with BMI2 and
ADX): the same curve, so the same precondition and postcondition.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86_64.P521

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.EcKey.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P521

theorem pre_of_x {s : State} (h : pkX86_64.pre s) : PkPre p521x s := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, h8, h9, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p521x_combConsts, p521_constRegions, p521x_C, show p521.C.len = 66 from rfl]; simp only [
    List.cons_append, List.nil_append], h2, h3, h4, h5, h8, h9, ?_⟩
  rw [TblsHeld, p521x_combConsts]
  refine ⟨fun c hc => ?_, fun t ht => ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · simp only [p521_constRegions, List.mem_singleton] at ht; subst ht
    refine ⟨fit, fun r hr => hdw r ?_⟩
    rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h]

theorem post_of_x {s s' : State} (h : PkPost p521x s s') : pkX86_64.post s s' := by
  unfold PkPost at h
  dsimp only [pkX86_64]
  revert h
  generalize hq : pk s.mem (s.gpr .rsi) = q
  rw [show Spec.EcKey.publicKey p521x.C (dk p521x s) = pk s.mem (s.gpr .rsi) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

/-- `publicKeyP521Adx` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its checks of every instruction evaluate
(`Proof/Weierstrass/X86_64/CodeErase.lean`). -/
def publicKeyP521AdxErased : Prog isa := Code.erase publicKeyP521Adx

materialize_shared publicKeyP521AdxErased

/-- `InlineOkN`, calls nested two deep, checked once for every theorem that
needs it. -/
theorem pk_inlineOk_adx : publicKeyP521Adx.InlineOkN 2 = true := by lit_decide

theorem pk_inlineAll_adx : publicKeyP521Adx.inlineAll = publicKeyI p521x := by kernel_rfl

theorem pk_x86_adx (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (s : State) (hs : pkX86_64.pre s) :
    ∃ t s', Exec isa publicKeyP521Adx.inlineAll s t s' ∧ abiPreserved s s' ∧ pkX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := publicKey_okI (c := p521x) (p521x_ok hI).toBaseCfgOk hL (p521x_tbls hT)
    (pre_of_x hs) p521x_mulBase
  rw [← pk_inlineAll_adx] at he
  have hsp := Code.clobbers_rsp_of_inlineOkN pk_inlineOk_adx
  have F := (Exec.regions he (Code.noCalls_inlineAll pk_inlineOk_adx)).2.2
  obtain ⟨-, hwr, -, -, -, hro, hrs, -, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by
    refine Code.allInstrs_inlineAll ?_
    rw [← Code.allInstrs_mapBlocks (f := Instr.erase) fun i => by rw [loadsMxcsr_erase]]
    show publicKeyP521AdxErased.allInstrs _ = true
    lit_decide) he
    ⟨fun r hr => ?_, ?_⟩, post_of_x hpost⟩
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

theorem pk_ct_adx : ConstantTime isa pkX86_64.pre pkX86_64.pub publicKeyP521Adx := by
  obtain ⟨_, hc⟩ : ∃ h, ((taintSym ["VG_P521_COMB"]).check
      (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) publicKeyP521Adx h).isSome = true := by
    taint_decide_sum [Proof.P521.X86_64.combGXSum, Proof.P521.X86_64.invPXSum]
  refine VG.Taint.constantTime (A := taintSym ["VG_P521_COMB"]) (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) ?_ hc
  exact fun _ _ _ _ ⟨h0, h1, h2, h3, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h0, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩

theorem pk_verified_adx (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target publicKeyP521Adx
      (Spec.EcKey.P521.inst.publicKeyContract (X86_64.abi.withConsts p521.combConsts) 16) :=
  Verified.of_inlineAll_ct pk_inlineOk_adx (by decide) (pk_x86_adx hL hT hI) pk_ct_adx implies16
    (fun _ h => Sig.clearN_of_pre_consts (d := 1) h) pk_patch


theorem publicKeyAdx_codeSp : (publicKeyP521Adx).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `vg_ec_p521_public_key_adx` as emitted (`Impl.EcKey.X86_64.Fn.publicKeyP521Adx`), its cleanup included, meets its contract in
constant time and returns without secret residue. -/
theorem publicKeyAdx_scrubbed (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    VerifiedScrubbed X86_64.target Impl.EcKey.X86_64.Fn.publicKeyP521Adx
      (Spec.EcKey.P521.publicKeyApi.contract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p521.combConsts) 16) 32 :=
  X86_64.Scrub.verifiedScrubbedAll (api := Spec.EcKey.P521.publicKeyApi)
    { code := publicKeyP521Adx
      stack := 16
      verified := pk_verified_adx hL hT hI
      spSafe := publicKeyAdx_codeSp } .avx (EcKey.X86_64.Scrub.publicKeyOut_consts Spec.EcKey.P521.inst 16 Impl.Ecdsa.X86_64.p521.combConsts)

theorem publicKeyAdx_spSafe : Impl.EcKey.X86_64.Fn.publicKeyP521Adx.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe publicKeyAdx_codeSp

end VG.Proof.EcKey.X86_64.P521
