module

import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Verified
public import VerifiedGarbage.Proof.Ecdh.X86_64.Main
public import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.VerifiedAdx
import VerifiedGarbage.Proof.Ecdh.X86_64.MulJ4
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Ecdh.X86_64.P521.LitAdx
import VerifiedGarbage.Proof.P521.X86_64.TaintSumsWinAdx
public import VerifiedGarbage.Impl.Ecdh.P521.X86_64
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.LitAdx
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJStep
meta import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Verified
meta import VerifiedGarbage.Proof.Ecdh.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.VerifiedAdx
meta import VerifiedGarbage.Proof.Ecdh.X86_64.MulJ4
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Ecdh.X86_64.P521.LitAdx
meta import VerifiedGarbage.Proof.P521.X86_64.TaintSumsWinAdx
meta import VerifiedGarbage.Impl.Ecdh.P521.X86_64
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Lit
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.LitAdx
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJStep
public import VerifiedGarbage.Proof.P521.X86_64.TaintSumsWin

/-!
# ECDH over P-521 on x86-64 with BMI2 and ADX: `Verified`

As `Verified.lean`, for `p521x` (`p521` multiplying modulo `p` with BMI2 and
ADX): the same curve, so the same precondition and postcondition.
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64.P521

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P521

theorem pre_of_x {s : State} (h : ecdhX86_64.pre s) : EPre p521x s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, -, -, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h10, h11⟩

theorem post_of_x {s s' : State} (h : EPost p521x s s') : ecdhX86_64.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .rsi) (s.gpr .rdx) with
    | some z => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 66 = z
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 66 = List.replicate 66 0
  revert h
  generalize hq : ex s.mem (s.gpr .rsi) (s.gpr .rdx) = q
  rw [show Spec.Ecdh.exchange p521x.C (dk p521x s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .rdx) (1 + 2 * p521x.C.len)) = ex s.mem (s.gpr .rsi) (s.gpr .rdx) from rfl, hq]
  rcases q with _ | z <;> exact id

/-! The facts about every instruction, each its own declaration: the code is
large enough that the two in one would leave `ecdh_x86` little of its
budget. -/

theorem ecdh_inlineOk_adx : exchangeP521Adx.InlineOk = true := by lit_decide

theorem ecdh_noCalls_adx : exchangeP521Adx.inline.noCalls = true := Code.noCalls_inline ecdh_inlineOk_adx

theorem ecdh_mxcsr_adx : exchangeP521Adx.inline.allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [Code.allInstrs_inline]; lit_decide

theorem ecdh_x86_adx (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P521.curve) (s : State) (hs : ecdhX86_64.pre s) :
    ∃ t s', Exec isa exchangeP521Adx.inline s t s' ∧ abiPreserved s s' ∧ ecdhX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := exchangeWith_ok (c := p521x) (p521x_ok hI).toBaseCfgOk hL
    (mulQJ4_ok (p521x_ok hI) (by decide) hL hO (by decide +kernel)) (mulQJ4_w (p521x_ok hI)) (pre_of_x hs)
  have hsp := Code.clobbers_rsp_of_inlineOk ecdh_inlineOk_adx
  have F := (Exec.regions he ecdh_noCalls_adx).2.2
  obtain ⟨-, hwr, -, -, -, -, -, hro, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec ecdh_mxcsr_adx he ⟨fun r hr => ?_, ?_⟩, post_of_x hpost⟩
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

theorem ecdh_ct_adx : ConstantTime isa ecdhX86_64.pre ecdhX86_64.pub exchangeP521Adx := by
  obtain ⟨_, hc⟩ : ∃ h, (taintS.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) exchangeP521Adx h).isSome = true := by
    taint_decide_sum [Proof.P521.X86_64.winBuildJXSum, Proof.P521.X86_64.winNormJXSum,
      Proof.P521.X86_64.winLoopJXSum, Proof.P521.X86_64.winLastJXSum]
  refine VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) ?_ hc
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h0

theorem ecdh_verified_adx (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P521.curve) :
    Verified X86_64.target exchangeP521Adx (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst X86_64.abi 8) :=
  Verified.of_inline_ct ecdh_inlineOk_adx (ecdh_x86_adx hL hI hO) ecdh_ct_adx implies8
    (fun _ h => Sig.clear_of_pre h) ecdh_patch

end VG.Proof.Ecdh.X86_64.P521
