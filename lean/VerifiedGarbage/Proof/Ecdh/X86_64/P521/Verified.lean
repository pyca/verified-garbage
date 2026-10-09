import VerifiedGarbage.Proof.Ecdh.X86_64.Main
import VerifiedGarbage.Proof.Ecdh.X86_64.MulJ4
import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Contract
import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
import VerifiedGarbage.Proof.P521.X86_64.TaintSumsWin
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified

/-!
# ECDH over P-521 on x86-64: `Verified`

P-521 is a curve the proof supports (`p521_ok`, and `Law` for its group law
and `InvSounds` for its inversions, which the registration file supplies:
`Proof.P521.law` and the variant's `inv`), of prime order (the variant's
`prime`), so its 4-bit windows with a Jacobian accumulator compute `[d]P`
(`mulQJ4_ok`) and `exchangeWith_ok`
gives the contract's postcondition; the callee-saved registers are restored,
`rsp` is never written, and every store is to `out` or `scratch`, which the
return address is apart from (`abiPreserved`). Constant time by taint
tracking: the only branches are on loop counters, and every address is an
argument plus a constant or a counter, so not even the peer's key (which the
contract would let leak) affects timing.
-/

namespace VG.Proof.Ecdh.X86_64.P521

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P521

theorem pre_of {s : State} (h : ecdhX86_64.pre s) : EPre p521 s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, -, -, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h10, h11⟩

theorem post_of {s s' : State} (h : EPost p521 s s') : ecdhX86_64.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .rsi) (s.gpr .rdx) with
    | some z => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 66 = z
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 66 = List.replicate 66 0
  revert h
  generalize hq : ex s.mem (s.gpr .rsi) (s.gpr .rdx) = q
  rw [show Spec.Ecdh.exchange p521.C (dk p521 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .rdx) (1 + 2 * p521.C.len)) = ex s.mem (s.gpr .rsi) (s.gpr .rdx) from rfl, hq]
  rcases q with _ | z <;> exact id

/-! The facts about every instruction, each its own declaration: the code is
large enough that the three in one would leave `ecdh_x86` little of its
budget. -/

theorem ecdh_rsp : exchangeP521.inline.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  rw [Code.allInstrs_inline]; lit_decide

theorem ecdh_inlineOk : exchangeP521.InlineOk = true := by lit_decide

theorem ecdh_noCalls : exchangeP521.inline.noCalls = true := Code.noCalls_inline ecdh_inlineOk

theorem ecdh_mxcsr : exchangeP521.inline.allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [Code.allInstrs_inline]; lit_decide

theorem ecdh_x86 (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P521.curve) (s : State) (hs : ecdhX86_64.pre s) :
    ∃ t s', Exec isa exchangeP521.inline s t s' ∧ abiPreserved s s' ∧ ecdhX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := exchangeWith_ok (c := p521) (p521_ok hI).toBaseCfgOk hL
    (mulQJ4_ok (p521_ok hI) (by decide) hL hO (by decide +kernel)) (mulQJ4_w (p521_ok hI)) (pre_of hs)
  have hsp : ∀ i ∈ instrs exchangeP521.inline, Taint.clobbers i .rsp = false := by
    have h := ecdh_rsp
    rw [Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he ecdh_noCalls).2.2
  obtain ⟨-, hwr, -, -, -, -, -, hro, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec ecdh_mxcsr he ⟨fun r hr => ?_, ?_⟩, post_of hpost⟩
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

theorem ecdh_ct : ConstantTime isa ecdhX86_64.pre ecdhX86_64.pub exchangeP521 := by
  obtain ⟨_, hc⟩ : ∃ h, (taintS.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) exchangeP521 h).isSome = true := by
    taint_decide_sum [Proof.P521.X86_64.winBuildJSum, Proof.P521.X86_64.winNormJSum,
      Proof.P521.X86_64.winLoopJSum, Proof.P521.X86_64.winLastJSum]
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

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 :
    ecdhX86_64.Implies (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst X86_64.abi 8) :=
  implies.stack8_abi (by
    sig_implies_sat [Spec.EcKey.P521.inst, Spec.Ecdh.Instance.exchangeContract,
      Spec.Ecdh.Instance.exchangeSig, Spec.P521.curve, Spec.EcKey.scratchWords, X86_64.abi,
      X86_64.argRegs, satState] [satState] using satState)

/-- The output is apart from the calls' return address. -/
theorem ecdh_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst X86_64.abi 8).pre s)
    (hp : ecdhX86_64.post s b) : ecdhX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -⟩ := implies8.pre s hs
  have hb := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := 66)
    (by rw [hwr]; simp) (by decide)
  simpa only [ecdhX86_64, State.patch_gpr, EcKey.bytesAt_patch hb] using hp

theorem ecdh_verified (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P521.curve) :
    Verified X86_64.target exchangeP521 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst X86_64.abi 8) :=
  Verified.of_inline_ct ecdh_inlineOk (ecdh_x86 hL hI hO) ecdh_ct implies8
    (fun _ h => Sig.clear_of_pre h) ecdh_patch

end VG.Proof.Ecdh.X86_64.P521
