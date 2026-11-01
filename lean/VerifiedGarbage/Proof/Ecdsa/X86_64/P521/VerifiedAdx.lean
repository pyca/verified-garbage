module

import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.P521.X86_64.TaintSumsAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.RspMxcsr
import VerifiedGarbage.Proof.P521.Prime
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.LitAdx
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Contract
meta import VerifiedGarbage.Proof.P521.X86_64.TaintSumsAdx
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.RspMxcsr
meta import VerifiedGarbage.Proof.P521.Prime
meta import VerifiedGarbage.Proof.P521.Point
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.LitAdx
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase

/-!
# ECDSA over P-521 on x86-64 with BMI2 and ADX: `Verified`

`p521x` is `p521` multiplying modulo `p` with BMI2 and ADX (`Mod.adx`) and
selecting the comb's entries with AVX2, which the proof of `sign_ok` covers
as it covers any multiplication (`Proof/Mont/X86_64/MulPX.lean`) and either
selection (`selPassV_ok`): the same curve, so the same facts
(`p521x_ok`, from `p521_ok`) and the same precondition.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.P521

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

/-! `p521x` is `p521` but for `adx` and `avx2`: its other fields, rewritten rather than
compared by unfolding (which would evaluate the order's bits). -/

theorem p521x_C : p521x.C = p521.C := rfl
theorem p521x_n : p521x.n = p521.n := rfl
theorem p521x_comb : p521x.comb = p521.comb := rfl

theorem p521x_sh : p521x.sh = 7 := by
  unfold Cfg.sh
  rw [p521x_C]
  exact p521_sh

theorem p521x_combConsts : p521x.combConsts = [("VG_P521_COMB", p521W)] := by
  unfold Cfg.combConsts Cfg.combWords Cfg.R
  rw [p521x_comb, p521x_C, p521x_n]
  rfl

theorem p521x_ok (hI : InvSounds) : CfgOk p521x where
  n0 := by decide
  n10 := by decide
  onG := Proof.P521.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  red_p := by decide +kernel
  red_n := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  n_len := by decide +kernel
  n_bits := by decide +kernel
  nbits_le := by decide
  mask _ := ⟨by decide, by decide⟩
  sh := by rw [p521x_sh]; decide
  comb d h := by cases h; exact ⟨by decide, by decide, by decide⟩
  inv _ := ⟨by decide, @hI _ _ (by
    show Nat.Prime Spec.P521.curve.p
    rw [show Spec.P521.curve.p =
      6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151
      by decide +kernel]
    exact Proof.P521.prime_6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151),
    InvOk.ofMod (by decide +kernel) (by decide)⟩
  inv_n _ _ := ⟨@hI _ p521x.C.n_ne_zero Proof.P521.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  window_am3 := fun _ => by unfold AM3; decide +kernel
  comb_am3 := fun _ _ => by unfold AM3; decide +kernel
  am3 := by unfold AM3; decide +kernel
  even h := absurd h (by decide)
  inverse _ := ⟨by decide, rfl⟩

theorem p521x_tbls (hT : CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) :
    CombTbls p521x := fun d h => by cases h; exact ⟨hT, fun h => absurd h (by decide)⟩

theorem pre_of_x {s : State} (h : signX86_64.pre s) : Pre p521x s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, h12, h13, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p521x_combConsts, p521_constRegions, p521x_C, show p521.C.len = 66 from rfl]; simp only [
    List.cons_append, List.nil_append], h2, h3, h4, h5, h6, h7, h8, h9, h12, h13, ?_⟩
  rw [TblsHeld, p521x_combConsts]
  refine ⟨fun c hc => ?_, fun t ht => ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · simp only [p521_constRegions, List.mem_singleton] at ht; subst ht
    refine ⟨fit, fun r hr => hdw r ?_⟩
    rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h]

/-- `InlineOk`, checked once for every theorem that needs it. -/
theorem sign_inlineOk_adx : signP521Adx.InlineOk = true := by lit_decide

theorem sign_x86_adx (hL : Law Spec.P521.curve)
    (hT : CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : InvSounds) (s : State)
    (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signP521Adx.inline s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok (c := p521x) (p521x_ok hI).toBaseCfgOk hL (p521x_tbls hT) (pre_of_x hs)
  obtain ⟨hsp, hmx⟩ := rsp_mxcsr (c := signP521Adx) (by lit_decide)
  have F := (Exec.regions he (Code.noCalls_inline sign_inlineOk_adx)).2.2
  obtain ⟨-, hwr, -, -, -, -, -, -, -, hro, hrs, -, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec hmx he
    ⟨fun r hr => ?_, ?_⟩, hpost⟩
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

theorem sign_ct_adx : ConstantTime isa signX86_64.pre signX86_64.pub signP521Adx := by
  obtain ⟨_, hc⟩ : ∃ h, ((taintSym ["VG_P521_COMB"]).check
      (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) signP521Adx h).isSome = true := by
    taint_decide_sum [Proof.P521.X86_64.combGXSum, Proof.P521.X86_64.invPXSum]
  refine VG.Taint.constantTime (A := taintSym ["VG_P521_COMB"])
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) ?_ hc
  exact fun _ _ _ _ ⟨h0, h1, h2, h3, h4, h5, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h0, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩

theorem sign_verified_adx (hL : Law Spec.P521.curve)
    (hT : CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : InvSounds) :
    Verified X86_64.target signP521Adx
      (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P521.inst (X86_64.abi.withConsts p521.combConsts) 8) :=
  Verified.of_inline_ct sign_inlineOk_adx (sign_x86_adx hL hT hI) sign_ct_adx implies8
    (fun _ h => Sig.clear_of_pre_consts h) sign_patch

/-- `sign_call_x86` with BMI2 and ADX. -/
theorem sign_call_x86_adx (hL : Law Spec.P521.curve)
    (hT : CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : InvSounds) (s : State) (hs : signX86_64.pre s) (hc : Clear (hole (s.gpr .rsp)) s) :
    ∃ t s', Exec isa signP521Adx s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' :=
  ok_of_inline (k := signX86_64) sign_inlineOk_adx (sign_x86_adx hL hT hI)
    (fun s b hv u hs hc hp => post_patch s b hv u hs hc hp) s ⟨hs, hc⟩

end VG.Proof.Ecdsa.X86_64.P521
