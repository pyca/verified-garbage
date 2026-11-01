module

import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitAdx
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitAdx

import VerifiedGarbage.Proof.P384.Order
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulBase
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.P384.Prime
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitEraseAdx
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.MulBase
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Contract
meta import VerifiedGarbage.Proof.P384.Prime
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
meta import VerifiedGarbage.Proof.P384.Point
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitEraseAdx
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA

/-!
# ECDSA over P-384 on x86-64 with BMI2 and ADX: `Verified`

`p384x` is `p384` multiplying modulo `p` and `n` with BMI2 and ADX
(`Mod.adx`) and selecting the comb's entries with AVX2, which the proof of
`sign_ok` covers as it covers any multiplication (`Proof/Mont/X86_64/Adx.lean`)
and either selection (`selPassV_ok`): the same curve, so the same facts
(`p384x_ok`, from `p384_ok`) and the same precondition.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.P384

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

/-! `p384x` is `p384` but for `adx` and `avx2`: its other fields, rewritten rather than
compared by unfolding (which would evaluate the order's bits). -/

theorem p384x_C : p384x.C = p384.C := rfl
theorem p384x_n : p384x.n = p384.n := rfl
theorem p384x_comb : p384x.comb = p384.comb := rfl

theorem p384x_sh : p384x.sh = 0 := by
  unfold Cfg.sh
  rw [p384x_C]
  exact p384_sh

theorem p384x_combConsts : p384x.combConsts = [("VG_P384_COMB", p384W)] := by
  unfold Cfg.combConsts Cfg.combWords Cfg.R
  rw [p384x_comb, p384x_C, p384x_n]
  rfl

theorem p384x_ok (hI : InvSounds) : CfgOk p384x where
  n0 := by decide
  n10 := by decide
  onG := Proof.P384.onCurve_G
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
  mask h := absurd h (by decide)
  sh := by rw [p384x_sh]; decide
  comb d h := by cases h; exact ⟨by decide, by decide, by decide⟩
  inv _ := ⟨by decide, @hI _ _ (by
    show Nat.Prime Spec.P384.curve.p
    rw [show Spec.P384.curve.p =
      39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319
      by decide +kernel]
    exact Proof.P384.prime_39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319),
    InvOk.ofMod (by decide +kernel) (by decide)⟩
  inv_n _ _ := ⟨@hI _ p384x.C.n_ne_zero Proof.P384.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  window_am3 := fun _ => by unfold AM3; decide +kernel
  comb_am3 := fun _ _ => by unfold AM3; decide +kernel
  am3 := by unfold AM3; decide +kernel
  even _ := by decide
  inverse _ := ⟨by decide, rfl⟩

/-- `[k]G` is a call of `vg_p384_mul_base_adx`, which calls no other function. -/
theorem p384x_mulBase : MulBaseOk p384x :=
  ⟨fun _ => ⟨_, rfl, by decide, by lit_decide⟩, fun h => absurd h (by decide)⟩

theorem p384x_tbls (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) :
    CombTbls p384x := fun d h => by cases h; exact ⟨hT, fun _ => Proof.P384.booth hL rfl rfl⟩

theorem pre_of_x {s : State} (h : signX86_64.pre s) : Pre p384x s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, h12, h13, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p384x_combConsts, p384x_C, show p384.C.len = 48 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h6, h7, h8, h9, h12, h13, ?_⟩
  rw [TblsHeld, p384x_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h]

/-- The inlining checks, shared by correctness and the two call wrappers. -/
theorem sign_inlineOk_adx : signP384Adx.InlineOk = true := by lit_decide

theorem sign_x86_adx (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : InvSounds) (s : State)
    (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signP384Adx.inline s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok (p384x_ok hI) hL (p384x_tbls hL hT) (pre_of_x hs) p384x_mulBase
  have hok := sign_inlineOk_adx
  have hsp := Code.clobbers_rsp_of_inlineOk hok
  have hmx : signP384Adx.inline.allInstrs (fun i => !loadsMxcsr i) = true := by
    rw [Code.allInstrs_inline]; lit_decide
  have F := (Exec.regions he (Code.noCalls_inline hok)).2.2
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

theorem sign_ct_adx : ConstantTime isa signX86_64.pre signX86_64.pub signP384Adx :=
  VG.Taint.constantTime_mapBlocks (c' := signErasedAdx) (taintSym_eraseInv ["VG_P384_COMB"])
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) rfl
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, h5, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h0, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    rfl (by taint_decide)

theorem sign_verified_adx (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : InvSounds) :
    Verified X86_64.target signP384Adx
      (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P384.inst (X86_64.abi.withConsts p384.combConsts) 8) :=
  Verified.of_inline_ct sign_inlineOk_adx (sign_x86_adx hL hT hI) sign_ct_adx implies8
    (fun _ h => Sig.clear_of_pre_consts h) sign_patch

/-- `sign_call_x86` with BMI2 and ADX. -/
theorem sign_call_x86_adx (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : InvSounds) (s : State) (hs : signX86_64.pre s) (hc : Clear (hole (s.gpr .rsp)) s) :
    ∃ t s', Exec isa signP384Adx s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' :=
  ok_of_inline (k := signX86_64) sign_inlineOk_adx (sign_x86_adx hL hT hI)
    (fun s b hv u hs hc hp => post_patch s b hv u hs hc hp) s ⟨hs, hc⟩

end VG.Proof.Ecdsa.X86_64.P384
