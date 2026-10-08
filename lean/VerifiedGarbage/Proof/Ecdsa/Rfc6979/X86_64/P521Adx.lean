import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P521
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.VerifiedAdx

/-!
# Deterministic ECDSA on x86-64: P-521 with BMI2 and ADX

As `P521.lean`, with `vg_ecdsa_p521_sign_adx` (`p521x`, P-521 multiplying
modulo `p` with BMI2 and ADX), proven correct and constant time against the
same contract; `p521Of` is either.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

/-- `coreK` is the same for `p521x` as for `p521`, the same curve. -/
theorem coreK_p521x : coreK Impl.Ecdsa.X86_64.p521x = Proof.Ecdsa.X86_64.P521.signX86_64 := by
  simp only [coreK, TblsOk, Proof.Ecdsa.X86_64.P521.p521x_combConsts, Proof.Ecdsa.X86_64.P521.p521_constRegions,
    Proof.Ecdsa.X86_64.P521.p521x_C,
    Abi.constsHeld, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, Proof.Ecdsa.X86_64.P521.signX86_64, Proof.Ecdsa.X86_64.P521.TblHeld]
  rfl

/-- P-521 with BMI2 and ADX, with the group law `hL`, the comb's tables `hT`
and the inversions' soundness `hI`. -/
def p521x (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.p521x
  inst := Spec.Ecdsa.P521.inst
  curve := rfl
  wide := true
  sizes := ⟨rfl, rfl, Proof.Ecdsa.X86_64.P521.p521_nBits⟩
  n_lt := by decide +kernel
  sh := 7
  sh_eq := Proof.Ecdsa.X86_64.P521.p521x_sh
  coreN := Spec.Ecdsa.P521.signApi.name ++ "_adx"
  coreC := Impl.Ecdsa.X86_64.signP521Adx
  coreX := by rw [coreK_p521x]; exact Proof.Ecdsa.X86_64.P521.sign_call_x86_adx hL hT hI
  coreCT := by rw [coreK_p521x]; exact Proof.Ecdsa.X86_64.P521.sign_ct_adx
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  reduceT := nofun
  reduceSp := nofun
  reduceMx := nofun

/-- P-521 with BMI2 and ADX (`adx`) or without. -/
def p521Of (adx : Bool) (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve :=
  bif adx then p521x hL hT hI else p521 hL hT hI

end VG.Proof.Ecdsa.Rfc6979.X86_64
