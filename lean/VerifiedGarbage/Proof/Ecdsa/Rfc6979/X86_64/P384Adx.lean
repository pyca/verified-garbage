import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P384
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx

/-!
# Deterministic ECDSA on x86-64: P-384 with BMI2 and ADX

As `P384.lean`, with `vg_ecdsa_p384_sign_adx` (`p384x`, P-384 multiplying
with BMI2 and ADX), proven correct and constant time against the same
contract; `p384Of` is either.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

/-- `coreK` is the same for `p384x` as for `p384`, the same curve. -/
theorem coreK_p384x : coreK Impl.Ecdsa.X86_64.p384x = Proof.Ecdsa.X86_64.P384.signX86_64 := by
  simp only [coreK, TblsOk, Proof.Ecdsa.X86_64.P384.p384x_combConsts, Proof.Ecdsa.X86_64.P384.p384x_C,
    Abi.constRegions, Abi.constsHeld, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true,
    Proof.Ecdsa.X86_64.P384.signX86_64, Proof.Ecdsa.X86_64.P384.TblHeld]
  rfl

/-- P-384 with BMI2 and ADX, with the group law `hL`, the comb's tables `hT`
and the inversions' soundness `hI`. -/
def p384x (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.p384x
  inst := Spec.Ecdsa.P384.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr rfl, .inl rfl, p384_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.P384.p384x_sh
  coreN := Spec.Ecdsa.P384.signApi.name ++ "_adx"
  coreC := Impl.Ecdsa.X86_64.signP384Adx
  coreX := by rw [coreK_p384x]; exact fun s h _ => Proof.Ecdsa.X86_64.P384.sign_x86_adx hL hT hI s h
  coreCT := by rw [coreK_p384x]; exact Proof.Ecdsa.X86_64.P384.sign_ct_adx
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  reduceT := (p384 hL hT hI).reduceT
  reduceSp := (p384 hL hT hI).reduceSp
  reduceMx := (p384 hL hT hI).reduceMx

/-- P-384 with BMI2 and ADX (`adx`) or without. -/
def p384Of (adx : Bool) (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve :=
  bif adx then p384x hL hT hI else p384 hL hT hI

end VG.Proof.Ecdsa.Rfc6979.X86_64
