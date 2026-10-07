import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified

/-!
# Deterministic ECDSA on x86-64: P-384

P-384 as the proof's curve (`p384`): scalars of 6 words, the order `n` of
exactly 384 bits with `2^384 < 2 n`, and `vg_ecdsa_p384_sign`, proven correct
(given the group law and the comb's tables) and constant time against its
contract (`coreK` at P-384's sizes, which is `Proof.Ecdsa.X86_64.P384.signX86_64`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

theorem p384_nBits : Spec.Ecdsa.nBits Spec.P384.curve = 384 := by
  show Spec.P384.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.P384.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P384.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- `coreK` at P-384's sizes is `Proof.Ecdsa.X86_64.P384.signX86_64` (by rewriting, as
deciding it would evaluate the tables' length). -/
theorem coreK_p384 : coreK Impl.Ecdsa.X86_64.p384 = Proof.Ecdsa.X86_64.P384.signX86_64 := by
  simp only [coreK, TblsOk, Proof.Ecdsa.X86_64.P384.p384_combConsts, Abi.constRegions_cons,
    Abi.constRegions_nil, Sig.forall_mem_const_single]
  simp only [Abi.constsHeld, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true, Proof.Ecdsa.X86_64.P384.signX86_64, Proof.Ecdsa.X86_64.P384.TblHeld]
  rfl

/-- P-384, with the group law `hL`, the comb's tables `hT` and the inversions'
soundness `hI`. -/
def p384 (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.p384
  inst := Spec.Ecdsa.P384.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr rfl, .inl rfl, p384_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.P384.p384_sh
  coreN := Spec.Ecdsa.P384.signApi.name
  coreC := Impl.Ecdsa.X86_64.signP384
  coreX := by rw [coreK_p384]; exact Proof.Ecdsa.X86_64.P384.sign_x86 hL hT hI
  coreCT := by rw [coreK_p384]; exact Proof.Ecdsa.X86_64.P384.sign_ct
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  reduceT := Function.const _ ⟨_, by taint_decide⟩
  reduceSp := Function.const _ (by decide +kernel)
  reduceMx := Function.const _ (by decide +kernel)

end VG.Proof.Ecdsa.Rfc6979.X86_64
