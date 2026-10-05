import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified

/-!
# Deterministic ECDSA on x86-64: P-256

P-256 as the proof's curve (`p256`): scalars of 4 words, the order `n` of
exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_p256_sign`, proven correct
(given the group law and the comb's tables) and constant time against its
contract (`coreK` at P-256's sizes, which is `Proof.Ecdsa.X86_64.signX86_64`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

theorem p256_nBits : Spec.Ecdsa.nBits Spec.P256.curve = 256 := by
  show Spec.P256.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.P256.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P256.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- `coreK` at P-256's sizes is `Proof.Ecdsa.X86_64.signX86_64` (by rewriting, as
deciding it would evaluate the tables' length). -/
theorem coreK_p256 : coreK Impl.Ecdsa.X86_64.p256 = Proof.Ecdsa.X86_64.signX86_64 := by
  simp only [coreK, TblsOk, Proof.Ecdsa.X86_64.p256_combConsts, Abi.constRegions, Abi.constsHeld,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true, Proof.Ecdsa.X86_64.signX86_64, Proof.Ecdsa.X86_64.TblHeld]
  rfl

/-- P-256, with the group law `hL` and the comb's tables `hT`. -/
def p256 (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) : RfcCurve where
  E := Impl.Ecdsa.X86_64.p256
  inst := Spec.Ecdsa.P256.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, rfl, p256_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.p256_sh
  coreN := Spec.Ecdsa.P256.signApi.name
  coreC := Impl.Ecdsa.X86_64.signP256
  coreX := by rw [coreK_p256]; exact Proof.Ecdsa.X86_64.sign_x86 hL hT
  coreCT := by rw [coreK_p256]; exact Proof.Ecdsa.X86_64.sign_ct
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  reduceT := Function.const _ ⟨_, by taint_decide⟩
  reduceSp := Function.const _ (by decide +kernel)
  reduceMx := Function.const _ (by decide +kernel)

end VG.Proof.Ecdsa.Rfc6979.X86_64
