import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified

/-!
# Deterministic ECDSA on x86-64: P-224

P-224 as the proof's curve (`p224`): scalars of 28 bytes in 4 words, the
order `n` of exactly 224 bits with `2^224 < 2 n`, and `vg_ecdsa_p224_sign`,
proven correct (given the group law, the comb's tables and the inversions'
soundness) and constant time against its contract (`coreK` at P-224's sizes,
which is `Proof.Ecdsa.X86_64.P224.signX86_64`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

/-- `coreK` at P-224's sizes is `Proof.Ecdsa.X86_64.P224.signX86_64` (by rewriting, as
deciding it would evaluate the tables' length). -/
theorem coreK_p224 : coreK Impl.Ecdsa.X86_64.p224 = Proof.Ecdsa.X86_64.P224.signX86_64 := by
  simp only [coreK, TblsOk, Proof.Ecdsa.X86_64.P224.p224_combConsts, Abi.constRegions, Abi.constsHeld,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true, Proof.Ecdsa.X86_64.P224.signX86_64, Proof.Ecdsa.X86_64.P224.TblHeld]
  rfl

/-- P-224, with the group law `hL`, the comb's tables `hT` and the inversions'
soundness `hI`. -/
def p224 (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.p224
  inst := Spec.Ecdsa.P224.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inr ⟨rfl, rfl⟩, Proof.Ecdsa.X86_64.P224.p224_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.P224.p224_sh
  coreN := Spec.Ecdsa.P224.signApi.name
  coreC := Impl.Ecdsa.X86_64.signP224
  coreX := by rw [coreK_p224]; exact Proof.Ecdsa.X86_64.P224.sign_x86 hL hT hI
  coreCT := by rw [coreK_p224]; exact Proof.Ecdsa.X86_64.P224.sign_ct
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  reduceT := Function.const _ ⟨_, by taint_decide⟩
  reduceSp := Function.const _ (by decide +kernel)
  reduceMx := Function.const _ (by decide +kernel)

end VG.Proof.Ecdsa.Rfc6979.X86_64
