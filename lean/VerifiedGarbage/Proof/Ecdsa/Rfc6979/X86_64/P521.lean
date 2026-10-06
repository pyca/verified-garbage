import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified

/-!
# Deterministic ECDSA on x86-64: P-521

P-521 as the proof's curve (`p521`): scalars of 9 words and 66 bytes, longer
than any hash function's output (`wide`), the order `n` of 521 bits, so that
the signature drops 7 bits of a 66-byte digest, and `vg_ecdsa_p521_sign`,
proven correct (given the group law and the comb's tables) and constant time
against its contract (`coreK` at P-521's sizes, which is
`Proof.Ecdsa.X86_64.P521.signX86_64`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

/-- `coreK` at P-521's sizes is `Proof.Ecdsa.X86_64.P521.signX86_64` (by rewriting, as
deciding it would evaluate the tables' length). -/
theorem coreK_p521 : coreK Impl.Ecdsa.X86_64.p521 = Proof.Ecdsa.X86_64.P521.signX86_64 := by
  simp only [coreK, TblsOk, Proof.Ecdsa.X86_64.P521.p521_combConsts, Proof.Ecdsa.X86_64.P521.p521_constRegions,
    Abi.constsHeld, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, Proof.Ecdsa.X86_64.P521.signX86_64, Proof.Ecdsa.X86_64.P521.TblHeld]
  rfl

/-- P-521, with the group law `hL` and the comb's tables `hT`. -/
def p521 (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) :
    RfcCurve where
  E := Impl.Ecdsa.X86_64.p521
  inst := Spec.Ecdsa.P521.inst
  curve := rfl
  wide := true
  sizes := ⟨rfl, rfl, Proof.Ecdsa.X86_64.P521.p521_nBits⟩
  n_lt := by decide +kernel
  sh := 7
  sh_eq := Proof.Ecdsa.X86_64.P521.p521_sh
  coreN := Spec.Ecdsa.P521.signApi.name
  coreC := Impl.Ecdsa.X86_64.signP521
  coreX := by rw [coreK_p521]; exact Proof.Ecdsa.X86_64.P521.sign_x86 hL hT
  coreCT := by rw [coreK_p521]; exact Proof.Ecdsa.X86_64.P521.sign_ct
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  reduceT := nofun
  reduceSp := nofun
  reduceMx := nofun

end VG.Proof.Ecdsa.Rfc6979.X86_64
