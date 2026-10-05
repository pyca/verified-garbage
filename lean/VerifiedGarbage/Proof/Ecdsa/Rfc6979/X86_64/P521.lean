import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified

/-!
# Deterministic ECDSA on x86-64: P-521

P-521 as the proof's curve (`p521`): scalars of 9 words and 66 bytes, longer
than any hash function's output (`wide`), the order `n` of 521 bits, so that
the signature drops 7 bits of a 66-byte digest, and `vg_ecdsa_p521_sign`,
proven correct (given the group law) and constant time against its contract
(`coreK` at P-521's sizes, with no tables, which is `Proof.Ecdsa.X86_64.P521.signX86_64`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

theorem p521_combConsts : Impl.Ecdsa.X86_64.p521.combConsts = [] := rfl

/-- `coreK` at P-521's sizes, with no tables, is `Proof.Ecdsa.X86_64.P521.signX86_64`. -/
theorem coreK_p521 : coreK Impl.Ecdsa.X86_64.p521 = Proof.Ecdsa.X86_64.P521.signX86_64 := by
  simp only [coreK, TblsOk, p521_combConsts, Abi.constRegions, Abi.constsHeld, List.map_nil, List.append_nil,
    List.not_mem_nil, false_implies, implies_true, and_true, Proof.Ecdsa.X86_64.P521.signX86_64]
  rfl

/-- P-521, with the group law `hL`. -/
def p521 (hL : Weierstrass.Law Spec.P521.curve) : RfcCurve where
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
  coreX := by rw [coreK_p521]; exact Proof.Ecdsa.X86_64.P521.sign_x86 hL
  coreCT := by rw [coreK_p521]; exact Proof.Ecdsa.X86_64.P521.sign_ct
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  reduceT := nofun
  reduceSp := nofun
  reduceMx := nofun

end VG.Proof.Ecdsa.Rfc6979.X86_64
