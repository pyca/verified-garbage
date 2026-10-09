import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.Verified

/-!
# Deterministic ECDSA on x86-64: p192

p192 as the proof's curve (`p192`): scalars of 24 bytes in 4 words, the
order `n` of exactly 192 bits with `2^192 < 2 n`, and `vg_ecdsa_p192_sign`,
proven correct (given the group law and the inversions'
soundness) and constant time against its contract (`coreK` at p192's sizes,
which is `Proof.Ecdsa.X86_64.P192.signX86_64`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

theorem coreK_p192 : coreK Impl.Ecdsa.X86_64.p192 = Proof.Ecdsa.X86_64.P192.signX86_64 := by
  simp only [coreK, TblsOk, Impl.Ecdsa.X86_64.Cfg.combConsts, Impl.Ecdsa.X86_64.p192,
    Abi.constRegions, Abi.constsHeld, List.map_nil, List.append_nil, List.not_mem_nil, false_implies,
    implies_true, and_true, Proof.Ecdsa.X86_64.P192.signX86_64]
  rfl

/-- p192, with the group law `hL` and the inversions'
soundness `hI`. -/
def p192 (hL : Weierstrass.Law Spec.P192.curve)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.p192
  inst := Spec.Ecdsa.P192.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inr ⟨rfl, .inr rfl⟩, Proof.Ecdsa.X86_64.P192.p192_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.P192.p192_sh
  coreN := Spec.Ecdsa.P192.signApi.name
  coreC := Impl.Ecdsa.X86_64.signP192
  coreX := by rw [coreK_p192]; exact fun s h _ => Proof.Ecdsa.X86_64.P192.sign_x86 hL hI s h
  coreCT := by rw [coreK_p192]; exact Proof.Ecdsa.X86_64.P192.sign_ct
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  reduceT := Function.const _ ⟨_, by taint_decide⟩
  reduceSp := Function.const _ (by decide +kernel)
  reduceMx := Function.const _ (by decide +kernel)

end VG.Proof.Ecdsa.Rfc6979.X86_64
