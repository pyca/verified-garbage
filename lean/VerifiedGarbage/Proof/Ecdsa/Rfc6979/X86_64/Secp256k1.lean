import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Verified

/-!
# Deterministic ECDSA on x86-64: secp256k1

secp256k1 as the proof's curve (`secp256k1`): scalars of 32 bytes in 4 words, the
order `n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_secp256k1_sign`,
proven correct (given the group law and the inversions'
soundness) and constant time against its contract (`coreK` at secp256k1's sizes,
which is `Proof.Ecdsa.X86_64.Secp256k1.signX86_64`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

theorem coreK_secp256k1 : coreK Impl.Ecdsa.X86_64.secp256k1 = Proof.Ecdsa.X86_64.Secp256k1.signX86_64 := by
  simp only [coreK, TblsOk, Impl.Ecdsa.X86_64.Cfg.combConsts, Impl.Ecdsa.X86_64.secp256k1,
    Abi.constRegions, Abi.constsHeld, List.map_nil, List.append_nil, List.not_mem_nil, false_implies,
    implies_true, and_true, Proof.Ecdsa.X86_64.Secp256k1.signX86_64]
  rfl

/-- secp256k1, with the group law `hL` and the inversions'
soundness `hI`. -/
def secp256k1 (hL : Weierstrass.Law Spec.Secp256k1.curve)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.secp256k1
  inst := Spec.Ecdsa.Secp256k1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inl rfl, Proof.Ecdsa.X86_64.Secp256k1.secp256k1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.Secp256k1.secp256k1_sh
  coreN := Spec.Ecdsa.Secp256k1.signApi.name
  coreC := Impl.Ecdsa.X86_64.signSecp256k1
  coreX := by rw [coreK_secp256k1]; exact fun s h _ => Proof.Ecdsa.X86_64.Secp256k1.sign_x86 hL hI s h
  coreCT := by rw [coreK_secp256k1]; exact Proof.Ecdsa.X86_64.Secp256k1.sign_ct
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  reduceT := Function.const _ ⟨_, by taint_decide⟩
  reduceSp := Function.const _ (by decide +kernel)
  reduceMx := Function.const _ (by decide +kernel)

end VG.Proof.Ecdsa.Rfc6979.X86_64
