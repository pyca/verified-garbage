module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.Verified
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Spec.EcKey.Generic
meta import VerifiedGarbage.Spec.EcKey.Generic

/-!
# Deterministic ECDSA on x86-64: brainpoolP256r1

brainpoolp256r1 as the proof's curve (`brainpoolp256r1`): scalars of 32 bytes in 4 words, the
order `n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_brainpoolp256r1_sign`,
proven correct (given the group law and the inversions'
soundness) and constant time against its contract (`coreK` at brainpoolP256r1's sizes,
which is `Proof.Ecdsa.X86_64.BrainpoolP256r1.signX86_64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

theorem coreK_brainpoolp256r1 : coreK Impl.Ecdsa.X86_64.brainpoolp256r1 = Proof.Ecdsa.X86_64.BrainpoolP256r1.signX86_64 := by
  simp only [coreK, TblsOk, Impl.Ecdsa.X86_64.Cfg.combConsts, Impl.Ecdsa.X86_64.brainpoolp256r1,
    Abi.constRegions, Abi.constsHeld, List.map_nil, List.append_nil, List.not_mem_nil, false_implies,
    implies_true, and_true, Proof.Ecdsa.X86_64.BrainpoolP256r1.signX86_64]
  rfl

/-- The blocks that depend on the curve, checked once. -/
theorem brainpoolp256r1_blks : CurveBlks (cfgC Impl.Ecdsa.X86_64.brainpoolp256r1 false 0) where
  prepCase := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro D (rfl | rfl | rfl | rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  post := by exact ⟨_, by taint_decide⟩
  msg₀ := by exact ⟨_, by taint_decide⟩
  msg₀f := by exact ⟨_, by taint_decide⟩
  msg₁f := by exact ⟨_, by taint_decide⟩
  appendV := by exact ⟨_, by taint_decide⟩
  conv := by exact ⟨_, by taint_decide⟩
  sp := by unfold CurveInstrs; decide +kernel
  mx := by unfold CurveInstrs; decide +kernel

/-- brainpoolp256r1, with the group law `hL` and the inversions'
soundness `hI`. -/
def brainpoolp256r1 (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.brainpoolp256r1
  inst := Spec.Ecdsa.BrainpoolP256r1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inl rfl, Proof.Ecdsa.X86_64.BrainpoolP256r1.brainpoolp256r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.BrainpoolP256r1.brainpoolp256r1_sh
  coreN := Spec.Ecdsa.BrainpoolP256r1.signApi.name
  coreC := Impl.Ecdsa.X86_64.signBrainpoolP256r1
  coreX := by rw [coreK_brainpoolp256r1]; exact Proof.Ecdsa.X86_64.BrainpoolP256r1.sign_call_x86 hL hI
  coreCT := by rw [coreK_brainpoolp256r1]; exact Proof.Ecdsa.X86_64.BrainpoolP256r1.sign_ct
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  blks := brainpoolp256r1_blks

end VG.Proof.Ecdsa.Rfc6979.X86_64
