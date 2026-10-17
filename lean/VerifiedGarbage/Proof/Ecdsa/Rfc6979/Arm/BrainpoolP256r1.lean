module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Lit
public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# Deterministic ECDSA on 32-bit ARM: brainpoolP256r1

brainpoolP256r1 as the proof's curve (`brainpoolp256r1`): scalars of 4
64-bit words, the order `n` of exactly 256 bits with `2^256 < 2 n`, and
`vg_ecdsa_brainpoolp256r1_sign`, proven correct (given the group law) and
constant time against its contract (`coreK` at brainpoolP256r1's sizes,
which is `Proof.Ecdsa.Arm.BrainpoolP256r1.signArm`). Its instance of RFC
6979 is `Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst` (whose curve and
number of candidates the code uses), whose contract implies `rfcArm`
(`brainpoolp256r1_implies`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

theorem brainpoolp256r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP256r1.curve = 256 := by
  show Spec.BrainpoolP256r1.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.BrainpoolP256r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP256r1.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- brainpoolP256r1, with the group law `hL`. -/
def brainpoolp256r1 (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.brainpoolp256r1
  inst := Spec.Ecdsa.BrainpoolP256r1.inst
  curve := rfl
  I := Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst
  ecdsa := rfl
  tries_pos := by decide
  tries_lt := by decide
  wide := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, brainpoolp256r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.BrainpoolP256r1.curve = 0; rw [brainpoolp256r1_nBits]
  coreN := Spec.Ecdsa.BrainpoolP256r1.signApi.name
  coreC := Impl.Ecdsa.Arm.signBrainpoolP256r1
  coreX := Proof.Ecdsa.Arm.BrainpoolP256r1.sign_arm hL
  coreCT := Proof.Ecdsa.Arm.BrainpoolP256r1.sign_ct
  coreStack := by lit_decide
  blks := by exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- The contract of `vg_ecdsa_brainpoolp256r1_rfc6979_sign` implies `rfcArm`. -/
theorem brainpoolp256r1_implies : (rfcArm Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst 456).Implies (Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst.signAnyContract Arm.abi 456) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signAnyContract,
          Spec.Ecdsa.Rfc6979.Instance.signAnySig, Spec.Ecdsa.BrainpoolP256r1.inst, Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm, stkR]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signAnyContract,
          Spec.Ecdsa.Rfc6979.Instance.signAnySig, Spec.Ecdsa.BrainpoolP256r1.inst, Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm, stkR, anyResult]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signAnyContract,
          Spec.Ecdsa.Rfc6979.Instance.signAnySig, Spec.Ecdsa.BrainpoolP256r1.inst, Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm, stkR] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5⟩ := h
        exact ⟨hsp, h0, h1, h2, h3, h4, h5, (List.cons.inj hl).1⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signAnyContract,
          Spec.Ecdsa.Rfc6979.Instance.signAnySig, Spec.Ecdsa.BrainpoolP256r1.inst, Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm, stkR] [satState, satMem] using satState 32 32 3 }

end VG.Proof.Ecdsa.Rfc6979.Arm
