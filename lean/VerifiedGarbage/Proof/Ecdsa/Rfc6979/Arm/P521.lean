module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P521Sha512
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P521Sha512
public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Lit
public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Deterministic ECDSA on 32-bit ARM: P-521

P-521 as the proof's curve (`p521`): scalars of 9 64-bit words and 66 bytes,
longer than any hash function's output (`wide`), the order `n` of 521 bits,
so that the signature drops 7 bits of a 66-byte digest, and
`vg_ecdsa_p521_sign`, proven correct (given the group law) and constant time
against its contract (`coreK` at P-521's sizes, which is
`Proof.Ecdsa.Arm.P521.signArm`). Its instance of RFC 6979 is
`Spec.Ecdsa.Rfc6979.P521Sha512.inst` (whose curve and number of candidates
the code uses), whose contract implies `rfcArm` (`p521_implies`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

/-- P-521, with the group law `hL`. -/
def p521 (hL : Weierstrass.Law Spec.P521.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.p521
  inst := Spec.Ecdsa.P521.inst
  curve := rfl
  I := Spec.Ecdsa.Rfc6979.P521Sha512.inst
  ecdsa := rfl
  tries_pos := by decide
  tries_lt := by decide
  wide := true
  sizes := ⟨rfl, rfl, Proof.Ecdsa.Arm.P521.p521_nBits⟩
  n_lt := by decide +kernel
  sh := 7
  sh_eq := Proof.Ecdsa.Arm.P521.p521_sh
  coreN := Spec.Ecdsa.P521.signApi.name
  coreC := Impl.Ecdsa.Arm.signP521
  coreX := Proof.Ecdsa.Arm.P521.sign_arm hL
  coreCT := Proof.Ecdsa.Arm.P521.sign_ct
  coreStack := by lit_decide
  blks := by exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- The contract of `vg_ecdsa_p521_rfc6979_sign` implies `rfcArm`. -/
theorem p521_implies : (rfcArm Spec.Ecdsa.Rfc6979.P521Sha512.inst 456).Implies (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signAnyContract Arm.abi 456) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signAnyContract,
          Spec.Ecdsa.Rfc6979.Instance.signAnySig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm, stkR]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signAnyContract,
          Spec.Ecdsa.Rfc6979.Instance.signAnySig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm, stkR, anyResult]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signAnyContract,
          Spec.Ecdsa.Rfc6979.Instance.signAnySig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm, stkR] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5⟩ := h
        exact ⟨hsp, h0, h1, h2, h3, h4, h5, (List.cons.inj hl).1⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signAnyContract,
          Spec.Ecdsa.Rfc6979.Instance.signAnySig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm, stkR] [satState, satMem] using satState 66 32 3 }

end VG.Proof.Ecdsa.Rfc6979.Arm
