module

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P224
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Sha224
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P224Sha224
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P224
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Sha224
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P224Sha224
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.CT
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Args
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Args

/-!
# Deterministic ECDSA over P-224 with HMAC-SHA-224 on PPC64LE

The instance for the generic proof (`pack`, with P-224's group law `hL`,
which the registration file supplies), the taint checks of its blocks
(`blks`), and the shared contract's implying `rfcPPC` (`implies`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE.P224Sha224

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE

/-- The code's configuration. -/
def cfg : Cfg := ⟨sha224K.hm, 28, Spec.P224.curve.n, 8, "vg_ecdsa_p224_sign", Impl.Ecdsa.PPC64LE.signP224⟩

/-- The instance, for P-224's group law `hL`. -/
def pack (hL : Weierstrass.Law Spec.P224.curve) : Rfc where
  K := sha224K
  R := p224Core hL
  c := cfg
  I := Spec.Ecdsa.Rfc6979.P224Sha224.inst
  k := 7
  hE := rfl
  hHash := rfl
  hD := rfl
  hcH := rfl
  hcN := rfl
  hcC := rfl
  hcl := rfl
  hcn := rfl
  hct := rfl
  hk := fun _ => rfl
  hk16 := fun _ => by decide
  hbits := fun _ => p224_nBits
  hn₁ := fun _ => by decide +kernel
  hn₂ := fun _ => by decide +kernel
  hW := fun h => absurd h (by decide)
  hT := by decide
  hT' := by decide

theorem blks : Blks sha224K cfg where
  a₁ := ⟨_, by taint_decide⟩
  a₂V := ⟨_, by taint_decide⟩
  a₂F := ⟨_, by taint_decide⟩
  a₂R := ⟨_, by taint_decide⟩
  a₃V := ⟨_, by taint_decide⟩
  a₃F := ⟨_, by taint_decide⟩
  a₃R := ⟨_, by taint_decide⟩
  m₀ := ⟨_, by taint_decide⟩
  m₁ := ⟨_, by taint_decide⟩
  mR := ⟨_, by taint_decide⟩
  red := by intro; exact ⟨_, by taint_decide⟩
  wide := fun h => absurd h (by decide)
  cnt := ⟨_, by taint_decide⟩

theorem implies :
    (rfcPPC Spec.Ecdsa.Rfc6979.P224Sha224.inst 400).Implies
      (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract PPC64LE.abi 400) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          PPC64LE.abi, PPC64LE.argRegs, rfcPPC, stackBelow]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          PPC64LE.abi, PPC64LE.argRegs, rfcPPC, stackBelow]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          PPC64LE.abi, PPC64LE.argRegs, rfcPPC, stackBelow] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6⟩ := h
        exact ⟨hsp, h3, h4, h5, h6, (List.cons.inj hl).1⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          PPC64LE.abi, PPC64LE.argRegs, rfcPPC, stackBelow] [satState 28 28] using satState 28 28 }

theorem sign_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified PPC64LE.target (pack hL).c.sign (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract PPC64LE.abi 400) :=
  PPC64LE.sign_verified (pack hL) blks rfl implies

end VG.Proof.Ecdsa.Rfc6979.PPC64LE.P224Sha224
