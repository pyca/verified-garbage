module

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P521
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Sha384
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P521Sha512
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P521
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Sha384
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P521Sha512
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.CT

/-!
# Deterministic ECDSA over P-521 with HMAC-SHA-512 on PPC64LE

The instance for the generic proof (`pack`, with P-521's group law `hL`,
which the registration file supplies), the taint checks of its blocks
(`blks`), and the shared contract's implying `rfcPPC` (`implies`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE.P521Sha512

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE

/-- The code's configuration. -/
def cfg : Cfg := ⟨sha512K.hm, 66, Spec.P521.curve.n, 8, "vg_ecdsa_p521_sign", Impl.Ecdsa.PPC64LE.signP521⟩

/-- The instance, for P-521's group law `hL`. -/
def pack (hL : Weierstrass.Law Spec.P521.curve) : Rfc where
  K := sha512K
  R := p521Core hL
  c := cfg
  I := Spec.Ecdsa.Rfc6979.P521Sha512.inst
  k := 0
  hE := rfl
  hHash := rfl
  hD := rfl
  hcH := rfl
  hcN := rfl
  hcC := rfl
  hcl := rfl
  hcn := rfl
  hct := rfl
  hk h := absurd h (by decide)
  hk16 h := absurd h (by decide)
  hbits h := absurd h (by decide)
  hn₁ h := absurd h (by decide)
  hn₂ h := absurd h (by decide)
  hW _ := ⟨rfl, rfl, p521_nBits⟩
  hT := by decide
  hT' := by decide

theorem blks : Blks sha512K cfg where
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
  red h := absurd h (by decide)
  wide := by
    intro
    exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩⟩
  cnt := ⟨_, by taint_decide⟩

theorem implies :
    (rfcPPC Spec.Ecdsa.Rfc6979.P521Sha512.inst 544).Implies
      (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract PPC64LE.abi 544) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          PPC64LE.abi, PPC64LE.argRegs, rfcPPC, stackBelow]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          PPC64LE.abi, PPC64LE.argRegs, rfcPPC, stackBelow]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          PPC64LE.abi, PPC64LE.argRegs, rfcPPC, stackBelow] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6⟩ := h
        exact ⟨hsp, h3, h4, h5, h6, (List.cons.inj hl).1⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          PPC64LE.abi, PPC64LE.argRegs, rfcPPC, stackBelow] [satState 66 64] using satState 66 64 }

theorem sign_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified PPC64LE.target (pack hL).c.sign (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract PPC64LE.abi 544) :=
  PPC64LE.sign_verified (pack hL) blks rfl implies

end VG.Proof.Ecdsa.Rfc6979.PPC64LE.P521Sha512
