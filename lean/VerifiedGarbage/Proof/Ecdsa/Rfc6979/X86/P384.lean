module

import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.X86.P384.Comb
public import VerifiedGarbage.Spec.Ecdsa.P384
import VerifiedGarbage.Proof.Ecdsa.X86.P384.CombLit
public import VerifiedGarbage.Impl.Ecdsa.P384.X86Comb
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.X86.P384.Comb
meta import VerifiedGarbage.Spec.Ecdsa.P384
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CombCore
meta import VerifiedGarbage.Proof.Ecdsa.X86.P384.CombLit
meta import VerifiedGarbage.Impl.Ecdsa.P384.X86Comb
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CombCore

/-!
# Deterministic ECDSA on x86 (32-bit): P-384

P-384 as the proof's curve (`p384`): scalars of 6 64-bit words, the order
`n` of exactly 384 bits with `2^384 < 2 n`, and `vg_ecdsa_p384_sign_k`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-384's sizes, which is `Proof.Ecdsa.X86.P384.signX86`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem p384_nBits : Spec.Ecdsa.nBits Spec.P384.curve = 384 := by
  show Spec.P384.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.P384.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P384.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

/-- P-384, with the group law `hL`. -/
def p384 (hL : Weierstrass.Law Spec.P384.curve) : RfcCurve where
  E := Impl.Ecdsa.X86.p384Comb
  inst := Spec.Ecdsa.P384.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inr (.inl rfl)), .inl rfl, p384_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 48 - Spec.Ecdsa.nBits Spec.P384.curve = 0; rw [p384_nBits]
  coreN := "vg_ecdsa_p384_sign_k"
  coreC := Impl.Ecdsa.X86.signP384Comb
  coreX := coreX_comb (Proof.Ecdsa.X86.P384.p384Comb_ok) hL (Proof.Ecdsa.X86.P384.p384Comb_tables hL) rfl Proof.Ecdsa.X86.P384.p384Comb_shape
    Proof.Ecdsa.X86.P384.signComb_sp
  coreCT := coreCT_comb (Proof.Ecdsa.X86.P384.p384Comb_ok) hL (Proof.Ecdsa.X86.P384.p384Comb_tables hL) rfl Proof.Ecdsa.X86.P384.p384Comb_shape
    (Proof.Ecdsa.X86.P384.p384Comb_gMul hL) Proof.Ecdsa.X86.P384.signCT Proof.Ecdsa.X86.P384.signComb_sp
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  blk := by rfcT_decide

/-- `vg_ecdsa_p384_sign`, with the tables of `vs`. -/
theorem p384T_verified (hL : Weierstrass.Law Spec.P384.curve) (vs : List Proof.HmacTable.X86.HVar) (h : OK vs ∧ "VG_P384_COMB" ∉ Proof.HmacTable.X86.names vs) :
    Verified X86.target (signCodeT (p384 hL) Spec.Ecdsa.Rfc6979.Curves.p384.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p384 Impl.Ecdsa.X86.p384Comb.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.p384) h.1 (constMem 0x100000 Proof.Ecdsa.X86.P384.p384W) h.2
    (by rw [Proof.Ecdsa.X86.P384.p384W_length]; decide)
    (constMem_held 0x100000 Proof.Ecdsa.X86.P384.p384W (by rw [Proof.Ecdsa.X86.P384.p384W_length]; decide)) (by decide) rfl
  rw [show Impl.Ecdsa.X86.p384Comb.combConsts = [("VG_P384_COMB", Proof.Ecdsa.X86.P384.p384W)] from Proof.Ecdsa.X86.P384.p384Comb_consts]
  exact signT_verified (R := p384 hL) ⟨rfl, by decide, by decide⟩ rfl h.1
    (by rw [show (p384 hL).E.combConsts = [("VG_P384_COMB", Proof.Ecdsa.X86.P384.p384W)] from Proof.Ecdsa.X86.P384.p384Comb_consts]; exact hsat)

end VG.Proof.Ecdsa.Rfc6979.X86
