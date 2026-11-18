module

import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Comb
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.CombLit
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86Comb
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Comb
meta import VerifiedGarbage.Spec.Ecdsa.Secp256k1
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CombCore
meta import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.CombLit
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86Comb
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CombCore

/-!
# Deterministic ECDSA on x86 (32-bit): secp256k1

secp256k1 as the proof's curve (`secp256k1`): scalars of 4 64-bit words, the order
`n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_secp256k1_sign_k`, proven
correct (given the group law) and constant time against its contract
(`coreK` at secp256k1's sizes, which is `Proof.Ecdsa.X86.Secp256k1.signX86`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem secp256k1_nBits : Spec.Ecdsa.nBits Spec.Secp256k1.curve = 256 := by
  show Spec.Secp256k1.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.Secp256k1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Secp256k1.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

/-- secp256k1, with the group law `hL`. -/
def secp256k1 (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Proof.Weierstrass.X86.Inv.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86.secp256k1Comb
  inst := Spec.Ecdsa.Secp256k1.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, secp256k1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.Secp256k1.curve = 0; rw [secp256k1_nBits]
  coreN := "vg_ecdsa_secp256k1_sign_k"
  coreC := Impl.Ecdsa.X86.signSecp256k1Comb
  coreX := coreX_comb (Proof.Ecdsa.X86.Secp256k1.secp256k1Comb_ok hI) hL (Proof.Ecdsa.X86.Secp256k1.secp256k1Comb_tables hL) rfl Proof.Ecdsa.X86.Secp256k1.secp256k1Comb_shape
    Proof.Ecdsa.X86.Secp256k1.signComb_sp
  coreCT := coreCT_comb (Proof.Ecdsa.X86.Secp256k1.secp256k1Comb_ok hI) hL (Proof.Ecdsa.X86.Secp256k1.secp256k1Comb_tables hL) rfl Proof.Ecdsa.X86.Secp256k1.secp256k1Comb_shape
    (Proof.Ecdsa.X86.Secp256k1.secp256k1Comb_gMul hL hI) Proof.Ecdsa.X86.Secp256k1.signCT Proof.Ecdsa.X86.Secp256k1.signComb_sp
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  blk := by rfcT_decide

/-- `vg_ecdsa_secp256k1_sign`, with the tables of `vs`. -/
theorem secp256k1T_verified (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Proof.Weierstrass.X86.Inv.InvSounds) (vs : List Proof.HmacTable.X86.HVar) (h : OK vs ∧ "VG_SECP256K1_COMB" ∉ Proof.HmacTable.X86.names vs) :
    Verified X86.target (signCodeT (secp256k1 hL hI) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.secp256k1 Impl.Ecdsa.X86.secp256k1Comb.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.secp256k1) h.1 (constMem 0x100000 Proof.Ecdsa.X86.Secp256k1.secp256k1W) h.2
    (by rw [Proof.Ecdsa.X86.Secp256k1.secp256k1W_length]; decide)
    (constMem_held 0x100000 Proof.Ecdsa.X86.Secp256k1.secp256k1W (by rw [Proof.Ecdsa.X86.Secp256k1.secp256k1W_length]; decide)) (by decide) rfl
  rw [show Impl.Ecdsa.X86.secp256k1Comb.combConsts = [("VG_SECP256K1_COMB", Proof.Ecdsa.X86.Secp256k1.secp256k1W)] from Proof.Ecdsa.X86.Secp256k1.secp256k1Comb_consts]
  exact signT_verified (R := secp256k1 hL hI) ⟨rfl, by decide, by decide⟩ rfl h.1
    (by rw [show (secp256k1 hL hI).E.combConsts = [("VG_SECP256K1_COMB", Proof.Ecdsa.X86.Secp256k1.secp256k1W)] from Proof.Ecdsa.X86.Secp256k1.secp256k1Comb_consts]; exact hsat)

end VG.Proof.Ecdsa.Rfc6979.X86
