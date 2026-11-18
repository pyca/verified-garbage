module

import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.X86.P224.Comb
public import VerifiedGarbage.Spec.Ecdsa.P224
import VerifiedGarbage.Proof.Ecdsa.X86.P224.CombLit
public import VerifiedGarbage.Impl.Ecdsa.P224.X86Comb
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.X86.P224.Comb
meta import VerifiedGarbage.Spec.Ecdsa.P224
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CombCore
meta import VerifiedGarbage.Proof.Ecdsa.X86.P224.CombLit
meta import VerifiedGarbage.Impl.Ecdsa.P224.X86Comb
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CombCore

/-!
# Deterministic ECDSA on x86 (32-bit): P-224

P-224 as the proof's curve (`p224`): scalars of 28 bytes in 4 64-bit words, the order
`n` of exactly 224 bits with `2^224 < 2 n`, and `vg_ecdsa_p224_sign_k`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-224's sizes, which is `Proof.Ecdsa.X86.P224.signX86`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem p224_nBits : Spec.Ecdsa.nBits Spec.P224.curve = 224 := by
  show Spec.P224.curve.n.log2 + 1 = 224
  have h₁ : 223 ≤ Spec.P224.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P224.curve.n.log2 < 224 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

/-- P-224, with the group law `hL`. -/
def p224 (hL : Weierstrass.Law Spec.P224.curve) : RfcCurve where
  E := Impl.Ecdsa.X86.p224Comb
  inst := Spec.Ecdsa.P224.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inl rfl), .inr ⟨rfl, rfl⟩, p224_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 28 - Spec.Ecdsa.nBits Spec.P224.curve = 0; rw [p224_nBits]
  coreN := "vg_ecdsa_p224_sign_k"
  coreC := Impl.Ecdsa.X86.signP224Comb
  coreX := coreX_comb (Proof.Ecdsa.X86.P224.p224Comb_ok) hL (Proof.Ecdsa.X86.P224.p224Comb_tables hL) rfl Proof.Ecdsa.X86.P224.p224Comb_shape
    Proof.Ecdsa.X86.P224.signComb_sp
  coreCT := coreCT_comb (Proof.Ecdsa.X86.P224.p224Comb_ok) hL (Proof.Ecdsa.X86.P224.p224Comb_tables hL) rfl Proof.Ecdsa.X86.P224.p224Comb_shape
    (Proof.Ecdsa.X86.P224.p224Comb_gMul hL) Proof.Ecdsa.X86.P224.signCT Proof.Ecdsa.X86.P224.signComb_sp
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  blk := by rfcT_decide

/-- `vg_ecdsa_p224_sign`, with the tables of `vs`. -/
theorem p224T_verified (hL : Weierstrass.Law Spec.P224.curve) (vs : List Proof.HmacTable.X86.HVar) (h : OK vs ∧ "VG_P224_COMB" ∉ Proof.HmacTable.X86.names vs) :
    Verified X86.target (signCodeT (p224 hL) Spec.Ecdsa.Rfc6979.Curves.p224.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p224 Impl.Ecdsa.X86.p224Comb.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.p224) h.1 (constMem 0x100000 Proof.Ecdsa.X86.P224.p224W) h.2
    (by rw [Proof.Ecdsa.X86.P224.p224W_length]; decide)
    (constMem_held 0x100000 Proof.Ecdsa.X86.P224.p224W (by rw [Proof.Ecdsa.X86.P224.p224W_length]; decide)) (by decide) rfl
  rw [show Impl.Ecdsa.X86.p224Comb.combConsts = [("VG_P224_COMB", Proof.Ecdsa.X86.P224.p224W)] from Proof.Ecdsa.X86.P224.p224Comb_consts]
  exact signT_verified (R := p224 hL) ⟨rfl, by decide, by decide⟩ rfl h.1
    (by rw [show (p224 hL).E.combConsts = [("VG_P224_COMB", Proof.Ecdsa.X86.P224.p224W)] from Proof.Ecdsa.X86.P224.p224Comb_consts]; exact hsat)

end VG.Proof.Ecdsa.Rfc6979.X86
