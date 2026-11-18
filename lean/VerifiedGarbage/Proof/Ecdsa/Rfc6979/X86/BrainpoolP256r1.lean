module

import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP256r1.Comb
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP256r1.CombLit
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.X86Comb
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP256r1.Comb
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CombCore
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP256r1.CombLit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.X86Comb
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CombCore

/-!
# Deterministic ECDSA on x86 (32-bit): brainpoolP256r1

brainpoolP256r1 as the proof's curve (`brainpoolp256r1`): scalars of 4 64-bit words, the order
`n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_brainpoolp256r1_sign_k`, proven
correct (given the group law) and constant time against its contract
(`coreK` at brainpoolP256r1's sizes, which is `Proof.Ecdsa.X86.BrainpoolP256r1.signX86`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem brainpoolp256r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP256r1.curve = 256 := by
  show Spec.BrainpoolP256r1.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.BrainpoolP256r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP256r1.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

/-- brainpoolP256r1, with the group law `hL`. -/
def brainpoolp256r1 (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Proof.Weierstrass.X86.Inv.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86.brainpoolp256r1Comb
  inst := Spec.Ecdsa.BrainpoolP256r1.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, brainpoolp256r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.BrainpoolP256r1.curve = 0; rw [brainpoolp256r1_nBits]
  coreN := "vg_ecdsa_brainpoolp256r1_sign_k"
  coreC := Impl.Ecdsa.X86.signBrainpoolP256r1Comb
  coreX := coreX_comb (Proof.Ecdsa.X86.BrainpoolP256r1.brainpoolp256r1Comb_ok hI) hL (Proof.Ecdsa.X86.BrainpoolP256r1.brainpoolp256r1Comb_tables hL) rfl Proof.Ecdsa.X86.BrainpoolP256r1.brainpoolp256r1Comb_shape
    Proof.Ecdsa.X86.BrainpoolP256r1.signComb_sp
  coreCT := coreCT_comb (Proof.Ecdsa.X86.BrainpoolP256r1.brainpoolp256r1Comb_ok hI) hL (Proof.Ecdsa.X86.BrainpoolP256r1.brainpoolp256r1Comb_tables hL) rfl Proof.Ecdsa.X86.BrainpoolP256r1.brainpoolp256r1Comb_shape
    (Proof.Ecdsa.X86.BrainpoolP256r1.brainpoolp256r1Comb_gMul hL hI) Proof.Ecdsa.X86.BrainpoolP256r1.signCT Proof.Ecdsa.X86.BrainpoolP256r1.signComb_sp
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  blk := by rfcT_decide

/-- `vg_ecdsa_brainpoolp256r1_sign`, with the tables of `vs`. -/
theorem brainpoolp256r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Proof.Weierstrass.X86.Inv.InvSounds) (vs : List Proof.HmacTable.X86.HVar) (h : OK vs ∧ "VG_BRAINPOOLP256R1_COMB" ∉ Proof.HmacTable.X86.names vs) :
    Verified X86.target (signCodeT (brainpoolp256r1 hL hI) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1 Impl.Ecdsa.X86.brainpoolp256r1Comb.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1) h.1 (constMem 0x100000 Proof.Ecdsa.X86.BrainpoolP256r1.brainpoolp256r1W) h.2
    (by rw [Proof.Ecdsa.X86.BrainpoolP256r1.brainpoolp256r1W_length]; decide)
    (constMem_held 0x100000 Proof.Ecdsa.X86.BrainpoolP256r1.brainpoolp256r1W (by rw [Proof.Ecdsa.X86.BrainpoolP256r1.brainpoolp256r1W_length]; decide)) (by decide) rfl
  rw [show Impl.Ecdsa.X86.brainpoolp256r1Comb.combConsts = [("VG_BRAINPOOLP256R1_COMB", Proof.Ecdsa.X86.BrainpoolP256r1.brainpoolp256r1W)] from Proof.Ecdsa.X86.BrainpoolP256r1.brainpoolp256r1Comb_consts]
  exact signT_verified (R := brainpoolp256r1 hL hI) ⟨rfl, by decide, by decide⟩ rfl h.1
    (by rw [show (brainpoolp256r1 hL hI).E.combConsts = [("VG_BRAINPOOLP256R1_COMB", Proof.Ecdsa.X86.BrainpoolP256r1.brainpoolp256r1W)] from Proof.Ecdsa.X86.BrainpoolP256r1.brainpoolp256r1Comb_consts]; exact hsat)

end VG.Proof.Ecdsa.Rfc6979.X86
