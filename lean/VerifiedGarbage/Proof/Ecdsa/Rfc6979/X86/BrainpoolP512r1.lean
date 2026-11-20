module

meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86Comb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86Comb
import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Config
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Comb
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.CombLit
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Config
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Comb
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CombCore
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.CombLit
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CombCore

/-!
# Deterministic ECDSA on x86 (32-bit): brainpoolP512r1

brainpoolP512r1 as the proof's curve (`brainpoolp512r1`): scalars of 8 64-bit words, the order
`n` of exactly 512 bits with `2^512 < 2 n`, and `vg_ecdsa_brainpoolp512r1_sign_k`, proven
correct (given the group law) and constant time against its contract
(`coreK` at brainpoolP512r1's sizes, which is `Proof.Ecdsa.X86.BrainpoolP512r1.signX86`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem brainpoolp512r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP512r1.curve = 512 := by
  show Spec.BrainpoolP512r1.curve.n.log2 + 1 = 512
  have h₁ : 511 ≤ Spec.BrainpoolP512r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP512r1.curve.n.log2 < 512 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

/-- brainpoolP512r1, with the group law `hL`. -/
def brainpoolp512r1 (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : RfcCurve where
  E := Impl.Ecdsa.X86.brainpoolp512r1Comb
  inst := Spec.Ecdsa.BrainpoolP512r1.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inr (.inr (.inr rfl))), .inl rfl, brainpoolp512r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := (Proof.Ecdsa.X86.Cfg.sh_withComb Impl.Ecdsa.X86.brainpoolp512r1 Impl.Ecdsa.X86.brainpoolp512r1d).trans
    Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1_sh
  coreN := "vg_ecdsa_brainpoolp512r1_sign_k"
  coreC := Impl.Ecdsa.X86.signBrainpoolP512r1Comb
  coreX := coreX_comb (Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1Comb_ok) hL (Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1Comb_tables hL) rfl Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1Comb_shape
    Proof.Ecdsa.X86.BrainpoolP512r1.signComb_sp
  coreCT := coreCT_comb (Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1Comb_ok) hL (Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1Comb_tables hL) rfl Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1Comb_shape
    (Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1Comb_gMul hL) Proof.Ecdsa.X86.BrainpoolP512r1.signCT Proof.Ecdsa.X86.BrainpoolP512r1.signComb_sp
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  blk := by rfcT_decide

/-- `vg_ecdsa_brainpoolp512r1_sign`, with the tables of `vs`. -/
theorem brainpoolp512r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (vs : List Proof.HmacTable.X86.HVar) (h : OK vs ∧ "VG_BRAINPOOLP512R1_COMB" ∉ Proof.HmacTable.X86.names vs) :
    Verified X86.target (signCodeT (brainpoolp512r1 hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 Impl.Ecdsa.X86.brainpoolp512r1Comb.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1) h.1 (constMem 0x100000 Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1W) h.2
    (by rw [Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1W_length]; decide)
    (constMem_held 0x100000 Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1W (by rw [Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1W_length]; decide)) (by decide) rfl
  rw [show Impl.Ecdsa.X86.brainpoolp512r1Comb.combConsts = [("VG_BRAINPOOLP512R1_COMB", Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1W)] from Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1Comb_consts]
  exact signT_verified (R := brainpoolp512r1 hL) ⟨rfl, by decide, by decide⟩ rfl h.1
    (by rw [show (brainpoolp512r1 hL).E.combConsts = [("VG_BRAINPOOLP512R1_COMB", Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1W)] from Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1Comb_consts]; exact hsat)

end VG.Proof.Ecdsa.Rfc6979.X86
