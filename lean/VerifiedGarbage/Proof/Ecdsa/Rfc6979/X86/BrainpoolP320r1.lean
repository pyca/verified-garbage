module

import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.X86Fn
import VerifiedGarbage.Proof.BrainpoolP320r1.X86.Law
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP320r1.Comb
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP320r1
import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP320r1.CombLit
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.X86Comb
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP320r1.Comb
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP320r1
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CombCore
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP320r1.CombLit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.X86Comb
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CombCore
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Scrub
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Scrub

/-!
# Deterministic ECDSA on x86 (32-bit): brainpoolP320r1

brainpoolP320r1 as the proof's curve (`brainpoolp320r1`): scalars of 5 64-bit words, the order
`n` of exactly 320 bits with `2^320 < 2 n`, and `vg_ecdsa_brainpoolp320r1_sign_k`, proven
correct (given the group law) and constant time against its contract
(`coreK` at brainpoolP320r1's sizes, which is `Proof.Ecdsa.X86.BrainpoolP320r1.signX86`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem brainpoolp320r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP320r1.curve = 320 := by
  show Spec.BrainpoolP320r1.curve.n.log2 + 1 = 320
  have h₁ : 319 ≤ Spec.BrainpoolP320r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP320r1.curve.n.log2 < 320 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

/-- brainpoolP320r1, with the group law `hL`. -/
def brainpoolp320r1 (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) : RfcCurve where
  E := Impl.Ecdsa.X86.brainpoolp320r1Comb
  inst := Spec.Ecdsa.BrainpoolP320r1.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inr (.inl rfl)), .inl rfl, brainpoolp320r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 40 - Spec.Ecdsa.nBits Spec.BrainpoolP320r1.curve = 0; rw [brainpoolp320r1_nBits]
  coreN := "vg_ecdsa_brainpoolp320r1_sign_k"
  coreC := Impl.Ecdsa.X86.signBrainpoolP320r1Comb
  coreX := coreX_comb (Proof.Ecdsa.X86.BrainpoolP320r1.brainpoolp320r1Comb_ok) hL (Proof.Ecdsa.X86.BrainpoolP320r1.brainpoolp320r1Comb_tables hL) rfl Proof.Ecdsa.X86.BrainpoolP320r1.brainpoolp320r1Comb_shape
    Proof.Ecdsa.X86.BrainpoolP320r1.signComb_sp
  coreCT := coreCT_comb (Proof.Ecdsa.X86.BrainpoolP320r1.brainpoolp320r1Comb_ok) hL (Proof.Ecdsa.X86.BrainpoolP320r1.brainpoolp320r1Comb_tables hL) rfl Proof.Ecdsa.X86.BrainpoolP320r1.brainpoolp320r1Comb_shape
    (Proof.Ecdsa.X86.BrainpoolP320r1.brainpoolp320r1Comb_gMul hL) Proof.Ecdsa.X86.BrainpoolP320r1.signCT Proof.Ecdsa.X86.BrainpoolP320r1.signComb_sp
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  blk := by rfcT_decide

/-- `vg_ecdsa_brainpoolp320r1_sign`, with the tables of `vs`. -/
theorem brainpoolp320r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) (vs : List Proof.HmacTable.X86.HVar) (h : OK vs ∧ "VG_BRAINPOOLP320R1_COMB" ∉ Proof.HmacTable.X86.names vs) :
    Verified X86.target (signCodeT (brainpoolp320r1 hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1 Impl.Ecdsa.X86.brainpoolp320r1Comb.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1) h.1 (constMem 0x100000 Proof.Ecdsa.X86.BrainpoolP320r1.brainpoolp320r1W) h.2
    (by rw [Proof.Ecdsa.X86.BrainpoolP320r1.brainpoolp320r1W_length]; decide)
    (constMem_held 0x100000 Proof.Ecdsa.X86.BrainpoolP320r1.brainpoolp320r1W (by rw [Proof.Ecdsa.X86.BrainpoolP320r1.brainpoolp320r1W_length]; decide)) (by decide) rfl
  rw [show Impl.Ecdsa.X86.brainpoolp320r1Comb.combConsts = [("VG_BRAINPOOLP320R1_COMB", Proof.Ecdsa.X86.BrainpoolP320r1.brainpoolp320r1W)] from Proof.Ecdsa.X86.BrainpoolP320r1.brainpoolp320r1Comb_consts]
  exact signT_verified (R := brainpoolp320r1 hL) ⟨rfl, by decide, by decide⟩ rfl h.1
    (by rw [show (brainpoolp320r1 hL).E.combConsts = [("VG_BRAINPOOLP320R1_COMB", Proof.Ecdsa.X86.BrainpoolP320r1.brainpoolp320r1W)] from Proof.Ecdsa.X86.BrainpoolP320r1.brainpoolp320r1Comb_consts]; exact hsat)

/-- What the scrub of `vg_ecdsa_brainpoolp320r1_sign` needs of its code, with the
tables of every HMAC implementation (`X86.Scrub.scrubFSide`): its frames and
calls fit its stack, it calls indirectly only the functions of its table, and
it has no MMX instruction. The code is the same for every proof of the group
law, so it is evaluated at the curve's own. -/
private theorem brainpoolp320r1T_scrubLaw :
    VG.X86.Scrub.scrubFSide
      (signCodeT (brainpoolp320r1 Proof.BrainpoolP320r1.X86.hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries
        (Proof.HmacTable.X86.vars Proof.Variants.Sha1.X86.variants Proof.Variants.Sha256.X86.variants))
      [("hmac", Proof.HmacTable.X86.tables
        (Proof.HmacTable.X86.vars Proof.Variants.Sha1.X86.variants Proof.Variants.Sha256.X86.variants))] stackT = true := by
  lit_decide

theorem brainpoolp320r1T_scrub (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    VG.X86.Scrub.scrubFSide
      (signCodeT (brainpoolp320r1 hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries
        (Proof.HmacTable.X86.vars Proof.Variants.Sha1.X86.variants Proof.Variants.Sha256.X86.variants))
      [("hmac", Proof.HmacTable.X86.tables
        (Proof.HmacTable.X86.vars Proof.Variants.Sha1.X86.variants Proof.Variants.Sha256.X86.variants))] stackT = true :=
  brainpoolp320r1T_scrubLaw

/-- `vg_ecdsa_brainpoolp320r1_sign` as emitted (`Impl.Ecdsa.X86.Fn.signBrainpoolP320r1`), with
the tables of every HMAC implementation, meets its contract in constant time and returns without
secret residue (`X86.Scrub.verifiedScrubbedF`). -/
theorem brainpoolp320r1Sign_scrubbed (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve)
    (hv : OK (Proof.HmacTable.X86.vars Proof.Variants.Sha1.X86.variants Proof.Variants.Sha256.X86.variants) ∧
      "VG_BRAINPOOLP320R1_COMB" ∉ Proof.HmacTable.X86.names
        (Proof.HmacTable.X86.vars Proof.Variants.Sha1.X86.variants Proof.Variants.Sha256.X86.variants)) :
    VerifiedScrubbed X86.target
      (Impl.Ecdsa.X86.Fn.signBrainpoolP320r1 (Proof.HmacTable.X86.fnsOf (Proof.HmacTable.X86.vars Proof.Variants.Sha1.X86.variants Proof.Variants.Sha256.X86.variants)))
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1 Impl.Ecdsa.X86.brainpoolp320r1Comb.combConsts
        (Proof.HmacTable.X86.vars Proof.Variants.Sha1.X86.variants Proof.Variants.Sha256.X86.variants)) 32 :=
  X86.Scrub.verifiedScrubbedF (api := Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1SignApi)
    { tables := [("hmac", Proof.HmacTable.X86.tables
        (Proof.HmacTable.X86.vars Proof.Variants.Sha1.X86.variants Proof.Variants.Sha256.X86.variants))]
      code := signCodeT (brainpoolp320r1 hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries
        (Proof.HmacTable.X86.vars Proof.Variants.Sha1.X86.variants Proof.Variants.Sha256.X86.variants)
      verified := brainpoolp320r1T_verified hL
        (Proof.HmacTable.X86.vars Proof.Variants.Sha1.X86.variants Proof.Variants.Sha256.X86.variants) hv
      spSafe := signCode_sp _ _ _ }
    (Proof.Ecdsa.Rfc6979.X86.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1
      Impl.Ecdsa.X86.brainpoolp320r1Comb.combConsts _)
    (hs := brainpoolp320r1T_scrub hL)

end VG.Proof.Ecdsa.Rfc6979.X86
