module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Scrub
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Lit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Lit
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.AArch64
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import VerifiedGarbage.Impl.Ecdh.P384.AArch64
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Verified
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# Deterministic ECDSA on AArch64: P-384

P-384 as the proof's curve (`p384`): scalars of 6 words, the order `n` of
exactly 384 bits with `2^384 < 2 n`, and `vg_ecdsa_p384_sign`, proven correct
(given the group law and the comb's tables) and constant time against its
contract (`coreK` at P-384's sizes, which is `Proof.Ecdsa.AArch64.P384.signAArch64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

theorem p384_nBits : Spec.Ecdsa.nBits Spec.P384.curve = 384 := by
  show Spec.P384.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.P384.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P384.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

/-! ## The curve's blocks -/

theorem p384_blk : RfcT (cfgC Impl.Ecdsa.AArch64.p384 false 0) := by rfcT_decide

/-- P-384, with the group law `hL`, the inversions' soundness `hI` and the comb's tables `hT`. -/
def p384 (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) : RfcCurve where
  E := Impl.Ecdsa.AArch64.p384
  inst := Spec.Ecdsa.P384.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inr (.inl rfl)), .inl rfl, p384_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 48 - Spec.Ecdsa.nBits Spec.P384.curve = 0; rw [p384_nBits]
  coreN := "vg_ecdsa_p384_sign_k"
  coreC := Impl.Ecdsa.AArch64.signP384
  coreX := Proof.Ecdsa.AArch64.P384.sign_a64 hL hI hT
  coreCT := Proof.Ecdsa.AArch64.P384.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  blk := p384_blk

/-- `vg_ecdsa_p384_sign`, with the tables of `vs`. -/
theorem p384T_verified (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) (vs : List Proof.Pbkdf2.Md.AArch64.MdHash)
    (h : OK vs ∧ "VG_P384_COMB" ∉ Proof.HmacTable.AArch64.names vs) :
    Verified AArch64.target (signCodeT (p384 hL hI hT) Spec.Ecdsa.Rfc6979.Curves.p384.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p384 Impl.Ecdsa.AArch64.p384.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.p384) h.1 Proof.Ecdsa.AArch64.P384.satMem h.2
    (by rw [Proof.Ecdsa.AArch64.P384.p384_combWords_length]; decide) Proof.Ecdsa.AArch64.P384.satMem_held (by decide) rfl
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl rfl h.1 hsat

/-! ## What the scrubbed functions clear

The registers the tails of `vg_ecdsa_p384_sign` and `vg_ecdsa_p384_verify`
clear, and what `Scrub.verifiedScrubbedAll` needs of their code
(`Scrub.scrubSide`): evaluated here, by the kernel, so that the emitter
works out nothing. -/

/-- No instruction of `vg_ecdsa_p384_sign_k` writes PSTATE.DIT, and it calls
nothing indirectly. -/
theorem p384_core_side :
    AArch64.Scrub.sideAll (fun i => !i.writesDit)
      Impl.Ecdsa.AArch64.signP384 = true := by
  lit_decide

/-- `vg_ecdsa_p384_sign` as emitted, cleanup included
(`Impl.Ecdsa.Rfc6979.AArch64.Fn.p384`), with the tables of every hash
function: it meets its contract in constant time and returns without secret
residue. What the cleanup needs of the code is evaluated here, once, with
nothing in the place of `vg_ecdsa_p384_sign_k`, whose own is evaluated
apart. -/
theorem p384Sign_scrubbed (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds) (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) :
    VerifiedScrubbed AArch64.target
      (Impl.Ecdsa.Rfc6979.AArch64.Fn.p384 Proof.Variants.MdHash.AArch64.hashes)
      (specK Spec.Ecdsa.Rfc6979.Curves.p384 Impl.Ecdsa.AArch64.p384.combConsts
        Proof.Variants.MdHash.AArch64.variants)
      32 :=
  Scrub.sign_scrubbed (R := p384 hL hI hT)
    (p384T_verified hL hI hT _ ⟨Scrub.variants_ok, of_decide_eq_true (by kernel_rfl)⟩)
    rfl p384_core_side
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))

/-- `vg_ecdsa_p384_verify` as emitted, cleanup included
(`Impl.Ecdsa.Verify.AArch64.Fn.verifyHashP384`): it meets its contract in
constant time and returns without secret residue. What the cleanup needs of
the code (`Scrub.scrubSide`) is evaluated here, by the kernel. -/
theorem p384Verify (hL : Weierstrass.Law Spec.P384.curve) (hO : Weierstrass.PrimeOrder Spec.P384.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P384.curve 9 1 Impl.P384.p384G9 Impl.P384.p384G9Start) :
    VerifiedScrubbed AArch64.target Impl.Ecdsa.Verify.AArch64.Fn.verifyHashP384
      (Spec.Ecdsa.P384.inst.verifyHashContract (AArch64.abi.withConsts Impl.Ecdsa.Verify.AArch64.P384Joint.p384v.combConsts) 80) 32 :=
  AArch64.Scrub.verifiedScrubbedAll (api := Spec.Ecdsa.P384.verifyHashApi)
    { code := Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false
        Impl.Ecdsa.Verify.AArch64.verifyP384
      verified := Proof.Ecdsa.Verify.AArch64.P384.verifyHash_verified hL hO hI hT } _
    (Proof.EcKey.AArch64.Scrub.verifyHashOk_consts _ _ _) (by dsimp only; lit_decide)

end VG.Proof.Ecdsa.Rfc6979.AArch64
