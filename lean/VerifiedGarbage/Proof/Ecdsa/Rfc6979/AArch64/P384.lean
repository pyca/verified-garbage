module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
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
clear, and what `ScrubAll.scrubAllOf` needs of their code
(`ScrubAll.scrubSide`): evaluated here, by the kernel, so that the emitter
works out nothing. -/

/-- The registers the tail of `vg_ecdsa_p384_sign` clears: those its code,
with the HMAC implementations of its table, may write. -/
def p384SignClear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17], [.v0,
   .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
   .v27, .v28, .v29, .v30, .v31], []⟩

theorem p384SignSide (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds) (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) :
    AArch64.ScrubAll.scrubSide
      (signCodeT (p384 hL hI hT) Spec.Ecdsa.Rfc6979.Curves.p384.tries Proof.Variants.MdHash.AArch64.variants)
      stackT
      (Spec.Ecdsa.Rfc6979.Curves.p384.signSig.retBits
        ((AArch64.abi.withConsts Impl.Ecdsa.AArch64.p384.combConsts).withTables Spec.Ecdsa.Rfc6979.Curves.p384.signSig
          [("hmac", HmacTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants)]).ptrBits)
      p384SignClear [("hmac", HmacTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants)] = true := by rw_lit; kernel_rfl

/-- The registers the tail of `vg_ecdsa_p384_verify` clears: those its code may write. -/
def p384VerifyClear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17], [.v16,
   .v17, .v18, .v19, .v28, .v29], []⟩

theorem p384VerifySide :
    AArch64.ScrubAll.scrubSide
      (Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false Impl.Ecdsa.Verify.AArch64.verifyP384)
      80 (Spec.Ecdsa.P384.inst.verifyHashSig.retBits AArch64.abi.ptrBits) p384VerifyClear [] = true := by lit_decide

end VG.Proof.Ecdsa.Rfc6979.AArch64
