module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Tables
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Lit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Impl.Ecdsa.Verify.P224.AArch64
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
public import VerifiedGarbage.Impl.Ecdh.P224.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
public import VerifiedGarbage.Proof.P224.AArch64.Law
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.P224.Comb7

/-!
# Deterministic ECDSA on AArch64: P-224

P-224 as the proof's curve (`p224`): scalars of 28 bytes in 4 words, the
order `n` of exactly 224 bits with `2^224 < 2 n`, and `vg_ecdsa_p224_sign`,
proven correct (given the group law, the inversions' soundness and the comb's
tables) and constant time against its contract (`coreK` at P-224's sizes,
which is `Proof.Ecdsa.AArch64.P224.signAArch64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

/-! ## The curve's blocks -/

theorem p224_blk : RfcT (cfgC Impl.Ecdsa.AArch64.p224 false 0) := by rfcT_decide

/-- P-224, with the group law `hL`, the inversions' soundness `hI` and the comb's tables `hT`. -/
def p224 (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start) : RfcCurve where
  E := Impl.Ecdsa.AArch64.p224
  inst := Spec.Ecdsa.P224.inst
  curve := rfl
  big := false
  sizes := ⟨.inl rfl, .inr ⟨rfl, .inl rfl⟩, Proof.Ecdsa.AArch64.P224.p224_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.AArch64.P224.p224_sh
  coreN := "vg_ecdsa_p224_sign_k"
  coreC := Impl.Ecdsa.AArch64.signP224
  coreX := Proof.Ecdsa.AArch64.P224.sign_a64 hL hI hT
  coreCT := Proof.Ecdsa.AArch64.P224.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  blk := p224_blk

/-- `vg_ecdsa_p224_sign`, with the tables of `vs`. -/
theorem p224T_verified (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start) (vs : List Proof.Pbkdf2.Md.AArch64.MdHash)
    (h : OK vs ∧ "VG_P224_COMB" ∉ Proof.HmacTable.AArch64.names vs) :
    Verified AArch64.target (signCodeT (p224 hL hI hT) Spec.Ecdsa.Rfc6979.Curves.p224.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p224 Impl.Ecdsa.AArch64.p224.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.p224) h.1 Proof.Ecdsa.AArch64.P224.satMem h.2
    (by rw [Proof.Ecdsa.AArch64.P224.p224_combWords_length]; decide) Proof.Ecdsa.AArch64.P224.satMem_held (by decide) rfl
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl rfl h.1 hsat

/-! ## What the scrubbed functions clear

The registers the tails of `vg_ecdsa_p224_sign` and `vg_ecdsa_p224_verify`
clear, and what `ScrubAll.scrubAllOf` needs of their code
(`ScrubAll.scrubSide`): evaluated here, by the kernel, so that the emitter
works out nothing. -/

/-- The registers the tail of `vg_ecdsa_p224_sign` clears: those its code,
with the HMAC implementations of its table, may write. -/
def p224SignClear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17], [.v0,
   .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
   .v27, .v28, .v29, .v30, .v31], []⟩

theorem p224SignSide :
    AArch64.ScrubAll.scrubSide
      (signCodeT (p224 Proof.P224.AArch64.hasLaw.law Proof.P224.AArch64.hasLaw.inv (Proof.P224.combOk7 Proof.P224.AArch64.hasLaw.law)) Spec.Ecdsa.Rfc6979.Curves.p224.tries Proof.Variants.MdHash.AArch64.variants)
      stackT
      (Spec.Ecdsa.Rfc6979.Curves.p224.signSig.retBits
        ((AArch64.abi.withConsts Impl.Ecdsa.AArch64.p224.combConsts).withTables Spec.Ecdsa.Rfc6979.Curves.p224.signSig
          [("hmac", HmacTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants)]).ptrBits)
      p224SignClear [("hmac", HmacTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants)] = true := by lit_decide

/-- The registers the tail of `vg_ecdsa_p224_verify` clears: those its code may write. -/
def p224VerifyClear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x16, .x17], [.v28, .v29], []⟩

theorem p224VerifySide :
    AArch64.ScrubAll.scrubSide
      (Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false Impl.Ecdsa.Verify.AArch64.verifyP224)
      80 (Spec.Ecdsa.P224.inst.verifyHashSig.retBits AArch64.abi.ptrBits) p224VerifyClear [] = true := by lit_decide

end VG.Proof.Ecdsa.Rfc6979.AArch64
