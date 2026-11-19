module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.AArch64.Tables
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.CombW
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
meta import VerifiedGarbage.Proof.Weierstrass.CombW
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothVerified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothContract
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothContract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothVerified
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
public import VerifiedGarbage.Impl.Ecdh.P256.AArch64
public import VerifiedGarbage.Impl.P256.EcdhJac
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# Deterministic ECDSA on AArch64: P-256

P-256 as the proof's curve (`p256`): scalars of 4 words, the order `n` of
exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_p256_sign`, proven correct
(given the group law and the comb's tables) and constant time against its
contract (`coreK` at P-256's sizes, which is `Proof.Ecdsa.AArch64.signAArch64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

theorem p256_nBits : Spec.Ecdsa.nBits Spec.P256.curve = 256 := by
  show Spec.P256.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.P256.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P256.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

/-! ## The curve's blocks -/

theorem p256_blk : RfcT (cfgC Impl.Ecdsa.AArch64.p256 false 0) := by rfcT_decide

/-- P-256, with the group law `hL`, the inversions' soundness `hI` and the comb's tables `hT`. -/
def p256 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) : RfcCurve where
  E := Impl.Ecdsa.AArch64.p256
  inst := Spec.Ecdsa.P256.inst
  curve := rfl
  big := false
  sizes := ⟨.inl rfl, .inl rfl, p256_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.P256.curve = 0; rw [p256_nBits]
  coreN := "vg_ecdsa_p256_sign_k"
  coreC := Impl.P256.Booth.sign
  coreX := Proof.Ecdsa.AArch64.booth_sign_a64 hL hI (Proof.Ecdsa.AArch64.booth_comb_correct hL hI hT)
  coreCT := Proof.Ecdsa.AArch64.booth_sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  blk := p256_blk

/-- `vg_ecdsa_p256_sign`, with the tables of `vs`. -/
theorem p256T_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) (vs : List Proof.Pbkdf2.Md.AArch64.MdHash)
    (h : OK vs ∧ "VG_P256_COMB" ∉ Proof.HmacTable.AArch64.names vs) :
    Verified AArch64.target (signCodeT (p256 hL hI hT) Spec.Ecdsa.Rfc6979.Curves.p256.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p256 Impl.Ecdsa.AArch64.p256.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.p256) h.1 Proof.Ecdsa.AArch64.satMem h.2
    (by rw [Proof.Ecdsa.AArch64.p256_combWords_length]; decide) Proof.Ecdsa.AArch64.satMem_held (by decide) rfl
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl rfl h.1 hsat

/-! ## What the scrubbed functions clear

The registers the tails of `vg_ecdsa_p256_sign` and `vg_ecdsa_p256_verify`
clear, and what `ScrubAll.scrubAllOf` needs of their code
(`ScrubAll.scrubSide`): evaluated here, by the kernel, so that the emitter
works out nothing. -/

/-- The registers the tail of `vg_ecdsa_p256_sign` clears: those its code,
with the HMAC implementations of its table, may write. -/
def p256SignClear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17], [.v0,
   .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
   .v27, .v28, .v29, .v30, .v31], []⟩

theorem p256SignSide (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds) (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    AArch64.ScrubAll.scrubSide
      (signCodeT (p256 hL hI hT) Spec.Ecdsa.Rfc6979.Curves.p256.tries Proof.Variants.MdHash.AArch64.variants)
      stackT
      (Spec.Ecdsa.Rfc6979.Curves.p256.signSig.retBits
        ((AArch64.abi.withConsts Impl.Ecdsa.AArch64.p256.combConsts).withTables Spec.Ecdsa.Rfc6979.Curves.p256.signSig
          [("hmac", HmacTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants)]).ptrBits)
      p256SignClear [("hmac", HmacTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants)] = true := by rw_lit; kernel_rfl

/-- The registers the tail of `vg_ecdsa_p256_verify` clears: those its code may write. -/
def p256VerifyClear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17], [.v28],
   []⟩

theorem p256VerifySide :
    AArch64.ScrubAll.scrubSide
      (Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false Impl.Ecdsa.Verify.AArch64.P256Allocated.verify)
      80 (Spec.Ecdsa.P256.inst.verifyHashSig.retBits AArch64.abi.ptrBits) p256VerifyClear [] = true := by lit_decide

end VG.Proof.Ecdsa.Rfc6979.AArch64
