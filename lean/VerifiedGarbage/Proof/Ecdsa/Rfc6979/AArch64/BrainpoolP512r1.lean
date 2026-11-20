module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP512r1Literals
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP512r1Literals
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb.Verified
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Config
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb.Lit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Order.RelClasses
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb.Lit
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Order.RelClasses
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.AArch64.Joint
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP512r1
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Verified
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# Deterministic ECDSA on AArch64: brainpoolP512r1

brainpoolp512r1 as the proof's curve (`brainpoolp512r1`): scalars of 64 bytes in 8 words, the
order `n` of exactly 512 bits with `2^512 < 2 n`, and `vg_ecdsa_brainpoolp512r1_sign`,
proven correct (given the group law, the inversions' soundness) and constant time against its contract (`coreK` at brainpoolP512r1's sizes).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

theorem coreK_brainpoolp512r1 : coreK Impl.Ecdsa.AArch64.BrainpoolP512r1.combCfg =
    Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb.signAArch64 := by rfl

/-! ## The curve's blocks -/

theorem brainpoolp512r1_blk : RfcT (cfgC Impl.Ecdsa.AArch64.BrainpoolP512r1.combCfg false 0) := by rfcT_decide

/-- brainpoolp512r1, with the group law `hL`, the inversions' soundness `hI`. -/
def brainpoolp512r1 (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.AArch64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.AArch64.BrainpoolP512r1.combCfg
  inst := Spec.Ecdsa.BrainpoolP512r1.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inr (.inr rfl)), .inl rfl, Proof.Ecdsa.AArch64.BrainpoolP512r1.brainpoolp512r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by
    unfold Impl.Ecdsa.AArch64.Cfg.sh
    rw [show Impl.Ecdsa.AArch64.BrainpoolP512r1.combCfg.C =
      Impl.Ecdsa.AArch64.brainpoolp512r1.C from rfl]
    exact Proof.Ecdsa.AArch64.BrainpoolP512r1.brainpoolp512r1_sh
  coreN := "vg_ecdsa_brainpoolp512r1_sign_k"
  coreC := Impl.Ecdsa.AArch64.BrainpoolP512r1.signComb
  coreX := by rw [coreK_brainpoolp512r1]; exact Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb.sign_a64 hL hI
  coreCT := by rw [coreK_brainpoolp512r1]; exact Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  blk := brainpoolp512r1_blk

/-- `vg_ecdsa_brainpoolp512r1_sign`, with the tables of `vs`. -/
theorem brainpoolp512r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.AArch64.InvSounds) (vs : List Proof.Pbkdf2.Md.AArch64.MdHash)
    (h : OK vs ∧ "VG_BRAINPOOLP512R1_COMB7" ∉ Proof.HmacTable.AArch64.names vs) :
    Verified AArch64.target (signCodeT (brainpoolp512r1 hL hI) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 Impl.Ecdsa.AArch64.BrainpoolP512r1.combCfg.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1) h.1 Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb.satMem h.2
    (by rw [Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb.combCfg_combWords_length]; decide) Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb.satMem_held (by decide) rfl
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl rfl h.1 hsat

/-! ## What the scrubbed functions clear

The registers the tails of `vg_ecdsa_brainpoolp512r1_sign` and `vg_ecdsa_brainpoolp512r1_verify`
clear, and what `ScrubAll.scrubAllOf` needs of their code
(`ScrubAll.scrubSide`): evaluated here, by the kernel, so that the emitter
works out nothing. -/

/-- The registers the tail of `vg_ecdsa_brainpoolp512r1_sign` clears: those its code,
with the HMAC implementations of its table, may write. -/
def brainpoolp512r1SignClear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17], [.v0,
   .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
   .v27, .v28, .v29, .v30, .v31], []⟩

theorem brainpoolp512r1SignSide (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.AArch64.InvSounds) :
    AArch64.ScrubAll.scrubSide
      (signCodeT (brainpoolp512r1 hL hI) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries Proof.Variants.MdHash.AArch64.variants)
      stackT
      (Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.signSig.retBits
        ((AArch64.abi.withConsts Impl.Ecdsa.AArch64.BrainpoolP512r1.combCfg.combConsts).withTables Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.signSig
          [("hmac", HmacTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants)]).ptrBits)
      brainpoolp512r1SignClear [("hmac", HmacTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants)] = true := by rw_lit; kernel_rfl

/-- `vg_ecdsa_brainpoolp512r1_verify` as emitted, cleanup included
(`Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Fn.verifyHash`): it meets its contract in
constant time and returns without secret residue. What the cleanup needs of
the code (`ScrubAll.scrubSide`) is evaluated here, by the kernel. -/
theorem brainpoolp512r1Verify (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.AArch64.InvSounds) :
    VerifiedScrubbed AArch64.target Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Fn.verifyHash
      (Spec.Ecdsa.BrainpoolP512r1.inst.verifyHashContract AArch64.abi 80) 32 :=
  AArch64.ScrubAll.verifiedScrubbed (api := Spec.Ecdsa.BrainpoolP512r1.verifyHashApi)
    { code := Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false
        Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.verify
      verified := Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.verifyHash_verified hL hI } _
    (Proof.EcKey.AArch64.Scrub.verifyHashOk _) (by dsimp only; lit_decide)

end VG.Proof.Ecdsa.Rfc6979.AArch64
