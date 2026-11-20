module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Lit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Order.RelClasses
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Lit
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Order.RelClasses
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.AArch64.Joint
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.Verified
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# Deterministic ECDSA on AArch64: secp256k1

secp256k1 as the proof's curve (`secp256k1`): scalars of 32 bytes in 4 words, the
order `n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_secp256k1_sign`,
proven correct (given the group law, the inversions' soundness) and constant time against its contract (`coreK` at secp256k1's sizes,
which is `Proof.Ecdsa.AArch64.Secp256k1.signAArch64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

theorem coreK_secp256k1 : coreK Impl.Ecdsa.AArch64.secp256k1 =
    Proof.Ecdsa.AArch64.Secp256k1.signAArch64 := by
  have fit : (0 : Addr).toNat + 0 ≤ 2 ^ 64 := by decide
  simp only [fit, coreK, tableRegions, tableAddr, TblOk, Impl.Ecdsa.AArch64.secp256k1,
    Impl.Ecdsa.AArch64.Cfg.combWords, Impl.Weierstrass.tcombWords,
    List.isEmpty_nil, ↓reduceIte, List.flatMap_nil, List.length_nil,
    List.append_nil, Nat.mul_zero, Nat.not_lt_zero, false_implies, implies_true,
    empty_disjoint, and_true, Proof.Ecdsa.AArch64.Secp256k1.signAArch64]
  rfl

/-! ## The curve's blocks -/

theorem secp256k1_blk : RfcT (cfgC Impl.Ecdsa.AArch64.secp256k1 false 0) := by rfcT_decide

/-- secp256k1, with the group law `hL`, the inversions' soundness `hI`. -/
def secp256k1 (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.AArch64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.AArch64.secp256k1
  inst := Spec.Ecdsa.Secp256k1.inst
  curve := rfl
  big := false
  sizes := ⟨.inl rfl, .inl rfl, Proof.Ecdsa.AArch64.Secp256k1.secp256k1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.AArch64.Secp256k1.secp256k1_sh
  coreN := "vg_ecdsa_secp256k1_sign_k"
  coreC := Impl.Ecdsa.AArch64.signSecp256k1
  coreX := by rw [coreK_secp256k1]; exact Proof.Ecdsa.AArch64.Secp256k1.sign_a64 hL hI
  coreCT := by rw [coreK_secp256k1]; exact Proof.Ecdsa.AArch64.Secp256k1.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  blk := secp256k1_blk

/-- `vg_ecdsa_secp256k1_sign`, with the tables of `vs`. -/
theorem secp256k1T_verified (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.AArch64.InvSounds) (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) (h : OK vs) :
    Verified AArch64.target (signCodeT (secp256k1 hL hI) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.secp256k1 [] vs) := by
  have hsat := sat_nil (T := Spec.Ecdsa.Rfc6979.Curves.secp256k1) h (by decide) rfl
  exact signT_verified_nil ⟨rfl, by decide, by decide⟩ rfl rfl rfl h hsat

/-! ## What the scrubbed functions clear

The registers the tails of `vg_ecdsa_secp256k1_sign` and `vg_ecdsa_secp256k1_verify`
clear, and what `ScrubAll.scrubAllOf` needs of their code
(`ScrubAll.scrubSide`): evaluated here, by the kernel, so that the emitter
works out nothing. -/

/-- The registers the tail of `vg_ecdsa_secp256k1_sign` clears: those its code,
with the HMAC implementations of its table, may write. -/
def secp256k1SignClear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17], [.v0,
   .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
   .v27, .v28, .v29, .v30, .v31], []⟩

theorem secp256k1SignSide (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.AArch64.InvSounds) :
    AArch64.ScrubAll.scrubSide
      (signCodeT (secp256k1 hL hI) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries Proof.Variants.MdHash.AArch64.variants)
      stackT
      (Spec.Ecdsa.Rfc6979.Curves.secp256k1.signSig.retBits
        ((AArch64.abi.withConsts []).withTables Spec.Ecdsa.Rfc6979.Curves.secp256k1.signSig
          [("hmac", HmacTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants)]).ptrBits)
      secp256k1SignClear [("hmac", HmacTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants)] = true := by rw_lit; kernel_rfl

/-- `vg_ecdsa_secp256k1_verify` as emitted, cleanup included
(`Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint.Fn.verifyHash`): it meets its contract in
constant time and returns without secret residue. What the cleanup needs of
the code (`ScrubAll.scrubSide`) is evaluated here, by the kernel. -/
theorem secp256k1Verify (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.AArch64.InvSounds) :
    VerifiedScrubbed AArch64.target Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint.Fn.verifyHash
      (Spec.Ecdsa.Secp256k1.inst.verifyHashContract AArch64.abi 80) 32 :=
  AArch64.ScrubAll.verifiedScrubbed (api := Spec.Ecdsa.Secp256k1.verifyHashApi)
    { code := Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false
        Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint.verify
      verified := Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.verifyHash_verified hL hI } _
    (Proof.EcKey.AArch64.Scrub.verifyHashOk _) (by dsimp only; lit_decide)

end VG.Proof.Ecdsa.Rfc6979.AArch64
