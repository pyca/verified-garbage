module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Scrub
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

/-! ## The function, as emitted -/

/-- No instruction of `vg_ecdsa_p256_sign_k` writes PSTATE.DIT, and it calls
nothing indirectly. -/
theorem p256_core_side : AArch64.ScrubAll.sideAll (fun i => !i.writesDit) Impl.P256.Booth.sign = true := by
  lit_decide

/-- `vg_ecdsa_p256_sign` as emitted, cleanup included
(`Impl.Ecdsa.Rfc6979.AArch64.Fn.p256`), with the tables of every hash
function: it meets its contract in constant time and returns without secret
residue. What the cleanup needs of the code is evaluated here, once, with
nothing in the place of `vg_ecdsa_p256_sign_k`, whose own is evaluated
apart. -/
theorem p256Sign_scrubbed (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    VerifiedScrubbed AArch64.target (Impl.Ecdsa.Rfc6979.AArch64.Fn.p256 Proof.Variants.MdHash.AArch64.hashes)
      (specK Spec.Ecdsa.Rfc6979.Curves.p256 Impl.Ecdsa.AArch64.p256.combConsts Proof.Variants.MdHash.AArch64.variants)
      32 :=
  Scrub.sign_scrubbed (R := p256 hL hI hT)
    (p256T_verified hL hI hT _ ⟨Scrub.variants_ok, of_decide_eq_true (by kernel_rfl)⟩) rfl p256_core_side
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))

end VG.Proof.Ecdsa.Rfc6979.AArch64
