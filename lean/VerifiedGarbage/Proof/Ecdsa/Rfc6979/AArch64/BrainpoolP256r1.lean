module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP256r1Literals
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP256r1Literals
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Scrub
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Verified
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Config
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Lit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Order.RelClasses
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Lit
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Order.RelClasses
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP256r1
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP256r1.AArch64.Joint
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Verified
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# Deterministic ECDSA on AArch64: brainpoolP256r1

brainpoolp256r1 as the proof's curve (`brainpoolp256r1`): scalars of 32 bytes in 4 words, the
order `n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_brainpoolp256r1_sign`,
proven correct (given the group law, the inversions' soundness) and constant time against its contract (`coreK` at brainpoolP256r1's sizes).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

theorem coreK_brainpoolp256r1 : coreK Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg =
    Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.signAArch64 := by rfl

/-! ## The curve's blocks -/

theorem brainpoolp256r1_blk : RfcT (cfgC Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg false 0) := by rfcT_decide

/-- brainpoolp256r1, with the group law `hL`, the inversions' soundness `hI`. -/
def brainpoolp256r1 (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.AArch64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg
  inst := Spec.Ecdsa.BrainpoolP256r1.inst
  curve := rfl
  big := false
  sizes := ⟨.inl rfl, .inl rfl, Proof.Ecdsa.AArch64.BrainpoolP256r1.brainpoolp256r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.AArch64.BrainpoolP256r1.brainpoolp256r1_sh
  coreN := "vg_ecdsa_brainpoolp256r1_sign_k"
  coreC := Impl.Ecdsa.AArch64.BrainpoolP256r1.signComb
  coreX := by rw [coreK_brainpoolp256r1]; exact Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.sign_a64 hL hI
  coreCT := by rw [coreK_brainpoolp256r1]; exact Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  blk := brainpoolp256r1_blk

/-- `vg_ecdsa_brainpoolp256r1_sign`, with the tables of `vs`. -/
theorem brainpoolp256r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.AArch64.InvSounds) (vs : List Proof.Pbkdf2.Md.AArch64.MdHash)
    (h : OK vs ∧ "VG_BRAINPOOLP256R1_COMB7" ∉ Proof.HmacTable.AArch64.names vs) :
    Verified AArch64.target (signCodeT (brainpoolp256r1 hL hI) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1 Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1) h.1 Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.satMem h.2
    (by rw [Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.combCfg_combWords_length]; decide) Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.satMem_held (by decide) rfl
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl rfl h.1 hsat

/-! ## What the scrubbed functions clear

The registers the tails of `vg_ecdsa_brainpoolp256r1_sign` and `vg_ecdsa_brainpoolp256r1_verify`
clear, and what `ScrubAll.scrubAllOf` needs of their code
(`ScrubAll.scrubSide`): evaluated here, by the kernel, so that the emitter
works out nothing. -/

/-- No instruction of `vg_ecdsa_brainpoolp256r1_sign_k` writes PSTATE.DIT, and it calls
nothing indirectly. -/
theorem brainpoolp256r1_core_side :
    AArch64.ScrubAll.sideAll (fun i => !i.writesDit)
      Impl.Ecdsa.AArch64.BrainpoolP256r1.signComb = true := by
  lit_decide

/-- `vg_ecdsa_brainpoolp256r1_sign` as emitted, cleanup included
(`Impl.Ecdsa.Rfc6979.AArch64.Fn.brainpoolp256r1`), with the tables of every hash
function: it meets its contract in constant time and returns without secret
residue. What the cleanup needs of the code is evaluated here, once, with
nothing in the place of `vg_ecdsa_brainpoolp256r1_sign_k`, whose own is evaluated
apart. -/
theorem brainpoolp256r1Sign_scrubbed (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.AArch64.InvSounds) :
    VerifiedScrubbed AArch64.target
      (Impl.Ecdsa.Rfc6979.AArch64.Fn.brainpoolp256r1 Proof.Variants.MdHash.AArch64.hashes)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1 Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg.combConsts
        Proof.Variants.MdHash.AArch64.variants)
      32 :=
  Scrub.sign_scrubbed (R := brainpoolp256r1 hL hI) (n := 128)
    (brainpoolp256r1T_verified hL hI _ ⟨Scrub.variants_ok, of_decide_eq_true (by kernel_rfl)⟩)
    rfl brainpoolp256r1_core_side
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))

/-- `vg_ecdsa_brainpoolp256r1_verify` as emitted, cleanup included
(`Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Fn.verifyHash`): it meets its contract in
constant time and returns without secret residue. What the cleanup needs of
the code (`ScrubAll.scrubSide`) is evaluated here, by the kernel. -/
theorem brainpoolp256r1Verify (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.AArch64.InvSounds) :
    VerifiedScrubbed AArch64.target Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Fn.verifyHash
      (Spec.Ecdsa.BrainpoolP256r1.inst.verifyHashContract AArch64.abi 80) 32 :=
  AArch64.ScrubAll.verifiedScrubbed (api := Spec.Ecdsa.BrainpoolP256r1.verifyHashApi)
    { code := Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP256r1.inst.curve.len false
        Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.verify
      verified := Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.verifyHash_verified hL hI } _
    (Proof.EcKey.AArch64.Scrub.verifyHashOk _) (by dsimp only; lit_decide)

end VG.Proof.Ecdsa.Rfc6979.AArch64
