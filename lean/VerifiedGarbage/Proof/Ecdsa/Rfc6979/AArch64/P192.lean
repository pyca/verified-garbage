module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Scrub
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Lit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Order.RelClasses
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Lit
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Order.RelClasses
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Verify.P192.AArch64.Joint
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Verified
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# Deterministic ECDSA on AArch64: p192

p192 as the proof's curve (`p192`): scalars of 24 bytes in 4 words, the
order `n` of exactly 192 bits with `2^192 < 2 n`, and `vg_ecdsa_p192_sign`,
proven correct (given the group law, the inversions' soundness) and constant time against its contract (`coreK` at p192's sizes,
which is `Proof.Ecdsa.AArch64.P192.signAArch64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

theorem coreK_p192 : coreK Impl.Ecdsa.AArch64.p192 =
    Proof.Ecdsa.AArch64.P192.signAArch64 := by
  have fit : (0 : Addr).toNat + 0 ≤ 2 ^ 64 := by decide
  simp only [fit, coreK, tableRegions, tableAddr, TblOk, Impl.Ecdsa.AArch64.p192,
    Impl.Ecdsa.AArch64.Cfg.combWords, Impl.Weierstrass.tcombWords,
    List.isEmpty_nil, ↓reduceIte, List.flatMap_nil, List.length_nil,
    List.append_nil, Nat.mul_zero, Nat.not_lt_zero, false_implies, implies_true,
    empty_disjoint, and_true, Proof.Ecdsa.AArch64.P192.signAArch64]
  rfl

/-! ## The curve's blocks -/

theorem p192_blk : RfcT (cfgC Impl.Ecdsa.AArch64.p192 false 0) := by rfcT_decide

/-- p192, with the group law `hL`, the inversions' soundness `hI`. -/
def p192 (hL : Weierstrass.Law Spec.P192.curve) (hI : Weierstrass.AArch64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.AArch64.p192
  inst := Spec.Ecdsa.P192.inst
  curve := rfl
  big := false
  sizes := ⟨.inl rfl, .inr ⟨rfl, .inr rfl⟩, Proof.Ecdsa.AArch64.P192.p192_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.AArch64.P192.p192_sh
  coreN := "vg_ecdsa_p192_sign_k"
  coreC := Impl.Ecdsa.AArch64.signP192
  coreX := by rw [coreK_p192]; exact Proof.Ecdsa.AArch64.P192.sign_a64 hL hI
  coreCT := by rw [coreK_p192]; exact Proof.Ecdsa.AArch64.P192.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  blk := p192_blk

/-- `vg_ecdsa_p192_sign`, with the tables of `vs`. -/
theorem p192T_verified (hL : Weierstrass.Law Spec.P192.curve) (hI : Weierstrass.AArch64.InvSounds) (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) (h : OK vs) :
    Verified AArch64.target (signCodeT (p192 hL hI) Spec.Ecdsa.Rfc6979.Curves.p192.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p192 [] vs) := by
  have hsat := sat_nil (T := Spec.Ecdsa.Rfc6979.Curves.p192) h (by decide) rfl
  exact signT_verified_nil ⟨rfl, by decide, by decide⟩ rfl rfl rfl h hsat

/-! ## What the scrubbed functions clear

The registers the tails of `vg_ecdsa_p192_sign` and `vg_ecdsa_p192_verify`
clear, and what `ScrubAll.scrubAllOf` needs of their code
(`ScrubAll.scrubSide`): evaluated here, by the kernel, so that the emitter
works out nothing. -/

/-- No instruction of `vg_ecdsa_p192_sign_k` writes PSTATE.DIT, and it calls
nothing indirectly. -/
theorem p192_core_side :
    AArch64.ScrubAll.sideAll (fun i => !i.writesDit)
      Impl.Ecdsa.AArch64.signP192 = true := by
  lit_decide

/-- `vg_ecdsa_p192_sign` as emitted, cleanup included
(`Impl.Ecdsa.Rfc6979.AArch64.Fn.p192`), with the tables of every hash
function: it meets its contract in constant time and returns without secret
residue. What the cleanup needs of the code is evaluated here, once, with
nothing in the place of `vg_ecdsa_p192_sign_k`, whose own is evaluated
apart. -/
theorem p192Sign_scrubbed (hL : Weierstrass.Law Spec.P192.curve) (hI : Weierstrass.AArch64.InvSounds) :
    VerifiedScrubbed AArch64.target
      (Impl.Ecdsa.Rfc6979.AArch64.Fn.p192 Proof.Variants.MdHash.AArch64.hashes)
      (specK Spec.Ecdsa.Rfc6979.Curves.p192 []
        Proof.Variants.MdHash.AArch64.variants)
      32 :=
  Scrub.sign_scrubbed (R := p192 hL hI)
    (p192T_verified hL hI _ Scrub.variants_ok) rfl p192_core_side
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))

/-- `vg_ecdsa_p192_verify` as emitted, cleanup included
(`Impl.Ecdsa.Verify.AArch64.P192.Joint.Fn.verifyHash`): it meets its contract in
constant time and returns without secret residue. What the cleanup needs of
the code (`ScrubAll.scrubSide`) is evaluated here, by the kernel. -/
theorem p192Verify (hL : Weierstrass.Law Spec.P192.curve) (hI : Weierstrass.AArch64.InvSounds) :
    VerifiedScrubbed AArch64.target Impl.Ecdsa.Verify.AArch64.P192.Joint.Fn.verifyHash
      (Spec.Ecdsa.P192.inst.verifyHashContract AArch64.abi 80) 32 :=
  AArch64.ScrubAll.verifiedScrubbed (api := Spec.Ecdsa.P192.verifyHashApi)
    { code := Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false
        Impl.Ecdsa.Verify.AArch64.P192.Joint.verify
      verified := Proof.Ecdsa.Verify.AArch64.P192.Joint.verifyHash_verified hL hI } _
    (Proof.EcKey.AArch64.Scrub.verifyHashOk _) (by dsimp only; lit_decide)

end VG.Proof.Ecdsa.Rfc6979.AArch64
