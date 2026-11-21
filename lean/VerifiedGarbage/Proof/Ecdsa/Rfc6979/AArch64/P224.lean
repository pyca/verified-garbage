module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Scrub
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
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P224.Verified
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl

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
clear, and what `Scrub.verifiedScrubbedAll` needs of their code
(`Scrub.scrubSide`): evaluated here, by the kernel, so that the emitter
works out nothing. -/

/-- No instruction of `vg_ecdsa_p224_sign_k` writes PSTATE.DIT, and it calls
nothing indirectly. -/
theorem p224_core_side :
    AArch64.Scrub.sideAll (fun i => !i.writesDit)
      Impl.Ecdsa.AArch64.signP224 = true := by
  lit_decide

/-- `vg_ecdsa_p224_sign` as emitted, cleanup included
(`Impl.Ecdsa.Rfc6979.AArch64.Fn.p224`), with the tables of every hash
function: it meets its contract in constant time and returns without secret
residue. What the cleanup needs of the code is evaluated here, once, with
nothing in the place of `vg_ecdsa_p224_sign_k`, whose own is evaluated
apart. -/
theorem p224Sign_scrubbed (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.AArch64.InvSounds) (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start) :
    VerifiedScrubbed AArch64.target
      (Impl.Ecdsa.Rfc6979.AArch64.Fn.p224 Proof.Variants.MdHash.AArch64.hashes)
      (specK Spec.Ecdsa.Rfc6979.Curves.p224 Impl.Ecdsa.AArch64.p224.combConsts
        Proof.Variants.MdHash.AArch64.variants)
      32 :=
  Scrub.sign_scrubbed (R := p224 hL hI hT)
    (p224T_verified hL hI hT _ ⟨Scrub.variants_ok, of_decide_eq_true (by kernel_rfl)⟩)
    rfl p224_core_side
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))

/-- `vg_ecdsa_p224_verify` as emitted, cleanup included
(`Impl.Ecdsa.Verify.AArch64.Fn.verifyHashP224`): it meets its contract in
constant time and returns without secret residue. What the cleanup needs of
the code (`Scrub.scrubSide`) is evaluated here, by the kernel. -/
theorem p224Verify (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start) :
    VerifiedScrubbed AArch64.target Impl.Ecdsa.Verify.AArch64.Fn.verifyHashP224
      (Spec.Ecdsa.P224.inst.verifyHashContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p224.combConsts) 80) 32 :=
  AArch64.Scrub.verifiedScrubbedAll (api := Spec.Ecdsa.P224.verifyHashApi)
    { code := Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false
        Impl.Ecdsa.Verify.AArch64.verifyP224
      verified := Proof.Ecdsa.Verify.AArch64.P224.verifyHash_verified hL hI hT } _
    (Proof.EcKey.AArch64.Scrub.verifyHashOk_consts _ _ _) (by dsimp only; lit_decide)

end VG.Proof.Ecdsa.Rfc6979.AArch64
