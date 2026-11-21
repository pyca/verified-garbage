module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Scrub
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Lit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.AArch64
public import VerifiedGarbage.Impl.AArch64Instrs
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import VerifiedGarbage.Impl.Ecdsa.P521.AArch64
public import VerifiedGarbage.Impl.Ecdh.P256.AArch64
public import VerifiedGarbage.Impl.Ecdh.P521.AArch64
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Forward
public import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointVerified
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# Deterministic ECDSA on AArch64: P-521

P-521 as the proof's curve (`p521`): scalars of 9 words and 66 bytes, longer
than any hash function's output (`wide`), the order `n` of 521 bits, so that
the signature drops 7 bits of a 66-byte digest, and `vg_ecdsa_p521_sign`,
proven correct (given the group law, the inversions' soundness and the comb's
tables) and constant time against its contract (`coreK` at P-521's sizes,
which is `Proof.Ecdsa.AArch64.P521.signAArch64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

/-! ## The curve's blocks -/

theorem p521_blk : RfcT (cfgC Impl.Ecdsa.AArch64.p521 true 7) := by rfcT_decide

/-- P-521, with the group law `hL`, the inversions' soundness `hI` and the comb's tables `hT`. -/
def p521 (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) : RfcCurve where
  E := Impl.Ecdsa.AArch64.p521
  inst := Spec.Ecdsa.P521.inst
  curve := rfl
  big := true
  sizes := ⟨rfl, rfl, Proof.Ecdsa.AArch64.P521.p521_nBits⟩
  n_lt := by decide +kernel
  sh := 7
  sh_eq := Proof.Ecdsa.AArch64.P521.p521_sh
  coreN := "vg_ecdsa_p521_sign_k"
  coreC := Impl.Ecdsa.AArch64.signP521
  coreX := Proof.Ecdsa.AArch64.P521.sign_a64 hL hI hT
  coreCT := Proof.Ecdsa.AArch64.P521.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  blk := p521_blk

/-- `vg_ecdsa_p521_sign`, with the tables of `vs`. -/
theorem p521T_verified (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) (vs : List Proof.Pbkdf2.Md.AArch64.MdHash)
    (h : OK vs ∧ "VG_P521_COMB" ∉ Proof.HmacTable.AArch64.names vs) :
    Verified AArch64.target (signCodeT (p521 hL hI hT) Spec.Ecdsa.Rfc6979.Curves.p521.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p521 Impl.Ecdsa.AArch64.p521.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.p521) h.1 Proof.Ecdsa.AArch64.P521.satMem h.2
    (by rw [Proof.Ecdsa.AArch64.P521.p521_combWords_length]; decide) Proof.Ecdsa.AArch64.P521.satMem_held (by decide) rfl
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl rfl h.1 hsat

/-! ## What the scrubbed functions clear

The registers the tails of `vg_ecdsa_p521_sign` and `vg_ecdsa_p521_verify`
clear, and what `Scrub.scrubAllOf` needs of their code
(`Scrub.scrubSide`): evaluated here, by the kernel, so that the emitter
works out nothing. -/

/-- No instruction of `vg_ecdsa_p521_sign_k` writes PSTATE.DIT, and it calls
nothing indirectly. -/
theorem p521_core_side :
    AArch64.Scrub.sideAll (fun i => !i.writesDit)
      Impl.Ecdsa.AArch64.signP521 = true := by
  lit_decide

/-- `vg_ecdsa_p521_sign` as emitted, cleanup included
(`Impl.Ecdsa.Rfc6979.AArch64.Fn.p521`), with the tables of every hash
function: it meets its contract in constant time and returns without secret
residue. What the cleanup needs of the code is evaluated here, once, with
nothing in the place of `vg_ecdsa_p521_sign_k`, whose own is evaluated
apart. -/
theorem p521Sign_scrubbed (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.AArch64.InvSounds) (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) :
    VerifiedScrubbed AArch64.target
      (Impl.Ecdsa.Rfc6979.AArch64.Fn.p521 Proof.Variants.MdHash.AArch64.hashes)
      (specK Spec.Ecdsa.Rfc6979.Curves.p521 Impl.Ecdsa.AArch64.p521.combConsts
        Proof.Variants.MdHash.AArch64.variants)
      32 :=
  Scrub.sign_scrubbed (R := p521 hL hI hT)
    (p521T_verified hL hI hT _ ⟨Scrub.variants_ok, of_decide_eq_true (by kernel_rfl)⟩)
    rfl p521_core_side
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))

/-- `vg_ecdsa_p521_verify` as emitted, cleanup included
(`Impl.Ecdsa.Verify.AArch64.Fn.verifyHashP521`): it meets its contract in
constant time and returns without secret residue. What the cleanup needs of
the code (`Scrub.scrubSide`) is evaluated here, by the kernel. -/
theorem p521Verify (hL : Weierstrass.Law Spec.P521.curve) (hO : Weierstrass.PrimeOrder Spec.P521.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) :
    VerifiedScrubbed AArch64.target Impl.Ecdsa.Verify.AArch64.Fn.verifyHashP521
      (Spec.Ecdsa.P521.inst.verifyHashContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p521.combConsts) 80) 32 :=
  AArch64.Scrub.verifiedScrubbedAll (api := Spec.Ecdsa.P521.verifyHashApi)
    { code := Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true
        Impl.Ecdsa.Verify.AArch64.verifyP521
      verified := Proof.Ecdsa.Verify.AArch64.P521.verifyHash_verified hL hO hI hT } _
    (Proof.EcKey.AArch64.Scrub.verifyHashOk_consts _ _ _) (by dsimp only; lit_decide)

end VG.Proof.Ecdsa.Rfc6979.AArch64
