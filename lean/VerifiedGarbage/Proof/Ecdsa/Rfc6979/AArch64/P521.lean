module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
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
clear, and what `ScrubAll.scrubAllOf` needs of their code
(`ScrubAll.scrubSide`): evaluated here, by the kernel, so that the emitter
works out nothing. -/

/-- The registers the tail of `vg_ecdsa_p521_sign` clears: those its code,
with the HMAC implementations of its table, may write. -/
def p521SignClear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17], [.v0,
   .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
   .v27, .v28, .v29, .v30, .v31], []⟩

theorem p521SignSide (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.AArch64.InvSounds) (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) :
    AArch64.ScrubAll.scrubSide
      (signCodeT (p521 hL hI hT) Spec.Ecdsa.Rfc6979.Curves.p521.tries Proof.Variants.MdHash.AArch64.variants)
      stackT
      (Spec.Ecdsa.Rfc6979.Curves.p521.signSig.retBits
        ((AArch64.abi.withConsts Impl.Ecdsa.AArch64.p521.combConsts).withTables Spec.Ecdsa.Rfc6979.Curves.p521.signSig
          [("hmac", HmacTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants)]).ptrBits)
      p521SignClear [("hmac", HmacTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants)] = true := by rw_lit; kernel_rfl

/-- The registers the tail of `vg_ecdsa_p521_verify` clears: those its code may write. -/
def p521VerifyClear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17], [.v16,
   .v17, .v18, .v19, .v20, .v21, .v22, .v24, .v25, .v26, .v28, .v29], []⟩

theorem p521VerifySide :
    AArch64.ScrubAll.scrubSide
      (Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true Impl.Ecdsa.Verify.AArch64.verifyP521)
      80 (Spec.Ecdsa.P521.inst.verifyHashSig.retBits AArch64.abi.ptrBits) p521VerifyClear [] = true := by lit_decide

end VG.Proof.Ecdsa.Rfc6979.AArch64
