module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Lit
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Lit
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# Deterministic ECDSA on x86-64: secp256k1

secp256k1 as the proof's curve (`secp256k1`): scalars of 32 bytes in 4 words, the
order `n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_secp256k1_sign`,
proven correct (given the group law and the inversions'
soundness) and constant time against its contract (`coreK` at secp256k1's sizes,
which is `Proof.Ecdsa.X86_64.Secp256k1.signX86_64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

theorem coreK_secp256k1 : coreK Impl.Ecdsa.X86_64.secp256k1 = Proof.Ecdsa.X86_64.Secp256k1.signX86_64 := by
  simp only [coreK, TblsOk, Impl.Ecdsa.X86_64.Cfg.combConsts, Impl.Ecdsa.X86_64.secp256k1,
    Abi.constRegions, Abi.constsHeld, List.map_nil, List.append_nil, List.not_mem_nil, false_implies,
    implies_true, and_true, Proof.Ecdsa.X86_64.Secp256k1.signX86_64]
  rfl

/-! ## The blocks for each hash function's sizes -/

theorem secp256k1_blk₀ : RfcT (cfgS Impl.Ecdsa.X86_64.secp256k1 false 0 16 64) := by rfcT_decide
theorem secp256k1_blk₁ : RfcT (cfgS Impl.Ecdsa.X86_64.secp256k1 false 0 20 64) := by rfcT_decide
theorem secp256k1_blk₂ : RfcT (cfgS Impl.Ecdsa.X86_64.secp256k1 false 0 28 64) := by rfcT_decide
theorem secp256k1_blk₃ : RfcT (cfgS Impl.Ecdsa.X86_64.secp256k1 false 0 32 64) := by rfcT_decide
theorem secp256k1_blk₄ : RfcT (cfgS Impl.Ecdsa.X86_64.secp256k1 false 0 48 128) := by rfcT_decide
theorem secp256k1_blk₅ : RfcT (cfgS Impl.Ecdsa.X86_64.secp256k1 false 0 64 128) := by rfcT_decide
theorem secp256k1_blk₆ : RfcT (cfgS Impl.Ecdsa.X86_64.secp256k1 false 0 28 128) := by rfcT_decide
theorem secp256k1_blk₇ : RfcT (cfgS Impl.Ecdsa.X86_64.secp256k1 false 0 32 128) := by rfcT_decide

/-- secp256k1, with the group law `hL` and the inversions'
soundness `hI`. -/
def secp256k1 (hL : Weierstrass.Law Spec.Secp256k1.curve)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.secp256k1
  inst := Spec.Ecdsa.Secp256k1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inl rfl, Proof.Ecdsa.X86_64.Secp256k1.secp256k1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.Secp256k1.secp256k1_sh
  coreN := "vg_ecdsa_secp256k1_sign_k"
  coreC := Impl.Ecdsa.X86_64.signSecp256k1
  coreX := by rw [coreK_secp256k1]; exact Proof.Ecdsa.X86_64.Secp256k1.sign_call_x86 hL hI
  coreCT := by rw [coreK_secp256k1]; exact Proof.Ecdsa.X86_64.Secp256k1.sign_ct
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  blkT := blkT_of secp256k1_blk₀ secp256k1_blk₁ secp256k1_blk₂ secp256k1_blk₃ secp256k1_blk₄ secp256k1_blk₅ secp256k1_blk₆ secp256k1_blk₇


/-- `vg_ecdsa_secp256k1_sign`, with the tables of `vs`. -/
theorem secp256k1T_verified (hL : Weierstrass.Law Spec.Secp256k1.curve)
    (hI : Weierstrass.X86_64.InvSounds)
    (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) (h : OK vs) :
    Verified X86_64.target (signCode (secp256k1 hL hI) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.secp256k1 Impl.Ecdsa.X86_64.secp256k1.combConsts vs) := by
  have hsat := sat_nil (T := Spec.Ecdsa.Rfc6979.Curves.secp256k1) h (by decide) rfl
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h hsat

end VG.Proof.Ecdsa.Rfc6979.X86_64
