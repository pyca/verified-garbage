module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.Lit
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.Lit
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# Deterministic ECDSA on x86-64: p192

p192 as the proof's curve (`p192`): scalars of 24 bytes in 4 words, the
order `n` of exactly 192 bits with `2^192 < 2 n`, and `vg_ecdsa_p192_sign`,
proven correct (given the group law and the inversions'
soundness) and constant time against its contract (`coreK` at p192's sizes,
which is `Proof.Ecdsa.X86_64.P192.signX86_64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

theorem coreK_p192 : coreK Impl.Ecdsa.X86_64.p192 = Proof.Ecdsa.X86_64.P192.signX86_64 := by
  simp only [coreK, TblsOk, Impl.Ecdsa.X86_64.Cfg.combConsts, Impl.Ecdsa.X86_64.p192,
    Abi.constRegions, Abi.constsHeld, List.map_nil, List.append_nil, List.not_mem_nil, false_implies,
    implies_true, and_true, Proof.Ecdsa.X86_64.P192.signX86_64]
  rfl

/-! ## The blocks for each hash function's sizes -/

theorem p192_blk₀ : RfcT (cfgS Impl.Ecdsa.X86_64.p192 false 0 16 64) := by rfcT_decide
theorem p192_blk₁ : RfcT (cfgS Impl.Ecdsa.X86_64.p192 false 0 20 64) := by rfcT_decide
theorem p192_blk₂ : RfcT (cfgS Impl.Ecdsa.X86_64.p192 false 0 28 64) := by rfcT_decide
theorem p192_blk₃ : RfcT (cfgS Impl.Ecdsa.X86_64.p192 false 0 32 64) := by rfcT_decide
theorem p192_blk₄ : RfcT (cfgS Impl.Ecdsa.X86_64.p192 false 0 48 128) := by rfcT_decide
theorem p192_blk₅ : RfcT (cfgS Impl.Ecdsa.X86_64.p192 false 0 64 128) := by rfcT_decide
theorem p192_blk₆ : RfcT (cfgS Impl.Ecdsa.X86_64.p192 false 0 28 128) := by rfcT_decide
theorem p192_blk₇ : RfcT (cfgS Impl.Ecdsa.X86_64.p192 false 0 32 128) := by rfcT_decide

/-- p192, with the group law `hL` and the inversions'
soundness `hI`. -/
def p192 (hL : Weierstrass.Law Spec.P192.curve)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.p192
  inst := Spec.Ecdsa.P192.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inr ⟨rfl, .inr rfl⟩, Proof.Ecdsa.X86_64.P192.p192_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.P192.p192_sh
  coreN := "vg_ecdsa_p192_sign"
  coreC := Impl.Ecdsa.X86_64.signP192
  coreX := by rw [coreK_p192]; exact Proof.Ecdsa.X86_64.P192.sign_call_x86 hL hI
  coreCT := by rw [coreK_p192]; exact Proof.Ecdsa.X86_64.P192.sign_ct
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  blkT := blkT_of p192_blk₀ p192_blk₁ p192_blk₂ p192_blk₃ p192_blk₄ p192_blk₅ p192_blk₆ p192_blk₇


/-- `vg_ecdsa_p192_sign`, with the tables of `vs`. -/
theorem p192T_verified (hL : Weierstrass.Law Spec.P192.curve)
    (hI : Weierstrass.X86_64.InvSounds)
    (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) (h : OK vs) :
    Verified X86_64.target (signCode (p192 hL hI) Spec.Ecdsa.Rfc6979.Curves.p192.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p192 Impl.Ecdsa.X86_64.p192.combConsts vs) := by
  have hsat := sat_nil (T := Spec.Ecdsa.Rfc6979.Curves.p192) h (by decide) rfl
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h hsat

end VG.Proof.Ecdsa.Rfc6979.X86_64
