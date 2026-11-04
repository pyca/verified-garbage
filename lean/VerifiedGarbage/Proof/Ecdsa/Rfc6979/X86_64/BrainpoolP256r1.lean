module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.Lit
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.Lit
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# Deterministic ECDSA on x86-64: brainpoolP256r1

brainpoolp256r1 as the proof's curve (`brainpoolp256r1`): scalars of 32 bytes in 4 words, the
order `n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_brainpoolp256r1_sign`,
proven correct (given the group law and the inversions'
soundness) and constant time against its contract (`coreK` at brainpoolP256r1's sizes,
which is `Proof.Ecdsa.X86_64.BrainpoolP256r1.signX86_64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

theorem coreK_brainpoolp256r1 : coreK Impl.Ecdsa.X86_64.brainpoolp256r1 = Proof.Ecdsa.X86_64.BrainpoolP256r1.signX86_64 := by
  simp only [coreK, TblsOk, Impl.Ecdsa.X86_64.Cfg.combConsts, Impl.Ecdsa.X86_64.brainpoolp256r1,
    Abi.constRegions, Abi.constsHeld, List.map_nil, List.append_nil, List.not_mem_nil, false_implies,
    implies_true, and_true, Proof.Ecdsa.X86_64.BrainpoolP256r1.signX86_64]
  rfl

/-! ## The blocks for each hash function's sizes -/

theorem brainpoolp256r1_blk₀ : RfcT (cfgS Impl.Ecdsa.X86_64.brainpoolp256r1 false 0 16 64) := by rfcT_decide
theorem brainpoolp256r1_blk₁ : RfcT (cfgS Impl.Ecdsa.X86_64.brainpoolp256r1 false 0 20 64) := by rfcT_decide
theorem brainpoolp256r1_blk₂ : RfcT (cfgS Impl.Ecdsa.X86_64.brainpoolp256r1 false 0 28 64) := by rfcT_decide
theorem brainpoolp256r1_blk₃ : RfcT (cfgS Impl.Ecdsa.X86_64.brainpoolp256r1 false 0 32 64) := by rfcT_decide
theorem brainpoolp256r1_blk₄ : RfcT (cfgS Impl.Ecdsa.X86_64.brainpoolp256r1 false 0 48 128) := by rfcT_decide
theorem brainpoolp256r1_blk₅ : RfcT (cfgS Impl.Ecdsa.X86_64.brainpoolp256r1 false 0 64 128) := by rfcT_decide
theorem brainpoolp256r1_blk₆ : RfcT (cfgS Impl.Ecdsa.X86_64.brainpoolp256r1 false 0 28 128) := by rfcT_decide
theorem brainpoolp256r1_blk₇ : RfcT (cfgS Impl.Ecdsa.X86_64.brainpoolp256r1 false 0 32 128) := by rfcT_decide

/-- brainpoolp256r1, with the group law `hL` and the inversions'
soundness `hI`. -/
def brainpoolp256r1 (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.brainpoolp256r1
  inst := Spec.Ecdsa.BrainpoolP256r1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inl rfl, Proof.Ecdsa.X86_64.BrainpoolP256r1.brainpoolp256r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.BrainpoolP256r1.brainpoolp256r1_sh
  coreN := "vg_ecdsa_brainpoolp256r1_sign"
  coreC := Impl.Ecdsa.X86_64.signBrainpoolP256r1
  coreX := by rw [coreK_brainpoolp256r1]; exact Proof.Ecdsa.X86_64.BrainpoolP256r1.sign_call_x86 hL hI
  coreCT := by rw [coreK_brainpoolp256r1]; exact Proof.Ecdsa.X86_64.BrainpoolP256r1.sign_ct
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  blkT := blkT_of brainpoolp256r1_blk₀ brainpoolp256r1_blk₁ brainpoolp256r1_blk₂ brainpoolp256r1_blk₃ brainpoolp256r1_blk₄ brainpoolp256r1_blk₅ brainpoolp256r1_blk₆ brainpoolp256r1_blk₇


/-- `vg_ecdsa_brainpoolp256r1_sign`, with the tables of `vs`. -/
theorem brainpoolp256r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve)
    (hI : Weierstrass.X86_64.InvSounds)
    (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) (h : OK vs) :
    Verified X86_64.target (signCode (brainpoolp256r1 hL hI) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1 Impl.Ecdsa.X86_64.brainpoolp256r1.combConsts vs) := by
  have hsat := sat_nil (T := Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1) h (by decide) rfl
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h hsat

end VG.Proof.Ecdsa.Rfc6979.X86_64
