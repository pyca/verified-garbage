module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Lit
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Lit
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb

/-!
# Deterministic ECDSA on x86-64: P-224

P-224 as the proof's curve (`p224`): scalars of 28 bytes in 4 words, the
order `n` of exactly 224 bits with `2^224 < 2 n`, and `vg_ecdsa_p224_sign`,
proven correct (given the group law, the comb's tables and the inversions'
soundness) and constant time against its contract (`coreK` at P-224's sizes,
which is `Proof.Ecdsa.X86_64.P224.signX86_64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

/-- `coreK` at P-224's sizes is `Proof.Ecdsa.X86_64.P224.signX86_64` (by rewriting, as
deciding it would evaluate the tables' length). -/
theorem coreK_p224 : coreK Impl.Ecdsa.X86_64.p224 = Proof.Ecdsa.X86_64.P224.signX86_64 := by
  simp only [coreK, TblsOk, Proof.Ecdsa.X86_64.P224.p224_combConsts, Abi.constRegions_cons,
    Abi.constRegions_nil, Sig.forall_mem_const_single]
  simp only [Abi.constsHeld, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true, Proof.Ecdsa.X86_64.P224.signX86_64, Proof.Ecdsa.X86_64.P224.TblHeld]
  rfl

/-! ## The blocks for each hash function's sizes -/

theorem p224_blk₀ : RfcT (cfgS Impl.Ecdsa.X86_64.p224 false 0 16 64) := by rfcT_decide
theorem p224_blk₁ : RfcT (cfgS Impl.Ecdsa.X86_64.p224 false 0 20 64) := by rfcT_decide
theorem p224_blk₂ : RfcT (cfgS Impl.Ecdsa.X86_64.p224 false 0 28 64) := by rfcT_decide
theorem p224_blk₃ : RfcT (cfgS Impl.Ecdsa.X86_64.p224 false 0 32 64) := by rfcT_decide
theorem p224_blk₄ : RfcT (cfgS Impl.Ecdsa.X86_64.p224 false 0 48 128) := by rfcT_decide
theorem p224_blk₅ : RfcT (cfgS Impl.Ecdsa.X86_64.p224 false 0 64 128) := by rfcT_decide
theorem p224_blk₆ : RfcT (cfgS Impl.Ecdsa.X86_64.p224 false 0 28 128) := by rfcT_decide
theorem p224_blk₇ : RfcT (cfgS Impl.Ecdsa.X86_64.p224 false 0 32 128) := by rfcT_decide

/-- P-224, with the group law `hL`, the comb's tables `hT` and the inversions'
soundness `hI`. -/
def p224 (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.p224
  inst := Spec.Ecdsa.P224.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inr ⟨rfl, .inl rfl⟩, Proof.Ecdsa.X86_64.P224.p224_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.P224.p224_sh
  coreN := "vg_ecdsa_p224_sign_k"
  coreC := Impl.Ecdsa.X86_64.signP224
  coreX := by rw [coreK_p224]; exact Proof.Ecdsa.X86_64.P224.sign_call_x86 hL hT hI
  coreCT := by rw [coreK_p224]; exact Proof.Ecdsa.X86_64.P224.sign_ct
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  blkT := blkT_of p224_blk₀ p224_blk₁ p224_blk₂ p224_blk₃ p224_blk₄ p224_blk₅ p224_blk₆ p224_blk₇


/-- `vg_ecdsa_p224_sign`, with the tables of `vs`. -/
theorem p224T_verified (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) (h : OK vs ∧ "VG_P224_COMB" ∉ Proof.HashTable.X86_64.names vs) :
    Verified X86_64.target (signCode (p224 hL hT hI) Spec.Ecdsa.Rfc6979.Curves.p224.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p224 Impl.Ecdsa.X86_64.p224.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.p224) h.1 Proof.Ecdsa.X86_64.P224.satMem h.2
    (by rw [Proof.Ecdsa.X86_64.P224.p224W_length]; decide) Proof.Ecdsa.X86_64.P224.satMem_held (by decide) rfl
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h.1 hsat

end VG.Proof.Ecdsa.Rfc6979.X86_64
