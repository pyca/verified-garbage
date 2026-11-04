module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSpec
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
public import VerifiedGarbage.Proof.Ecdsa.X86.P192.Contract
public import VerifiedGarbage.Spec.Ecdsa.P192
import VerifiedGarbage.Proof.Ecdsa.X86.P192.Lit
public import VerifiedGarbage.Impl.Ecdsa.P192.X86
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSpec
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.X86.P192.Contract
meta import VerifiedGarbage.Spec.Ecdsa.P192
meta import VerifiedGarbage.Proof.Ecdsa.X86.P192.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86.P192.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P192.X86
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
public import VerifiedGarbage.Proof.Ecdsa.X86.P192.Verified

/-!
# Deterministic ECDSA on x86 (32-bit): P-192

P-192 as the proof's curve (`p192`): scalars of 3 64-bit words, the order
`n` of exactly 192 bits with `2^192 < 2 n`, and `vg_ecdsa_p192_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-192's sizes, which is `Proof.Ecdsa.X86.P192.signX86`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem p192_nBits : Spec.Ecdsa.nBits Spec.P192.curve = 192 := by
  show Spec.P192.curve.n.log2 + 1 = 192
  have h₁ : 191 ≤ Spec.P192.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P192.curve.n.log2 < 192 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem core_pre_192 {s : State} (h : (coreK Impl.Ecdsa.X86.p192).pre s) :
    Proof.Ecdsa.X86.P192.signX86.pre s := by
  obtain ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss, _⟩ := h
  exact ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss⟩

/-! ## The blocks for each hash function's sizes -/

theorem p192_blk₀ : RfcT (cfgS Impl.Ecdsa.X86.p192 false 0 16 64) := by rfcT_decide
theorem p192_blk₁ : RfcT (cfgS Impl.Ecdsa.X86.p192 false 0 20 64) := by rfcT_decide
theorem p192_blk₂ : RfcT (cfgS Impl.Ecdsa.X86.p192 false 0 28 64) := by rfcT_decide
theorem p192_blk₃ : RfcT (cfgS Impl.Ecdsa.X86.p192 false 0 32 64) := by rfcT_decide
theorem p192_blk₄ : RfcT (cfgS Impl.Ecdsa.X86.p192 false 0 48 128) := by rfcT_decide
theorem p192_blk₅ : RfcT (cfgS Impl.Ecdsa.X86.p192 false 0 64 128) := by rfcT_decide
theorem p192_blk₆ : RfcT (cfgS Impl.Ecdsa.X86.p192 false 0 28 128) := by rfcT_decide
theorem p192_blk₇ : RfcT (cfgS Impl.Ecdsa.X86.p192 false 0 32 128) := by rfcT_decide

/-- P-192, with the group law `hL`. -/
def p192 (hL : Weierstrass.Law Spec.P192.curve) : RfcCurve where
  E := Impl.Ecdsa.X86.p192
  inst := Spec.Ecdsa.P192.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inl rfl, p192_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 24 - Spec.Ecdsa.nBits Spec.P192.curve = 0; rw [p192_nBits]
  coreN := "vg_ecdsa_p192_sign_k"
  coreC := Impl.Ecdsa.X86.signP192
  coreX := fun s h => Proof.Ecdsa.X86.P192.sign_x86 hL s (core_pre_192 h)
  coreCT := by
    intro s t tr₁ tr₂ s' t' hs ht hp
    obtain ⟨he, a0, a1, a2, a3, a4, _⟩ := hp
    exact Proof.Ecdsa.X86.P192.sign_ct s t tr₁ tr₂ s' t' (core_pre_192 hs) (core_pre_192 ht)
      ⟨he, a0, a1, a2, a3, a4⟩
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  blkT := blkT_of p192_blk₀ p192_blk₁ p192_blk₂ p192_blk₃ p192_blk₄ p192_blk₅ p192_blk₆ p192_blk₇

/-- `vg_ecdsa_p192_sign`, with the tables of `vs`. -/
theorem p192T_verified (hL : Weierstrass.Law Spec.P192.curve)
    (vs : List Proof.HashTable.X86.TVar) (h : OK vs) :
    Verified X86.target (signCode (p192 hL) Spec.Ecdsa.Rfc6979.Curves.p192.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p192 Impl.Ecdsa.X86.p192.combConsts vs) := by
  have hsat := sat_nil (T := Spec.Ecdsa.Rfc6979.Curves.p192) h (by decide) rfl
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h hsat


end VG.Proof.Ecdsa.Rfc6979.X86
