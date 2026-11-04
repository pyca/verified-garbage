module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSpec
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP256r1.Contract
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP256r1.Lit
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.X86
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSpec
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP256r1.Contract
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP256r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP256r1.Lit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.X86
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP256r1.Verified

/-!
# Deterministic ECDSA on x86 (32-bit): brainpoolP256r1

brainpoolP256r1 as the proof's curve (`brainpoolp256r1`): scalars of 4 64-bit words, the order
`n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_brainpoolp256r1_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at brainpoolP256r1's sizes, which is `Proof.Ecdsa.X86.BrainpoolP256r1.signX86`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem brainpoolp256r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP256r1.curve = 256 := by
  show Spec.BrainpoolP256r1.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.BrainpoolP256r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP256r1.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem core_pre_256 {s : State} (h : (coreK Impl.Ecdsa.X86.brainpoolp256r1).pre s) :
    Proof.Ecdsa.X86.BrainpoolP256r1.signX86.pre s := by
  obtain ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss, _⟩ := h
  exact ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss⟩

/-! ## The blocks for each hash function's sizes -/

theorem brainpoolp256r1_blk₀ : RfcT (cfgS Impl.Ecdsa.X86.brainpoolp256r1 false 0 16 64) := by rfcT_decide
theorem brainpoolp256r1_blk₁ : RfcT (cfgS Impl.Ecdsa.X86.brainpoolp256r1 false 0 20 64) := by rfcT_decide
theorem brainpoolp256r1_blk₂ : RfcT (cfgS Impl.Ecdsa.X86.brainpoolp256r1 false 0 28 64) := by rfcT_decide
theorem brainpoolp256r1_blk₃ : RfcT (cfgS Impl.Ecdsa.X86.brainpoolp256r1 false 0 32 64) := by rfcT_decide
theorem brainpoolp256r1_blk₄ : RfcT (cfgS Impl.Ecdsa.X86.brainpoolp256r1 false 0 48 128) := by rfcT_decide
theorem brainpoolp256r1_blk₅ : RfcT (cfgS Impl.Ecdsa.X86.brainpoolp256r1 false 0 64 128) := by rfcT_decide
theorem brainpoolp256r1_blk₆ : RfcT (cfgS Impl.Ecdsa.X86.brainpoolp256r1 false 0 28 128) := by rfcT_decide
theorem brainpoolp256r1_blk₇ : RfcT (cfgS Impl.Ecdsa.X86.brainpoolp256r1 false 0 32 128) := by rfcT_decide

/-- brainpoolP256r1, with the group law `hL`. -/
def brainpoolp256r1 (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Proof.Weierstrass.X86.Inv.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86.brainpoolp256r1
  inst := Spec.Ecdsa.BrainpoolP256r1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, brainpoolp256r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.BrainpoolP256r1.curve = 0; rw [brainpoolp256r1_nBits]
  coreN := "vg_ecdsa_brainpoolp256r1_sign_k"
  coreC := Impl.Ecdsa.X86.signBrainpoolP256r1
  coreX := fun s h => Proof.Ecdsa.X86.BrainpoolP256r1.sign_x86 hL hI s (core_pre_256 h)
  coreCT := by
    intro s t tr₁ tr₂ s' t' hs ht hp
    obtain ⟨he, a0, a1, a2, a3, a4, _⟩ := hp
    exact Proof.Ecdsa.X86.BrainpoolP256r1.sign_ct s t tr₁ tr₂ s' t' (core_pre_256 hs) (core_pre_256 ht)
      ⟨he, a0, a1, a2, a3, a4⟩
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  blkT := blkT_of brainpoolp256r1_blk₀ brainpoolp256r1_blk₁ brainpoolp256r1_blk₂ brainpoolp256r1_blk₃ brainpoolp256r1_blk₄ brainpoolp256r1_blk₅ brainpoolp256r1_blk₆ brainpoolp256r1_blk₇

/-- `vg_ecdsa_brainpoolp256r1_sign`, with the tables of `vs`. -/
theorem brainpoolp256r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Proof.Weierstrass.X86.Inv.InvSounds)
    (vs : List Proof.HashTable.X86.TVar) (h : OK vs) :
    Verified X86.target (signCode (brainpoolp256r1 hL hI) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1 Impl.Ecdsa.X86.brainpoolp256r1.combConsts vs) := by
  have hsat := sat_nil (T := Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1) h (by decide) rfl
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h hsat


end VG.Proof.Ecdsa.Rfc6979.X86
