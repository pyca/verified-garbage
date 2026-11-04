module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSpec
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Config
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Contract
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSpec
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Config
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Contract
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Verified

/-!
# Deterministic ECDSA on x86 (32-bit): brainpoolP512r1

brainpoolP512r1 as the proof's curve (`brainpoolp512r1`): scalars of 8 64-bit words, the order
`n` of exactly 512 bits with `2^512 < 2 n`, `h` kept at the frame's top (`hHigh`), and `vg_ecdsa_brainpoolp512r1_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at brainpoolP512r1's sizes, which is `Proof.Ecdsa.X86.BrainpoolP512r1.signX86`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem brainpoolp512r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP512r1.curve = 512 := by
  show Spec.BrainpoolP512r1.curve.n.log2 + 1 = 512
  have h₁ : 511 ≤ Spec.BrainpoolP512r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP512r1.curve.n.log2 < 512 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem core_pre_brainpoolp512r1 {s : State} (h : (coreK Impl.Ecdsa.X86.brainpoolp512r1).pre s) :
    Proof.Ecdsa.X86.BrainpoolP512r1.signX86.pre s := by
  obtain ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss, _⟩ := h
  exact ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss⟩

/-! ## The blocks for each hash function's sizes -/

theorem brainpoolp512r1_blk₀ : RfcT (cfgS Impl.Ecdsa.X86.brainpoolp512r1 true 0 16 64) := by rfcT_decide
theorem brainpoolp512r1_blk₁ : RfcT (cfgS Impl.Ecdsa.X86.brainpoolp512r1 true 0 20 64) := by rfcT_decide
theorem brainpoolp512r1_blk₂ : RfcT (cfgS Impl.Ecdsa.X86.brainpoolp512r1 true 0 28 64) := by rfcT_decide
theorem brainpoolp512r1_blk₃ : RfcT (cfgS Impl.Ecdsa.X86.brainpoolp512r1 true 0 32 64) := by rfcT_decide
theorem brainpoolp512r1_blk₄ : RfcT (cfgS Impl.Ecdsa.X86.brainpoolp512r1 true 0 48 128) := by rfcT_decide
theorem brainpoolp512r1_blk₅ : RfcT (cfgS Impl.Ecdsa.X86.brainpoolp512r1 true 0 64 128) := by rfcT_decide
theorem brainpoolp512r1_blk₆ : RfcT (cfgS Impl.Ecdsa.X86.brainpoolp512r1 true 0 28 128) := by rfcT_decide
theorem brainpoolp512r1_blk₇ : RfcT (cfgS Impl.Ecdsa.X86.brainpoolp512r1 true 0 32 128) := by rfcT_decide

/-- brainpoolP512r1, with the group law `hL`. -/
def brainpoolp512r1 (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : RfcCurve where
  E := Impl.Ecdsa.X86.brainpoolp512r1
  inst := Spec.Ecdsa.BrainpoolP512r1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inr (.inr rfl)), .inl rfl, brainpoolp512r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  hHigh := true
  sh := 0
  sh_eq := Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1_sh
  coreN := "vg_ecdsa_brainpoolp512r1_sign_k"
  coreC := Impl.Ecdsa.X86.signBrainpoolP512r1
  coreX := fun s h => Proof.Ecdsa.X86.BrainpoolP512r1.sign_x86 hL s (core_pre_brainpoolp512r1 h)
  coreCT := by
    intro s t tr₁ tr₂ s' t' hs ht hp
    obtain ⟨he, a0, a1, a2, a3, a4, _⟩ := hp
    exact Proof.Ecdsa.X86.BrainpoolP512r1.sign_ct s t tr₁ tr₂ s' t' (core_pre_brainpoolp512r1 hs) (core_pre_brainpoolp512r1 ht)
      ⟨he, a0, a1, a2, a3, a4⟩
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  blkT := blkT_of brainpoolp512r1_blk₀ brainpoolp512r1_blk₁ brainpoolp512r1_blk₂ brainpoolp512r1_blk₃ brainpoolp512r1_blk₄ brainpoolp512r1_blk₅ brainpoolp512r1_blk₆ brainpoolp512r1_blk₇

/-- `vg_ecdsa_brainpoolp512r1_sign`, with the tables of `vs`. -/
theorem brainpoolp512r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve)
    (vs : List Proof.HashTable.X86.TVar) (h : OK vs) :
    Verified X86.target (signCode (brainpoolp512r1 hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 Impl.Ecdsa.X86.brainpoolp512r1.combConsts vs) := by
  have hsat := sat_nil (T := Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1) h (by decide) rfl
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h hsat


end VG.Proof.Ecdsa.Rfc6979.X86
