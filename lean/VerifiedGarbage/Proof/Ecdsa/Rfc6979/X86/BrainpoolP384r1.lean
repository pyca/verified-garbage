module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP384r1.Contract
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP384r1.Lit
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP384r1.Contract
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP384r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP384r1.Lit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP384r1.Verified

/-!
# Deterministic ECDSA on x86 (32-bit): brainpoolP384r1

brainpoolP384r1 as the proof's curve (`brainpoolp384r1`): scalars of 6 64-bit words, the order
`n` of exactly 384 bits with `2^384 < 2 n`, and `vg_ecdsa_brainpoolp384r1_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at brainpoolP384r1's sizes, which is `Proof.Ecdsa.X86.BrainpoolP384r1.signX86`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem brainpoolp384r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP384r1.curve = 384 := by
  show Spec.BrainpoolP384r1.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.BrainpoolP384r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP384r1.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem core_pre_brainpoolp384r1 {s : State} (h : (coreK Impl.Ecdsa.X86.brainpoolp384r1).pre s) :
    Proof.Ecdsa.X86.BrainpoolP384r1.signX86.pre s := by
  obtain ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss, _⟩ := h
  exact ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss⟩

/-- brainpoolP384r1, with the group law `hL`. -/
def brainpoolp384r1 (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) : RfcCurve where
  E := Impl.Ecdsa.X86.brainpoolp384r1
  inst := Spec.Ecdsa.BrainpoolP384r1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inr (.inl rfl)), .inl rfl, brainpoolp384r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 48 - Spec.Ecdsa.nBits Spec.BrainpoolP384r1.curve = 0; rw [brainpoolp384r1_nBits]
  coreN := "vg_ecdsa_brainpoolp384r1_sign"
  coreC := Impl.Ecdsa.X86.signBrainpoolP384r1
  coreX := fun s h => Proof.Ecdsa.X86.BrainpoolP384r1.sign_x86 hL s (core_pre_brainpoolp384r1 h)
  coreCT := by
    intro s t tr₁ tr₂ s' t' hs ht hp
    obtain ⟨he, a0, a1, a2, a3, a4, _⟩ := hp
    exact Proof.Ecdsa.X86.BrainpoolP384r1.sign_ct s t tr₁ tr₂ s' t' (core_pre_brainpoolp384r1 hs) (core_pre_brainpoolp384r1 ht)
      ⟨he, a0, a1, a2, a3, a4⟩
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)

end VG.Proof.Ecdsa.Rfc6979.X86
