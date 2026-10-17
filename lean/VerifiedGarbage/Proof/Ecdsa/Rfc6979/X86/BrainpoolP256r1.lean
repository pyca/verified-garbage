module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP256r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP256r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP256r1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP256r1.Lit
public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.X25519.X86.Column
meta import VerifiedGarbage.Proof.X25519.X86.Column
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find

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
  coreN := Spec.Ecdsa.BrainpoolP256r1.signApi.name
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

end VG.Proof.Ecdsa.Rfc6979.X86
