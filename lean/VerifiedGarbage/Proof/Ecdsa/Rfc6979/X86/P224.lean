module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.X86.P224.Contract
public import VerifiedGarbage.Spec.Ecdsa.P224
import VerifiedGarbage.Proof.Ecdsa.X86.P224.Lit
public import VerifiedGarbage.Impl.Ecdsa.P224.X86
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
meta import VerifiedGarbage.Proof.Ecdsa.X86.P224.Contract
meta import VerifiedGarbage.Spec.Ecdsa.P224
meta import VerifiedGarbage.Proof.Ecdsa.X86.P224.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86.P224.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P224.X86
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
public import VerifiedGarbage.Proof.Ecdsa.X86.P224.Verified

/-!
# Deterministic ECDSA on x86 (32-bit): P-224

P-224 as the proof's curve (`p224`): scalars of 28 bytes in 4 64-bit words, the order
`n` of exactly 224 bits with `2^224 < 2 n`, and `vg_ecdsa_p224_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-224's sizes, which is `Proof.Ecdsa.X86.P224.signX86`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem p224_nBits : Spec.Ecdsa.nBits Spec.P224.curve = 224 := by
  show Spec.P224.curve.n.log2 + 1 = 224
  have h₁ : 223 ≤ Spec.P224.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P224.curve.n.log2 < 224 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem core_pre_224 {s : State} (h : (coreK Impl.Ecdsa.X86.p224).pre s) :
    Proof.Ecdsa.X86.P224.signX86.pre s := by
  obtain ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss, _⟩ := h
  exact ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss⟩

/-- P-224, with the group law `hL`. -/
def p224 (hL : Weierstrass.Law Spec.P224.curve) : RfcCurve where
  E := Impl.Ecdsa.X86.p224
  inst := Spec.Ecdsa.P224.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inl rfl), .inr ⟨rfl, rfl⟩, p224_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 28 - Spec.Ecdsa.nBits Spec.P224.curve = 0; rw [p224_nBits]
  coreN := "vg_ecdsa_p224_sign"
  coreC := Impl.Ecdsa.X86.signP224
  coreX := fun s h => Proof.Ecdsa.X86.P224.sign_x86 hL s (core_pre_224 h)
  coreCT := by
    intro s t tr₁ tr₂ s' t' hs ht hp
    obtain ⟨he, a0, a1, a2, a3, a4, _⟩ := hp
    exact Proof.Ecdsa.X86.P224.sign_ct s t tr₁ tr₂ s' t' (core_pre_224 hs) (core_pre_224 ht)
      ⟨he, a0, a1, a2, a3, a4⟩
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)

end VG.Proof.Ecdsa.Rfc6979.X86
