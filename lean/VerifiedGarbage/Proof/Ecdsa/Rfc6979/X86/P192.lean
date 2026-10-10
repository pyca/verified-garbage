import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
import VerifiedGarbage.Proof.Ecdsa.X86.P192.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.P192.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Deterministic ECDSA on x86 (32-bit): P-192

P-192 as the proof's curve (`p192`): scalars of 3 64-bit words, the order
`n` of exactly 192 bits with `2^192 < 2 n`, and `vg_ecdsa_p192_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-192's sizes, which is `Proof.Ecdsa.X86.P192.signX86`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem p192_nBits : Spec.Ecdsa.nBits Spec.P192.curve = 192 := by
  show Spec.P192.curve.n.log2 + 1 = 192
  have h₁ : 191 ≤ Spec.P192.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P192.curve.n.log2 < 192 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

private theorem core_pre_192 {s : State} (h : (coreK Impl.Ecdsa.X86.p192).pre s) :
    Proof.Ecdsa.X86.P192.signX86.pre s := by
  obtain ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss, _⟩ := h
  exact ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss⟩

/-- P-192, with the group law `hL`. -/
def p192 (hL : Weierstrass.Law Spec.P192.curve) : RfcCurve where
  E := Impl.Ecdsa.X86.p192
  inst := Spec.Ecdsa.P192.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, rfl, p192_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 24 - Spec.Ecdsa.nBits Spec.P192.curve = 0; rw [p192_nBits]
  coreN := Spec.Ecdsa.P192.signApi.name
  coreC := Impl.Ecdsa.X86.signP192
  coreX := fun s h => Proof.Ecdsa.X86.P192.sign_x86 hL s (core_pre_192 h)
  coreCT := by
    intro s t tr₁ tr₂ s' t' hs ht hp
    obtain ⟨he, a0, a1, a2, a3, a4, _⟩ := hp
    exact Proof.Ecdsa.X86.P192.sign_ct s t tr₁ tr₂ s' t' (core_pre_192 hs) (core_pre_192 ht)
      ⟨he, a0, a1, a2, a3, a4⟩
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  reduceT := Function.const _ ⟨_, by taint_decide⟩

end VG.Proof.Ecdsa.Rfc6979.X86
