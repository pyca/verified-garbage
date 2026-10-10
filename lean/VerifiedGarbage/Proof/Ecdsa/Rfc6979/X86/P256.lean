import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
import VerifiedGarbage.Proof.Ecdsa.X86.CombVerified
import VerifiedGarbage.Proof.Ecdsa.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Deterministic ECDSA on x86 (32-bit): P-256

P-256 as the proof's curve (`p256`): scalars of 4 64-bit words, the order
`n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_p256_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-256's sizes). Its seven-bit comb reads the same immutable
table as public-key generation and verification, using four bytes of stack
for position-independent addressing, within the 20 its calls use.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem p256_nBits : Spec.Ecdsa.nBits Spec.P256.curve = 256 := by
  show Spec.P256.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.P256.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P256.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

open VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86

private theorem core_pre_256 {s : State} (h : (coreK p256Comb).pre s) : CombSignPre p256Comb s := by
  obtain ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss, ds, gs, ks,
    ht⟩ := h
  exact ⟨⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss⟩, ht, ds, gs, ks⟩

private theorem core_pub_256 {s t : State} (h : (coreK p256Comb).pub s t) : CombSignPub s t := by
  obtain ⟨he, a0, a1, a2, a3, a4, sy⟩ := h
  refine ⟨he, ?_, sy ("VG_P256_COMB", p256W) (by rw [p256Comb_consts]; simp)⟩
  intro j hj
  match j, hj with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4

/-- P-256, with the group law `hL`. -/
def p256 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) : RfcCurve where
  E := p256Comb
  inst := Spec.Ecdsa.P256.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inl rfl), rfl, p256_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.P256.curve = 0; rw [p256_nBits]
  coreN := Spec.Ecdsa.P256.signApi.name
  coreC := signP256Comb
  coreX := by
    intro s h
    have co : ∀ d, p256Comb.comb = some d → CombOk p256Comb d := by
      intro d hd
      have he : p256d = d := Option.some.inj hd
      rw [← he]; exact p256Comb_shape
    obtain ⟨tr, t, he, ha, hp⟩ := signComb_ok (p256Comb_ok hI) hL (p256Comb_tables hL) co p256Comb_am3 rfl signComb_spG
      signComb_spTail (core_pre_256 h)
    refine ⟨tr, t, he, ha, ?_⟩
    simp only [coreK, coreSigOf, SignPost, ptr, BitVec.setWidth_append_eq_right] at hp ⊢
    generalize Spec.Ecdsa.signWith p256Comb.C
      (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem ((arg s 1).setWidth 64) p256Comb.C.len))
      (Spec.Ecdsa.hashToInt p256Comb.C (Spec.Ecdsa.bytesAt s.mem ((arg s 2).setWidth 64) p256Comb.C.len))
      (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem ((arg s 3).setWidth 64) p256Comb.C.len)) = r at hp ⊢
    cases r <;> exact hp
  coreCT := by
    intro s t tr₁ tr₂ s' t' hs ht hp
    exact signComb_ct (p256Comb_ok hI) hL (p256Comb_tables hL) p256Comb_shape p256Comb_am3 signComb_spMul
      s t tr₁ tr₂ s' t' (core_pre_256 hs) (core_pre_256 ht) (core_pub_256 hp)
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  reduceT := Function.const _ ⟨_, by taint_decide⟩

end VG.Proof.Ecdsa.Rfc6979.X86
