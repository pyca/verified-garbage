module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT

/-!
# Deterministic ECDSA on x86 (32-bit): `vg_ecdsa_<curve>_sign_k` with a comb

For a curve whose `[k]G` is a fixed-base comb, the signature with a given
`k` (`Cfg.signComb`) meets the contract RFC 6979's code calls it by
(`coreK`): correct (`coreX_comb`, from `signComb_ok`) and constant time
(`coreCT_comb`, from `signComb_ct`), given what a curve's own module checks
of its code: the comb's constant time (`GMulRel`), the taint checks of the
stages around it (`SignStagesCT`) and the stack it uses.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86 VG.Proof.Weierstrass.X86

variable {c : Cfg} {d : CombData}

/-- A curve with a comb has its tables, and no others. -/
theorem combConsts_eq (hcd : c.comb = some d) : c.combConsts = [(d.tsym, c.combWords d)] := by
  simp [Cfg.combConsts, hcd]

theorem coreComb_pre {s : State} (h : (coreK c).pre s) : CombSignPre c s := by
  obtain ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss, ds, gs, ks,
    ht⟩ := h
  exact ⟨⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss⟩, ht, ds, gs, ks⟩

theorem coreComb_pub (hcd : c.comb = some d) {s t : State} (h : (coreK c).pub s t) : CombSignPub d s t := by
  obtain ⟨he, a0, a1, a2, a3, a4, sy⟩ := h
  refine ⟨he, ?_, sy (d.tsym, c.combWords d) (by rw [combConsts_eq hcd]; simp)⟩
  intro j hj
  match j, hj with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4

/-- The stack of the parts of the signature with a comb, from the whole code's. -/
theorem signComb_spMul (hsp : SpOk c.signComb c.stk) : SpOk (c.signWithMul c.gMul) c.stk :=
  SpOk.right (a := c.tableAddr) hsp

/-- `vg_ecdsa_<curve>_sign_k`, with a comb, computes the signature. -/
theorem coreX_comb (hc : CfgOk c) (hL : Weierstrass.Law c.C) (hT : CombTbls c) (hcd : c.comb = some d)
    (hd : CombOk c d) (hsp : SpOk c.signComb c.stk) :
    ∀ s, (coreK c).pre s → ∃ t s', Exec isa c.signComb s t s' ∧ abiPreserved s s' ∧ (coreK c).post s s' := by
  intro s h
  have co : ∀ d', c.comb = some d' → CombOk c d' := by
    intro d' hd'
    have he : d = d' := Option.some.inj (hcd.symm.trans hd')
    rw [← he]; exact hd
  have hm := signComb_spMul hsp
  have hG : SpOk c.gMul c.stk := SpOk.left (SpOk.right (a := c.signPrep) hm)
  have hTl : SpOk c.signTail c.stk := SpOk.right (SpOk.right (a := c.signPrep) hm)
  obtain ⟨tr, t, he, ha, hp⟩ := signComb_ok hc hL hT co hcd hG hTl (coreComb_pre h)
  refine ⟨tr, t, he, ha, ?_⟩
  simp only [coreK, coreSigOf, SignPost, ptr, BitVec.setWidth_append_eq_right] at hp ⊢
  generalize Spec.Ecdsa.signWith c.C
    (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem ((arg s 1).setWidth 64) c.C.len))
    (Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt s.mem ((arg s 2).setWidth 64) c.C.len))
    (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem ((arg s 3).setWidth 64) c.C.len)) = r at hp ⊢
  cases r <;> exact hp

/-- `vg_ecdsa_<curve>_sign_k`, with a comb, is constant time. -/
theorem coreCT_comb (hc : CfgOk c) (hL : Weierstrass.Law c.C) (hT : CombTbls c) (hcd : c.comb = some d)
    (hd : CombOk c d) (hG : GMulRel c d true) (ct : SignStagesCT c) (hsp : SpOk c.signComb c.stk) :
    ConstantTime isa (coreK c).pre (coreK c).pub c.signComb := by
  intro s t tr₁ tr₂ s' t' hs ht hp
  exact signComb_ct hc hL hT hcd hd hG ct (signComb_spMul hsp)
    s t tr₁ tr₂ s' t' (coreComb_pre hs) (coreComb_pre ht) (coreComb_pub hcd hp)

end VG.Proof.Ecdsa.Rfc6979.X86
