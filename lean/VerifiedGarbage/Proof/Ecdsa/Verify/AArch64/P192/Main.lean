import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Points

/-! # p192 signature verification -/

namespace VG.Proof.Ecdsa.Verify.AArch64.P192

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V)

theorem verifyWithPoints_ok {c : Cfg} (hc : BaseCfgOk c) (hC : Law c.C)
    (pointCode : Prog isa)
    (hpoints : ∀ {s₀ : State} {base : Addr} {g : Reg → BitVec 64} {s : State},
      Mid c s₀ base g s → ∀ {Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop},
      (∀ X Y Z, Rep c.C X Y Z (mul (sv c base s U) (G c.C)) → Q₁ 0 X Y Z) →
      ∀ {P : Point c.C}, onCurve c.C P = true →
      Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
        (tmv c.C c.n base s (c.sl ONEP)) P →
      (∀ X Y Z, Rep c.C X Y Z (mul (sv c base s V) P) → Q₂ 0 X Y Z) →
      ∀ {rest : Prog isa} {Q : State → Prop},
      (∀ s', Pts c s₀ base g Q₁ Q₂ s' → WP isa rest s' Q) →
      WP isa (.seq pointCode rest) s Q)
    {s₀ : State} (hp : FrontPre c s₀) :
    WP isa (Impl.Ecdsa.Verify.AArch64.P192.verifyWithPoints c pointCode) s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ VPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  unfold Impl.Ecdsa.Verify.AArch64.P192.verifyWithPoints
  refine front_ok hc hp fun g s₁ hg hF => mid_ok hc hF fun s₂ hM => ?_
  have F₂ := hM.fixed
  have h1 := onep_tmv hc F₂
  -- The validated peer point.
  let P := peerPt c (s₀.mem (s₀.gpr .x0) = 4) (keyX c s₀) (keyY c s₀)
  have hPc : onCurve c.C P = true := peerPt_onCurve hc _ _ _
  have hQ : Rep c.C (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl PX)) (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl PY))
      (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl ONEP)) P := by
    rw [h1]
    exact peerPt_rep hC _ _ _ hM.px hM.py
  refine hpoints hM
    (Q₁ := fun j X Y Z => Rep c.C X Y Z (mul (sv c (s₀.gpr .x3) s₂ U >>> j) (G c.C)))
    (Q₂ := fun j X Y Z => Rep c.C X Y Z (mul (sv c (s₀.gpr .x3) s₂ V >>> j) P))
    (fun X Y Z h => by simp only [Nat.shiftRight_zero]; exact h) hPc hQ
    (fun X Y Z h => by simp only [Nat.shiftRight_zero]; exact h) fun s₃ hP => ?_
  refine WP.mono (tail_dispatch_ok hc hC hP.toFinalState) fun s' ⟨saved, xo, hxo, hx, ret⟩ =>
    ⟨fun r hr => (saved r hr).trans (hg r hr), ?_⟩
  obtain ⟨X1, Y1, Z1, X2, Y2, Z2, q1, q2, hsum⟩ := hP.pt
  have q1' : Rep c.C X1 Y1 Z1 (mul (sv c (s₀.gpr .x3) s₂ U) (G c.C)) := by
    have := q1; simp only [Nat.shiftRight_zero] at this; exact this
  have q2' : Rep c.C X2 Y2 Z2 (mul (sv c (s₀.gpr .x3) s₂ V) P) := by
    have := q2; simp only [Nat.shiftRight_zero] at this; exact this
  have hR := Rep.add hC (hC.onCurve_mul hc.onG _) (hC.onCurve_mul hPc _) q1' q2' hsum.symm
  -- The arguments as the specification reads them.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .x0)) := by
    rw [peer_bytes]; rfl
  have hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s₀ := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  have hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s₀ := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (s₀.gpr .x0)) (keyX c s₀) (keyY c s₀),
      P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    show peerPt c _ _ _ = _
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have h16 : 2 * c.C.len = c.C.len + c.C.len := by omega
  have hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (2 * c.C.len)).take c.C.len) = sigR c s₀ := by
    rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
  have hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (2 * c.C.len)).drop c.C.len) = sigS c s₀ := by
    rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
  have hspec := Proof.Ecdsa.verify_eq hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
  -- The conditions.
  have hz := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  have hiff : (Ecdh.Valid c.C (s₀.mem (s₀.gpr .x0)) (keyX c s₀) (keyY c s₀) ∧
      (1 ≤ sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (1 ≤ sigS c s₀ ∧ sigS c s₀ < c.C.n) ∧
      tmv c.C c.n (s₀.gpr .x3) s₃ (c.sl RZ) ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) ↔
      ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
        sv c (s₀.gpr .x3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
      exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
    · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
      exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
  unfold VPost
  rw [hashToInt_eq c, hspec, ret]
  by_cases h : (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
      sv c (s₀.gpr .x3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)
  · rw [ite_eq_left (decide_eq_true (hiff.mpr h)), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp (of_decide_eq_true h'))), ite_eq_right h]


theorem verify_ok (hc : BaseCfgOk p192) (hC : Law p192.C)
    {s₀ : State} (hp : FrontPre p192 s₀) :
    WP isa Impl.Ecdsa.Verify.AArch64.P192.verify s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ VPost p192 s₀ s' :=
  verifyWithPoints_ok hc hC Impl.Ecdsa.Verify.AArch64.P192.points
    (fun hM => points_ok hc hM hC) hp

end VG.Proof.Ecdsa.Verify.AArch64.P192
