import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.ProjectiveFinal
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPoints

namespace VG.Proof.Ecdsa.Verify.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdh.X86
open VG.Impl.Ecdh.X86 (PX PY)
open VG.Impl.Ecdsa.Verify.X86 (U V)

variable {c : Cfg}

theorem verifyCombBody_ok (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c)
    (hCo : ∀ d, c.comb = some d → CombOk c d) (ham3 : AM3 c.C)
    {s₀ : State} {extra : List Region} (hp : VPre c s₀ extra)
    (hTb : ∀ d, c.comb = some d → TblMem s₀ ((s₀.gpr .eax).setWidth 64) (c.combWords d) ∧
      ∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs (ptr s₀ 3) ((s₀.gpr .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    WP isa (Impl.Ecdsa.Verify.X86.Cfg.verifyCombBody c) s₀ fun s' => VKeep s₀ s' ∧ VPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine WP.seq (WP.mono (front_ok hc hp (rest := .block []) (fun _ h => WP.block_nil h)) fun s₁ hF => ?_)
  refine WP.seq (WP.mono (mid_ok hc hF (rest := .block []) (fun _ h => WP.block_nil h)) fun s₂ hM => ?_)
  have F₂ := hM.fixed
  obtain ⟨_, _, h1⟩ := consts_tmv hc F₂
  -- The point the variable-base method multiplies.
  let P := peerPt c (s₀.mem (ptr s₀ 0) = 4) (keyX c s₀) (keyY c s₀)
  have hPc : onCurve c.C P = true := peerPt_onCurve hc _ _ _
  have hQ : Rep c.C (tmv c.C c.n (ptr s₀ 3) s₂ (c.sl PX)) (tmv c.C c.n (ptr s₀ 3) s₂ (c.sl PY))
      (tmv c.C c.n (ptr s₀ 3) s₂ (c.sl ONEP)) P := by
    rw [h1]
    exact peerPt_rep hC _ _ _ hM.px hM.py
  refine pointsComb_ok hc hC hT hCo ham3 hM
    (fun d hd => by
      obtain ⟨ht, ho⟩ := hTb d hd
      exact ⟨ht.of_unch (by rw [hM.rd, hM.wr]) hM.unch
        (fun w hw => by rw [List.mem_singleton.mp hw]; exact Nat.le_refl _) ho, ho⟩)
    hPc hQ
    fun s₃ hP => ?_
  refine WP.mono (tail_dispatch_ok hc hC hP) fun s' ⟨saved, esp, frame, xo, hxo, hx, ret⟩ =>
    ⟨⟨saved, esp, frame⟩, ?_⟩
  obtain ⟨X1, Y1, Z1, X2, Y2, Z2, q1, q2, hsum⟩ := hP.pt
  have q1' : Rep c.C X1 Y1 Z1 (mul (sv c (ptr s₀ 3) s₂ U) (G c.C)) := by
    have := q1; simp only [Nat.shiftRight_zero] at this; exact this
  have q2' : Rep c.C X2 Y2 Z2 (mul (sv c (ptr s₀ 3) s₂ V) P) := by
    have := q2; simp only [Nat.shiftRight_zero] at this; exact this
  have hR := Rep.add hC (hC.onCurve_mul hc.onG _) (hC.onCurve_mul hPc _) q1' q2' hsum.symm
  -- The arguments as the specification reads them.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 0) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 0) (1 + 2 * c.C.len)).head? = some (s₀.mem (ptr s₀ 0)) := by
    rw [peer_bytes]; rfl
  have hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 0) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s₀ := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  have hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 0) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s₀ := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (ptr s₀ 0)) (keyX c s₀) (keyY c s₀),
      P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    show peerPt c _ _ _ = _
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have h16 : 2 * c.C.len = c.C.len + c.C.len := by omega
  have hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (2 * c.C.len)).take c.C.len) = sigR c s₀ := by
    rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
  have hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (2 * c.C.len)).drop c.C.len) = sigS c s₀ := by
    rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
  have hspec := Proof.Ecdsa.verify_eq hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
  -- The conditions.
  have hz := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  have hiff : (Ecdh.Valid c.C (s₀.mem (ptr s₀ 0)) (keyX c s₀) (keyY c s₀) ∧
      (1 ≤ sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (1 ≤ sigS c s₀ ∧ sigS c s₀ < c.C.n) ∧
      tmv c.C c.n (ptr s₀ 3) s₃ (c.sl RZ) ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) ↔
      ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
        sv c (ptr s₀ 3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
      exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
    · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
      exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
  unfold VPost
  rw [hashToInt_eq c, hspec, ret]
  by_cases h : (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
      sv c (ptr s₀ 3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)
  · rw [ite_eq_left (decide_eq_true (hiff.mpr h)), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp (of_decide_eq_true h'))), ite_eq_right h]

end VG.Proof.Ecdsa.Verify.X86
