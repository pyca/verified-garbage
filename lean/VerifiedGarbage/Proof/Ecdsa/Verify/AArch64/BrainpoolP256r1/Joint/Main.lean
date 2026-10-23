module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Points
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
import VerifiedGarbage.Proof.Ecdh.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages

/-! Full ECDSA verification correctness with the joint public multiplier. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

theorem verify_ok (hc : BaseCfgOk cfg) (hC : Law C) {s₀ : State} (hp : FrontPre cfg s₀) :
    WP isa verify s₀ fun s' => (∀ r ∈ Cfg.saved.map Prod.fst,s'.gpr r=s₀.gpr r) ∧ VPost cfg s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * cfg.n)
  unfold Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.verify
  unfold Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.verifyWithPoints
  refine front_ok hc hp fun g s₁ hg hF => mid_ok hc hF fun s₂ hM => ?_
  have F₂ := hM.fixed
  have h1 := onep_tmv hc F₂
  -- The validated peer point.
  let P := peerPt cfg (s₀.mem (s₀.gpr .x0) = 4) (keyX cfg s₀) (keyY cfg s₀)
  have hPc : onCurve cfg.C P = true := peerPt_onCurve hc _ _ _
  have hQ : Rep cfg.C (tmv cfg.C cfg.n (s₀.gpr .x3) s₂ (cfg.sl PX)) (tmv cfg.C cfg.n (s₀.gpr .x3) s₂ (cfg.sl PY))
      (tmv cfg.C cfg.n (s₀.gpr .x3) s₂ (cfg.sl ONEP)) P := by
    rw [h1]
    exact peerPt_rep hC _ _ _ hM.px hM.py
  refine WP.seq (WP.mono (points_ok hc hC hPc hM hQ) fun s₃ ⟨hP,hR⟩ => ?_)
  refine WP.mono (tail_dispatch_ok hc hC hP) fun s' ⟨saved,xo,hxo,hx,ret⟩ =>
    ⟨fun r hr => (saved r hr).trans (hg r hr),?_⟩
  -- The arguments as the specification reads them.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * cfg.C.len)).length = 2 * cfg.C.len + 1 := by
    rw [length_bytesAt]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * cfg.C.len)).head? = some (s₀.mem (s₀.gpr .x0)) := by
    rw [peer_bytes]; rfl
  have hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * cfg.C.len)).drop 1).take cfg.C.len) =
      keyX cfg s₀ := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  have hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * cfg.C.len)).drop (cfg.C.len + 1)) =
      keyY cfg s₀ := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hP' : ∀ h : Ecdh.Valid cfg.C (s₀.mem (s₀.gpr .x0)) (keyX cfg s₀) (keyY cfg s₀),
      P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    show peerPt cfg _ _ _ = _
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have h16 : 2 * cfg.C.len = cfg.C.len + cfg.C.len := by omega
  have hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (2 * cfg.C.len)).take cfg.C.len) = sigR cfg s₀ := by
    rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
  have hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (2 * cfg.C.len)).drop cfg.C.len) = sigS cfg s₀ := by
    rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
  have hspec := Proof.Ecdsa.verify_eq hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
  -- The conditions.
  have hz := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  have hiff : (Ecdh.Valid cfg.C (s₀.mem (s₀.gpr .x0)) (keyX cfg s₀) (keyY cfg s₀) ∧
      (1 ≤ sigR cfg s₀ ∧ sigR cfg s₀ < cfg.C.n) ∧ (1 ≤ sigS cfg s₀ ∧ sigS cfg s₀ < cfg.C.n) ∧
      tmv cfg.C cfg.n (s₀.gpr .x3) s₃ (cfg.sl RZ) ≠ 0 ∧ Fin.ofNat cfg.C.n xo = Fin.ofNat cfg.C.n (sigR cfg s₀)) ↔
      ((KeyOk cfg s₀ ∧ (0 < sigR cfg s₀ ∧ sigR cfg s₀ < cfg.C.n) ∧ (0 < sigS cfg s₀ ∧ sigS cfg s₀ < cfg.C.n)) ∧
        sv cfg (s₀.gpr .x3) s₃ RZ ≠ 0 ∧ Fin.ofNat cfg.C.n xo = Fin.ofNat cfg.C.n (sigR cfg s₀)) := by
    constructor
    · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
      exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
    · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
      exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
  unfold VPost
  rw [hashToInt_eq cfg, hspec, ret]
  split <;> split
  · rfl
  · rename_i ht hf
    exact False.elim (hf (decide_eq_true (hiff.mpr ht)))
  · rename_i hf ht
    exact False.elim (hf (hiff.mp (of_decide_eq_true ht)))
  · rfl

end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
