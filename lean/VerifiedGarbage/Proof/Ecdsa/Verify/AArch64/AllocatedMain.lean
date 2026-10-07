import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedScalars
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint

/-! The Jacobian verifier satisfies the existing complete verification postcondition. -/
namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V)

variable {c : Cfg}

/-- Any proven joint multiplication can feed the unchanged verifier prefix and final check. -/
theorem verify_of_joint_inverse (hc : CfgOk c) (hC : Law c.C) (inverse points program : Prog isa)
    (hmid : ∀ {s₀ : State} {base : Addr} {g : Reg → BitVec 64} {s : State},
      Front c s₀ base g s → ∀ {rest : Prog isa} {Q : State → Prop},
      (∀ s',Mid c s₀ base g s' → WP isa rest s' Q) →
      WP isa (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.scalars c) (.seq inverse
        (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.uv c) rest))) s Q)
    (heq : program =
      .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.args c)) (.seq (.seq (.block (c.setupWith (some D)))
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8*c.n)) (.block [])))
      (.seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.loadS c)) (.seq (.block (Impl.Ecdh.AArch64.Cfg.peer c))
      (.seq (Impl.Ecdh.AArch64.Cfg.validate c) (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.scalars c)
      (.seq inverse (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.uv c)
      (.seq points (Impl.Ecdsa.Verify.AArch64.Cfg.tail c))))))))))
    (hpoints : ∀ {s₀ : State} {base : Addr} {g : Reg → BitVec 64} {s : State},
      Mid c s₀ base g s → TblPre c s₀ (s₀.syms c.tsym) base →
      ∀ {P : Point c.C},onCurve c.C P=true →
      Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
        (tmv c.C c.n base s (c.sl ONEP)) P →
      WP isa points s fun t => FinalState c s₀ base g t ∧
        Rep c.C (tmv c.C c.n base t (c.sl RX)) (tmv c.C c.n base t (c.sl RY))
          (tmv c.C c.n base t (c.sl RZ))
          (add (mul (sv c base s U) (G c.C)) (mul (sv c base s V) P)))
    {s₀ : State} (hp : VPre c s₀) :
    WP isa program s₀ fun s' =>
      (∀ r∈Cfg.saved.map Prod.fst,s'.gpr r=s₀.gpr r) ∧ VPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  rw [heq]
  refine front_ok hc hp fun g s₁ hg hF => hmid hF fun s₂ hM => ?_
  have F₂ := hM.fixed
  have h1 := onep_tmv hc F₂
  -- The point the window method multiplies.
  let P := peerPt c (s₀.mem (s₀.gpr .x0) = 4) (keyX c s₀) (keyY c s₀)
  have hPc : onCurve c.C P = true := peerPt_onCurve hc _ _ _
  have hQ : Rep c.C (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl PX)) (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl PY))
      (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl ONEP)) P := by
    rw [h1]
    exact peerPt_rep hC _ _ _ hM.px hM.py
  refine WP.seq (WP.mono (hpoints hM hp.tbl hPc hQ) fun s₃ ⟨hP,hR⟩ => ?_)
  refine WP.mono (tail_dispatch_ok hc hC hP) fun s' ⟨saved,xo,hxo,hx,ret⟩ =>
    ⟨fun r hr => (saved r hr).trans (hg r hr),?_⟩
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

end VG.Proof.Ecdsa.Verify.AArch64
