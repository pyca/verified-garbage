import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Final
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdh.Arm.Main

/-!
# ECDSA verification on 32-bit ARM: the whole function

As on x86 (`Proof/Ecdsa/Verify/X86/Main.lean`).

`verify_ok`: `Cfg.verify` returns 1 exactly if the specification's
verification of the signature holds, for any curve the proof of the code
supports (`CfgOk`) whose group law the proofs support (`Law`), restores the
callee-saved registers and `lr`, keeps `sp` and writes only the working space.
`front_ok`, `mid_ok`, `points_ok` (with the invariants of the group law for
the two ladders, `step_rep`) and `vtail_ok` compute what
`Proof.Ecdsa.verify_eq` connects to the specification.
-/

namespace VG.Proof.Ecdsa.Verify.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Impl.Ecdh.Arm (PX PY)
open VG.Impl.Ecdsa.Verify.Arm (U V)

variable {c : Cfg}

/-- The result the contract asks for: 1 exactly if the specification's
verification holds. -/
def VPost (c : Cfg) (s₀ s' : State) : Prop :=
  s'.gpr .r0 =
    if Spec.Ecdsa.verify c.C (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r0) (1 + 16 * c.n))
      (Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r1) (8 * c.n)))
      (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r2) (16 * c.n)) then 1 else 0

/-- What the function keeps: the callee-saved registers and `lr`, `sp`, and memory
but the working space. -/
structure VKeep (s₀ s' : State) : Prop where
  saved : ∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1
  sp : s'.sp = s₀.sp
  frame : Unch (ptr s₀ .r3) [(0, 8192)] s₀.mem s'.mem

/-- What the slots of `a`, `3b` and `G` stand for. -/
theorem consts_tmv (hc : CfgOk c) {base : Addr} {g : Reg → BitVec 32} {s : State}
    (F : Fixed c base g s.mem) :
    tmv c.C c.n base s (c.sl AP) = Fin.ofNat c.C.p c.C.a ∧
      tmv c.C c.n base s (c.sl B3P) = Fin.ofNat c.C.p (3 * c.C.b) ∧
      tmv c.C c.n base s (c.sl ONEP) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · show toM _ _ (wordsVal s.mem base (c.sl AP) c.n) = _
    rw [F.ap]; exact toM_cmont hc _
  · show toM _ _ (wordsVal s.mem base (c.sl B3P) c.n) = _
    rw [F.b3p]; exact toM_cmont hc _
  · show toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n) = _
    rw [F.onep]; exact toM_one (unitMod_pow_two hc.p_odd _)

/-- `vg_ecdsa_<curve>_verify` returns whether the specification's
verification holds, and restores the callee-saved registers. -/
theorem verify_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State} (hp : VPre c s₀) :
    WP isa (Impl.Ecdsa.Verify.Arm.Cfg.verify c) s₀ fun s' => VKeep s₀ s' ∧ VPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine front_ok hc hp fun s₁ hF => mid_ok hc hF fun s₂ hM => ?_
  have F₂ := hM.fixed
  obtain ⟨ha, hb, h1⟩ := consts_tmv hc F₂
  -- The point the second ladder multiplies.
  let P := peerPt c (s₀.mem (ptr s₀ .r0) = 4) (keyX c s₀) (keyY c s₀)
  have hPc : onCurve c.C P = true := peerPt_onCurve hc _ _ _
  have hG : Rep c.C (tmv c.C c.n (ptr s₀ .r3) s₂ (c.sl GX)) (tmv c.C c.n (ptr s₀ .r3) s₂ (c.sl GY))
      (tmv c.C c.n (ptr s₀ .r3) s₂ (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s₂.mem _ (c.sl GX) c.n)) (toM _ _ (wordsVal s₂.mem _ (c.sl GY) c.n))
      (toM _ _ (wordsVal s₂.mem _ (c.sl ONEP) c.n)) (G c.C)
    rw [F₂.gx, F₂.gy, toM_cmont hc, toM_cmont hc, show toM c.C.p (2 ^ (64 * c.n))
      (wordsVal s₂.mem (ptr s₀ .r3) (c.sl ONEP) c.n) = 1 from h1]
    exact rep_affine' hC _ _
  have hQ : Rep c.C (tmv c.C c.n (ptr s₀ .r3) s₂ (c.sl PX)) (tmv c.C c.n (ptr s₀ .r3) s₂ (c.sl PY))
      (tmv c.C c.n (ptr s₀ .r3) s₂ (c.sl ONEP)) P := by
    rw [h1]
    exact peerPt_rep hC _ _ _ hM.px hM.py
  have hu : sv c (ptr s₀ .r3) s₂ U < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  have hv : sv c (ptr s₀ .r3) s₂ V < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  refine points_ok hc hM
    (Q₁ := fun j X Y Z => Rep c.C X Y Z (mul (sv c (ptr s₀ .r3) s₂ U >>> j) (G c.C)))
    (Q₂ := fun j X Y Z => Rep c.C X Y Z (mul (sv c (ptr s₀ .r3) s₂ V >>> j) P))
    (step_rep hC hc.onG ha hb hG)
    (by rw [shiftRight_eq_zero hu, mul_zero_pt]; exact rep_infinity' hC)
    (step_rep hC hPc ha hb hQ)
    (by rw [shiftRight_eq_zero hv, mul_zero_pt]; exact rep_infinity' hC)
    fun s₃ hP => ?_
  refine WP.mono (vtail_ok hc hP) fun s' ⟨saved, sp, frame, xo, hxo, hx, ret⟩ =>
    ⟨⟨saved, sp, frame⟩, ?_⟩
  obtain ⟨X1, Y1, Z1, X2, Y2, Z2, q1, q2, hsum⟩ := hP.pt
  have q1' : Rep c.C X1 Y1 Z1 (mul (sv c (ptr s₀ .r3) s₂ U) (G c.C)) := by
    have := q1; simp only [Nat.shiftRight_zero] at this; exact this
  have q2' : Rep c.C X2 Y2 Z2 (mul (sv c (ptr s₀ .r3) s₂ V) P) := by
    have := q2; simp only [Nat.shiftRight_zero] at this; exact this
  have hR := Rep.add hC (hC.onCurve_mul hc.onG _) (hC.onCurve_mul hPc _) q1' q2' hsum.symm
  -- The arguments as the specification reads them.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r0) (1 + 16 * c.n)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt, hc.len]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r0) (1 + 16 * c.n)).head? = some (s₀.mem (ptr s₀ .r0)) := by
    rw [peer_bytes]; rfl
  have hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r0) (1 + 16 * c.n)).drop 1).take c.C.len) =
      keyX c s₀ := by
    rw [peer_bytes, List.drop_one, List.tail_cons, hc.len, List.take_left' (length_bytesAt _ _ _)]
  have hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r0) (1 + 16 * c.n)).drop (c.C.len + 1)) =
      keyY c s₀ := by
    rw [peer_bytes, hc.len, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (ptr s₀ .r0)) (keyX c s₀) (keyY c s₀),
      P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    show peerPt c _ _ _ = _
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have h16 : 16 * c.n = 8 * c.n + 8 * c.n := by omega
  have hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r2) (16 * c.n)).take c.C.len) = sigR c s₀ := by
    rw [h16, bytesAt_add, hc.len, List.take_left' (length_bytesAt _ _ _)]
  have hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r2) (16 * c.n)).drop c.C.len) = sigS c s₀ := by
    rw [h16, bytesAt_add, hc.len, List.drop_left' (length_bytesAt _ _ _)]
  have hspec := Proof.Ecdsa.verify_eq hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
  -- The conditions.
  have hz := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  have hiff : (Ecdh.Valid c.C (s₀.mem (ptr s₀ .r0)) (keyX c s₀) (keyY c s₀) ∧
      (1 ≤ sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (1 ≤ sigS c s₀ ∧ sigS c s₀ < c.C.n) ∧
      tmv c.C c.n (ptr s₀ .r3) s₃ (c.sl RZ) ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) ↔
      ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
        sv c (ptr s₀ .r3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
      exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
    · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
      exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
  unfold VPost
  rw [hashToInt_eq hc, hspec, ret]
  by_cases h : (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
      sv c (ptr s₀ .r3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)
  · rw [ite_eq_left (decide_eq_true (hiff.mpr h)), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp (of_decide_eq_true h'))), ite_eq_right h]

end VG.Proof.Ecdsa.Verify.Arm
