module

public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Front
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Scalars
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Points
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Final
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Weierstrass.MulContract

/-!
# ECDSA verification on PPC64LE: the whole function

As on 32-bit ARM (`Proof/Ecdsa/Verify/Arm/Main.lean`). `verify_ok`:
`Cfg.verify` returns 1 exactly if the specification's verification of the
signature holds, for any curve the proof of the code supports (`CfgOk`)
whose group law the proofs support (`Law`), restores the callee-saved
registers and `lr`, keeps `sp` and writes only the working space.
`front_ok`, `mid_ok`, `points_ok` and `vtail_ok` compute what
`Proof.Ecdsa.verify_eq` connects to the specification.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdh.PPC64LE VG.Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.Point (tmv)
open VG.Impl.Ecdh.PPC64LE (PX PY)
open VG.Impl.Ecdsa.Verify.PPC64LE (U V)

variable {c : Cfg}

/-- The result the contract asks for: 1 exactly if the specification's
verification holds. -/
def VPost (c : Cfg) (s₀ s' : State) : Prop :=
  s'.gpr .r3 =
    if Spec.Ecdsa.verify c.C (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3) (1 + 2 * c.C.len))
      (Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r4) c.C.len))
      (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (2 * c.C.len)) then 1 else 0

/-- What the function keeps: the callee-saved registers, `sp` and `lr`, and
memory but the working space. -/
structure VKeep (s₀ s' : State) : Prop where
  saved : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r
  sp : s'.sp = s₀.sp
  lr : s'.lr = s₀.lr
  frame : Unch (s₀.gpr .r6) [(0, size)] s₀.mem s'.mem

theorem verifyWith_eq (c : Cfg) (pts : Prog isa) : Impl.Ecdsa.Verify.PPC64LE.Cfg.verifyWith c pts =
    .seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.prefix' c) (.seq (.block (Impl.Ecdsa.Verify.PPC64LE.Cfg.loadS c))
      (.seq (.block (Impl.Ecdh.PPC64LE.Cfg.peerAt c .r14)) (.seq (Impl.Ecdh.PPC64LE.Cfg.validate c)
      (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.scalars c) (.seq c.invN
      (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.uv c) (.seq pts
      (.seq c.invP (Impl.Ecdsa.Verify.PPC64LE.Cfg.final c))))))))) := rfl

/-- What a computation of `[u]G + [v]Q` into `R` does, as `points_ok` states
it: from the stages before (`Mid`, naming the statics `s₀` names), with the
key's point `P` at `PX`, `PY`, `ONEP`, it leaves `Pts`. -/
def PtsOk (c : Cfg) (s₀ : State) (pts : Prog isa) : Prop :=
  ∀ {s : State}, Mid c s₀ (s₀.gpr .r6) s → s.syms = s₀.syms → ∀ {P : Point c.C}, onCurve c.C P = true →
    Rep c.C (tmv c.C c.n (s₀.gpr .r6) s (c.sl PX)) (tmv c.C c.n (s₀.gpr .r6) s (c.sl PY))
      (tmv c.C c.n (s₀.gpr .r6) s (c.sl ONEP)) P →
    ∀ {rest : Prog isa} {Q : State → Prop},
      (∀ s', Pts c s₀ (s₀.gpr .r6) (sv c (s₀.gpr .r6) s U) (sv c (s₀.gpr .r6) s V) P s' → WP isa rest s' Q) →
      WP isa (.seq pts rest) s Q

/-- `Cfg.verifyWith c pts` returns whether the specification's verification
holds, and restores the callee-saved registers, for `pts` computing
`[u]G + [v]Q` as `PtsOk` states. -/
theorem verifyWith_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State}
    {extra : List Region} (hp : VPre c s₀ extra) {pts : Prog isa} (hpts : PtsOk c s₀ pts) :
    WP isa (Impl.Ecdsa.Verify.PPC64LE.Cfg.verifyWith c pts) s₀ fun s' => VKeep s₀ s' ∧ VPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have setupRun := front_ok hc hp (rest := .seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.scalars c)
    (.seq c.invN (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.uv c) (.block []))))
    (Q := fun s => Mid c s₀ (s₀.gpr .r6) s) (fun _ F => mid_ok hc F fun _ M => WP.block_nil M)
  have finish : ∀ s₂, Mid c s₀ (s₀.gpr .r6) s₂ → s₂.syms = s₀.syms →
      WP isa (.seq pts (.seq c.invP (Impl.Ecdsa.Verify.PPC64LE.Cfg.final c))) s₂
        (fun t => VKeep s₀ t ∧ VPost c s₀ t) := by
    intro s₂ hM syms₂
    -- The point the second ladder multiplies.
    let P := peerPt c (s₀.mem (s₀.gpr .r3) = 4) (keyX c s₀) (keyY c s₀)
    have hPc : onCurve c.C P = true := peerPt_onCurve hc _ _ _
    have h1 : tmv c.C c.n (s₀.gpr .r6) s₂ (c.sl ONEP) = 1 := by
      show toM _ _ (wordsVal s₂.mem _ (c.sl ONEP) c.n) = _
      rw [hM.fixed.onep]; exact toM_one hpR
    have hQ : Rep c.C (tmv c.C c.n (s₀.gpr .r6) s₂ (c.sl PX)) (tmv c.C c.n (s₀.gpr .r6) s₂ (c.sl PY))
        (tmv c.C c.n (s₀.gpr .r6) s₂ (c.sl ONEP)) P := by
      rw [h1]
      exact peerPt_rep hC _ _ _ hM.px hM.py
    refine hpts hM syms₂ hPc hQ fun s₃ hP => ?_
    refine WP.mono (vtail_ok hc hP) fun s' ⟨saved, sp, lr, frame, xo, hxo, hx, ret⟩ =>
      ⟨⟨saved, sp, lr, frame⟩, ?_⟩
    have hR := hP.pt
    -- The arguments as the specification reads them.
    have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
      rw [length_bytesAt]; omega_using []
    have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .r3)) := by
      rw [peer_bytes]; rfl
    have hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
        keyX c s₀ := by
      rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
    have hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
        keyY c s₀ := by
      rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
    have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (s₀.gpr .r3)) (keyX c s₀) (keyY c s₀),
        P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
      show peerPt c _ _ _ = _
      unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
    have h16 : 2 * c.C.len = c.C.len + c.C.len := by omega_using []
    have hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (2 * c.C.len)).take c.C.len) = sigR c s₀ := by
      rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
    have hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (2 * c.C.len)).drop c.C.len) = sigS c s₀ := by
      rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
    have hspec := Proof.Ecdsa.verify_eq hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
    -- The conditions.
    have hz := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
    have hiff : (Ecdh.Valid c.C (s₀.mem (s₀.gpr .r3)) (keyX c s₀) (keyY c s₀) ∧
        (1 ≤ sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (1 ≤ sigS c s₀ ∧ sigS c s₀ < c.C.n) ∧
        tmv c.C c.n (s₀.gpr .r6) s₃ (c.sl RZ) ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) ↔
        ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
          sv c (s₀.gpr .r6) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
      constructor
      · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
        exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
      · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
        exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
    unfold VPost
    rw [hashToInt_eq c, hspec, ret]
    by_cases h : (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
        sv c (s₀.gpr .r6) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)
    · rw [ite_eq_left (decide_eq_true (hiff.mpr h)), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hiff.mp (of_decide_eq_true h'))), ite_eq_right h]
  have run := VG.PPC64LE.WP.mono_syms setupRun finish
  simpa only [Impl.Ecdsa.Verify.PPC64LE.Cfg.verifyWith, Impl.Ecdsa.Verify.PPC64LE.Cfg.backWith,
    WP.seq_iff (M := isa), WP.block_nil_iff (M := isa)] using run

/-- `vg_ecdsa_<curve>_verify` returns whether the specification's
verification holds, and restores the callee-saved registers. -/
theorem verify_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {s₀ : State}
    {extra : List Region} (hp : VPre c s₀ extra) :
    WP isa (Impl.Ecdsa.Verify.PPC64LE.Cfg.verify c) s₀ fun s' => VKeep s₀ s' ∧ VPost c s₀ s' :=
  verifyWith_ok hc hC hp fun hM _ _ hP hQ _ _ h => points_ok hc h3 hC hM hP hQ h

end VG.Proof.Ecdsa.Verify.PPC64LE
