import VerifiedGarbage.Proof.Ed25519.X86.WindowCT
import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86.PointEqual
import VerifiedGarbage.Proof.Ed25519.X86.VerifyPoints
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# Verification's equation: what its traces depend on

The windows' traces depend only on the public scalars (`windowMultiply_ct`), and the projective
comparison's on whether the points represented are equal (`pointEqualRep_ct`), the same in both
runs.
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

private theorem ctEqualOps_eval (e : Env) :
    evalOps pointEqualOps e 8 = e 0 * e 6 ∧ evalOps pointEqualOps e 9 = e 4 * e 2 ∧
    evalOps pointEqualOps e 10 = e 1 * e 6 ∧ evalOps pointEqualOps e 11 = e 5 * e 2 := ⟨rfl, rfl, rfl, rfl⟩

theorem equalFirst_ok {s : State} {base : BitVec 32} (hs : Ctx base s) :
    WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
      FieldKeep base s t ∧
      t.zf = some (decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2)) ∧
      env t.mem base 10 = env s.mem base 1 * env s.mem base 6 ∧
      env t.mem base 11 = env s.mem base 5 * env s.mem base 2 := by
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok pointEqualOps hs) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (fieldEqual_ok (ka.ctx hs) 8 9) fun t ⟨kt, te, tz⟩ => ?_
  refine ⟨ka.trans kt, ?_, ?_, ?_⟩
  · rw [tz, va, (ctEqualOps_eval _).1, (ctEqualOps_eval _).2.1]
  · rw [te 10 (by decide), va, (ctEqualOps_eval _).2.2.1]
  · rw [te 11 (by decide), va, (ctEqualOps_eval _).2.2.2]

theorem returnFlag_ct (b : Bool) :
    RelCT isa (fun _ _ => True) (.block [.mov .eax (.imm (if b then 1 else 0))]) (fun _ _ => True) := by
  cases b
  · apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)
  · apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)

/-- Two points representing `P` and `Q` in slots 0–3 and 4–7. -/
def EqRepPre (base : BitVec 32) (P Q : Edwards.EPoint VG.Proof.Ed25519.dZ) (s : State) : Prop :=
  Ctx base s ∧ VG.Proof.Ed25519.RepP (point (env s.mem base) 0 1 2 3) P ∧
    VG.Proof.Ed25519.RepP (point (env s.mem base) 4 5 6 7) Q

/-- The comparison branches on whether the points represented are equal. -/
theorem pointEqualRep_ct (base : BitVec 32) (P Q : Edwards.EPoint VG.Proof.Ed25519.dZ) :
    RelCT isa (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      Impl.Ed25519.X86.pointEqual (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw (s : State) (h : EqRepPre base P Q s) :
      WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
        Ctx base t ∧ t.zf = some (decide (P.x = Q.x)) ∧
          (env t.mem base 10 = env t.mem base 11 ↔ P.y = Q.y) := by
    refine WP.mono (equalFirst_ok h.1) fun t ⟨kt, tz, tu, tv⟩ => ⟨kt.ctx h.1, ?_, ?_⟩
    · rw [tz]
      exact congrArg some (decide_eq_decide.mpr (VG.Proof.Ed25519.repP_cross_x h.2.1 h.2.2))
    · rw [tu, tv]
      exact VG.Proof.Ed25519.repP_cross_y h.2.1 h.2.2
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have ht2 : RelCT isa (fun s t => (Ctx base s ∧ (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) ∧
      (Ctx base t ∧ (env t.mem base 10 = env t.mem base 11 ↔ P.y = Q.y)))
      (.block (fieldEqual 10 11)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw2 (s : State) (h : Ctx base s ∧ (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) :
      WP isa (.block (fieldEqual 10 11)) s fun t => t.zf = some (decide (P.y = Q.y)) :=
    WP.mono (fieldEqual_ok h.1 10 11) fun t k => by
      rw [k.2.2]; exact congrArg some (decide_eq_decide.mpr h.2)
  have hp2 := VG.RelCT.wp ht2 (fun s t h => ⟨hw2 s h.1, hw2 t h.2⟩)
  rw [Impl.Ed25519.X86.pointEqual]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.1.trans h.2.2.2.1.symm
  · refine VG.RelCT.seq (hp2.mono (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩)
      (fun _ _ h => h)) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
    · exact fun _ _ h => h.2.1.trans h.2.2.symm
    · exact (returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
    · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards

/-- The windows, `-R`, and the comparison: the windows' traces depend only on the public
scalars, and the comparison's on whether the points represented are equal. -/
theorem verifyEquationPoints_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (a r : Spec.Ed25519.Point)
    {Aa Ra : EPoint dZ} (hA : Rep a Aa) (hR : Rep r Ra) :
    RelCT isa (fun s t => EquationCTPre s₀ a r s ∧ EquationCTPre t₀ a r t) verifyEquationPoints
      (fun _ _ => True) := by
  have ww (u x : State) (hu : VerifyPre u) (hx : EquationCTPre u a r x) :=
    windowMultiply_ok hu hx.1 hA hx.2.1 hx.2.2
  have nw (u x : State) (hx : WinCtx u Aa r x ∧ Rep (point (env x.mem (arg u 3)) 0 1 2 3)
      (verificationChallenge u • Aa + verificationScalar u • (-baseAff))) :
      WP isa (.block negR) x
        (EqRepPre (arg u 3) (verificationChallenge u • Aa + verificationScalar u • (-baseAff)) (-Ra)) :=
    WP.mono (negR_ok hx.1.ctx) fun t ⟨kt, qt, pt⟩ =>
      ⟨kt.ctx hx.1.ctx, by rw [pt]; exact hx.2.proj, by rw [qt, hx.1.r]; exact hR.neg.proj⟩
  rw [verifyEquationPoints]
  refine seq_runs (windowMultiply_ct h hA) (fun x hx => ww s₀ x (verify_pre h.left) hx)
    (fun y hy => ww t₀ y (verify_pre h.right) hy) ?_
  refine seq_runs (VG.RelCT.taint (A := taint) (regsTaint [.edi])
    (fun _ _ hh => agree_one (saved_edi h hh.1.1.saved hh.2.1.saved)) (by taint_decide))
    (fun x hx => nw s₀ x hx) (fun y hy => nw t₀ y hy) ?_
  refine (pointEqualRep_ct (arg s₀ 3) (verificationChallenge s₀ • Aa + verificationScalar s₀ • (-baseAff))
    (-Ra)).mono (fun x y hh => ⟨hh.1, ?_⟩) (fun _ _ h => h)
  rw [h.args 3 (by decide), h.challengeNat, h.scalarNat]
  exact hh.2

end VG.Proof.Ed25519.X86
