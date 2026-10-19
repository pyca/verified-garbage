module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Ed25519.Group.Double
public import VerifiedGarbage.Proof.Ed25519.X86.PointTable
public import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTInputs

import VerifiedGarbage.Proof.Ed25519.X86.WindowCT
meta import VerifiedGarbage.Proof.Ed25519.X86.WindowCT
import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86.PointEqual
meta import VerifiedGarbage.Proof.Ed25519.X86.PointEqual
import VerifiedGarbage.Proof.Ed25519.X86.VerifyPoints
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyPoints
import VerifiedGarbage.Proof.Framework.X86.TaintSym
meta import VerifiedGarbage.Proof.Framework.X86.TaintSym
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Ed25519.Window
meta import VerifiedGarbage.Proof.Ed25519.Window
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Impl.Mont.Mod
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.Ed25519.X86.FreezeField
import VerifiedGarbage.Proof.Ed25519.X86.InputBits
import VerifiedGarbage.Proof.Ed25519.X86.PointDecode
import VerifiedGarbage.Proof.Ed25519.X86.PointEncodeSign
import VerifiedGarbage.Proof.Ed25519.X86.PointMul
import VerifiedGarbage.Proof.Ed25519.X86.Power
import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Proof.Ed25519.X86.ScalarStep
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTBytes
import VerifiedGarbage.Proof.Ed25519.X86.VerifyTables
import VerifiedGarbage.Proof.Ed25519.X86.WindowTables
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Proof.X25519.X86.Freeze
import VerifiedGarbage.Spec.Rc2
meta import VerifiedGarbage.Impl.Mont.Mod
meta import VerifiedGarbage.Proof.Ed25519.Bytes
meta import VerifiedGarbage.Proof.Ed25519.ScalarBytes
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
meta import VerifiedGarbage.Proof.Ed25519.X86.FreezeField
meta import VerifiedGarbage.Proof.Ed25519.X86.InputBits
meta import VerifiedGarbage.Proof.Ed25519.X86.PointDecode
meta import VerifiedGarbage.Proof.Ed25519.X86.PointEncodeSign
meta import VerifiedGarbage.Proof.Ed25519.X86.PointMul
meta import VerifiedGarbage.Proof.Ed25519.X86.Power
meta import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarStep
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTBytes
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyTables
meta import VerifiedGarbage.Proof.Ed25519.X86.WindowTables
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.X25519.X86.Fold
meta import VerifiedGarbage.Proof.X25519.X86.Freeze
meta import VerifiedGarbage.Spec.Rc2

/-!
# Verification's equation: what its traces depend on

The windows' traces depend only on the public scalars (`windowMultiply_ct`), and the projective
comparison's on whether the points represented are equal (`pointEqualRep_ct`), the same in both
runs.
-/

@[expose] public section

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
  · apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by native_taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)
  · apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by native_taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)

/-- Two points representing `P` and `Q` in slots 0–3 and 4–7. -/
def EqRepPre (base : BitVec 32) (P Q : Edwards.EPoint VG.Proof.Ed25519.dZ) (s : State) : Prop :=
  Ctx base s ∧ VG.Proof.Ed25519.RepP (point (env s.mem base) 0 1 2 3) P ∧
    VG.Proof.Ed25519.RepP (point (env s.mem base) 4 5 6 7) Q

/-- Before pass `n` of `equalStep`: slots 8 and 9 are equal exactly when `P` and `Q` agree in `x`
(`n = 2`, with slots 10 and 11 for `y`) or in `y` (`n = 1`). -/
def EqLoopCT (base : BitVec 32) (P Q : Edwards.EPoint VG.Proof.Ed25519.dZ) (n : Nat) (s : State) : Prop :=
  Ctx base s ∧ s.gpr .esi = BitVec.ofNat 32 n ∧
    ((n = 2 ∧ (env s.mem base 8 = env s.mem base 9 ↔ P.x = Q.x) ∧
        (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) ∨
      (n = 1 ∧ (env s.mem base 8 = env s.mem base 9 ↔ P.y = Q.y)))

/-- The condition pass `n` compares. -/
abbrev eqCond (P Q : Edwards.EPoint VG.Proof.Ed25519.dZ) (n : Nat) : Prop := if n = 2 then P.x = Q.x else P.y = Q.y

theorem EqLoopCT.cond {base : BitVec 32} {P Q : Edwards.EPoint VG.Proof.Ed25519.dZ} {n : Nat} {s : State}
    (h : EqLoopCT base P Q n s) : env s.mem base 8 = env s.mem base 9 ↔ eqCond P Q n := by
  rcases h.2.2 with ⟨rfl, e, _⟩ | ⟨rfl, e⟩
  · exact e
  · exact e

/-- One pass: its trace depends only on the comparison, which is the same in both runs. -/
theorem equalStep_ct (base : BitVec 32) (P Q : Edwards.EPoint VG.Proof.Ed25519.dZ) (n : Nat) :
    RelCT isa (fun s t => EqLoopCT base P Q n s ∧ EqLoopCT base P Q n t) equalStep (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => EqLoopCT base P Q n s ∧ EqLoopCT base P Q n t)
      (.block (fieldEqual 8 9)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by native_taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw (s : State) (h : EqLoopCT base P Q n s) :
      WP isa (.block (fieldEqual 8 9)) s fun t => Ctx base t ∧ t.zf = some (decide (eqCond P Q n)) :=
    WP.mono (fieldEqual_ok h.1 8 9) fun t k => ⟨k.1.ctx h.1, by
      rw [k.2.2]; exact congrArg some (decide_eq_decide.mpr h.cond)⟩
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [equalStep]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by native_taint_decide)
    exact fun _ _ h => edi_agree h.1.2.1.1.edi h.1.2.2.1.edi
  · apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by native_taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)

/-- The comparison branches on whether the points represented are equal. -/
theorem pointEqualRep_ct (base : BitVec 32) (P Q : Edwards.EPoint VG.Proof.Ed25519.dZ) :
    RelCT isa (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      Impl.Ed25519.X86.pointEqual (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      (.block (fieldCode pointEqualOps ++ [.mov .esi (.imm 2)])) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by native_taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw (s : State) (h : EqRepPre base P Q s) :
      WP isa (.block (fieldCode pointEqualOps ++ [.mov .esi (.imm 2)])) s (EqLoopCT base P Q 2) := by
    rw [WP.block_append_iff]
    refine WP.mono (fieldCode_ok pointEqualOps h.1) fun a ⟨ka, ea⟩ => Wp.wp_movi fun t u => WP.block_nil ?_
    have ev := ctEqualOps_eval (env s.mem base)
    refine ⟨(IKeep.of_counter u).ctx (ka.ctx h.1), u.gpr, .inl ⟨rfl, ?_, ?_⟩⟩
    · rw [u.mem, ea, ev.1, ev.2.1]; exact VG.Proof.Ed25519.repP_cross_x h.2.1 h.2.2
    · rw [u.mem, ea, ev.2.2.1, ev.2.2.2]; exact VG.Proof.Ed25519.repP_cross_y h.2.1 h.2.2
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [Impl.Ed25519.X86.pointEqual]
  refine VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (VG.RelCT.loop (M := isa) (body := equalStep) (c := .ne) (Q := fun _ _ => True) (fun (n : Nat) (s t : State) => EqLoopCT base P Q n s ∧ EqLoopCT base P Q n t)
      (fun n => ?_) 2)
  -- One pass: the same branch in both runs, and the next pass's facts.
  have step (s : State) (h : EqLoopCT base P Q n s) : WP isa equalStep s fun t =>
      isa.eval .ne t = some (decide (eqCond P Q n ∧ n - 1 ≠ 0)) ∧
      (eqCond P Q n ∧ n - 1 ≠ 0 → EqLoopCT base P Q (n - 1) t) := by
    have hn : 1 ≤ n ∧ n ≤ 2 := by rcases h.2.2 with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
    refine WP.mono (equalStep_ok h.1 hn.1 hn.2 h.2.1) fun t ⟨k, yes, no⟩ => ?_
    by_cases c : eqCond P Q n
    · obtain ⟨_, ri, rz, r8, r9⟩ := yes (h.cond.mpr c)
      refine ⟨by rw [rz]; simp [c], fun ⟨_, hn1⟩ => ⟨k.ctx h.1, ri, ?_⟩⟩
      rcases h.2.2 with ⟨rfl, _, ey⟩ | ⟨rfl, _⟩
      · exact .inr ⟨rfl, by rw [r8, r9]; exact ey⟩
      · exact absurd rfl hn1
    · obtain ⟨_, rz⟩ := no (fun e => c (h.cond.mp e))
      exact ⟨by rw [rz]; simp [c], fun ⟨c', _⟩ => absurd c' c⟩
  refine (VG.RelCT.wp (equalStep_ct base P Q n) fun s t h => ⟨step s h.1, step t h.2⟩).mono
    (fun _ _ h => h) fun s t ⟨_, ⟨es, ns⟩, ⟨et, nt⟩⟩ => ⟨es.trans et.symm, fun _ => trivial, fun e => ?_⟩
  rw [es] at e
  have c := of_decide_eq_true (Option.some.inj e)
  exact ⟨n - 1, by omega, ns c, nt c⟩

end VG.Proof.Ed25519.X86

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards

/-- Before the equation's points: the saved state, `A` at byte 7680, `R` at byte 7808, and the
static's address. -/
def PointsCTPre (s₀ : State) (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  Saved s₀ (arg s₀ 3) s ∧ tablePoint s.mem (arg s₀ 3) 7680 = a ∧ tablePoint s.mem (arg s₀ 3) 7808 = r ∧
    s.syms = s₀.syms

/-- The copy of the static: its addresses are the static's, public, and the working space's. -/
theorem bTable_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (a r : Spec.Ed25519.Point) :
    RelCT isa (fun s t => PointsCTPre s₀ a r s ∧ PointsCTPre t₀ a r t) bTable (fun _ _ => True) :=
  VG.RelCT.taint (A := taintSym [bSym]) callTaint₀
    (fun _ _ hh => ⟨callTaint₀_agree (h.callPre hh.1.1 hh.2.1), fun n hn => by
      rw [List.mem_singleton.mp hn, hh.1.2.2.2, hh.2.2.2.2]; exact h.sym⟩) (by native_taint_decide)

/-- The windows, `-R`, and the comparison: the windows' traces depend only on the public
scalars, and the comparison's on whether the points represented are equal. -/
theorem verifyEquationPoints_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (a r : Spec.Ed25519.Point)
    {Aa Ra : EPoint dZ} (hA : Rep a Aa) (hR : Rep r Ra) :
    RelCT isa (fun s t => PointsCTPre s₀ a r s ∧ PointsCTPre t₀ a r t) verifyEquationPoints
      (fun _ _ => True) := by
  have bw (u x : State) (hu : VerifyPre u) (hx : PointsCTPre u a r x) : WP isa bTable x (EquationCTPre u a r) :=
    WP.mono (bTable_stage hu hx.1 hx.2.2.2) fun _ ⟨sb, ab, rb, tb⟩ =>
      ⟨sb, ab.trans hx.2.1, rb.trans hx.2.2.1, tb⟩
  have ww (u x : State) (hu : VerifyPre u) (hx : EquationCTPre u a r x) :=
    windowMultiply_ok hu hx.1 hA hx.2.1 hx.2.2.1 hx.2.2.2
  have nw (u x : State) (hx : WinCtx u Aa r x ∧ Rep (point (env x.mem (arg u 3)) 0 1 2 3)
      (verificationChallenge u • Aa + verificationScalar u • (-baseAff))) :
      WP isa (.block negR) x
        (EqRepPre (arg u 3) (verificationChallenge u • Aa + verificationScalar u • (-baseAff)) (-Ra)) :=
    WP.mono (negR_ok hx.1.ctx) fun t ⟨kt, qt, pt⟩ =>
      ⟨kt.ctx hx.1.ctx, by rw [pt]; exact hx.2.proj, by rw [qt, hx.1.r]; exact hR.neg.proj⟩
  rw [verifyEquationPoints]
  refine seq_runs (bTable_ct h a r) (fun x hx => bw s₀ x (verify_pre h.left) hx)
    (fun y hy => bw t₀ y (verify_pre h.right) hy) ?_
  refine seq_runs (windowMultiply_ct h hA) (fun x hx => ww s₀ x (verify_pre h.left) hx)
    (fun y hy => ww t₀ y (verify_pre h.right) hy) ?_
  refine seq_runs (VG.RelCT.taint (A := taint) (regsTaint [.edi])
    (fun _ _ hh => agree_one (saved_edi h hh.1.1.saved hh.2.1.saved)) (by native_taint_decide))
    (fun x hx => nw s₀ x hx) (fun y hy => nw t₀ y hy) ?_
  refine (pointEqualRep_ct (arg s₀ 3) (verificationChallenge s₀ • Aa + verificationScalar s₀ • (-baseAff))
    (-Ra)).mono (fun x y hh => ⟨hh.1, ?_⟩) (fun _ _ h => h)
  rw [h.args 3 (by decide), h.challengeNat, h.scalarNat]
  exact hh.2

end VG.Proof.Ed25519.X86
