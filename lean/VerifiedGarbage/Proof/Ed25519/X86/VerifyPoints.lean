module

public import VerifiedGarbage.Proof.Ed25519.X86.WindowLoop
public import VerifiedGarbage.Impl.Ed25519.X86.Verify
import VerifiedGarbage.Proof.Ed25519.X86.PointEqual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed25519.X86.WindowTables
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
import VerifiedGarbage.Proof.Ed25519.Window

/-!
# Verification's equation from the windows

The windows' `[k]A - [S]B` equals `-R` exactly when `[S]B = R + [k]A`
(`window_equation`), which the projective comparison checks.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards

theorem negR_eval (e : Env) :
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 4 5 6 7 = negPoint (point e 4 5 6 7) := rfl

theorem negR_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block negR) s fun t => IKeep x s t ∧
      point (env t.mem x) 4 5 6 7 = negPoint (tablePoint s.mem x 7808) ∧
      point (env t.mem x) 0 1 2 3 = point (env s.mem x) 0 1 2 3 := by
  rw [negR, WP.block_append_iff]
  refine WP.mono (pointTableQ_ok hc 7808 (by decide) (by decide)) fun a ⟨ka, _, pa, ha⟩ => ?_
  refine WP.mono (fieldCode_ok _ (ka.ctx hc)) fun t ⟨kt, et⟩ => ⟨ka.trans (IKeep.of_field kt), ?_, ?_⟩
  · rw [et, negR_eval, pa]
  · rw [et]
    change point (env a.mem x) 0 1 2 3 = _
    simp only [point, ha 0 (Or.inl (by decide)), ha 1 (Or.inl (by decide)), ha 2 (Or.inl (by decide)),
      ha 3 (Or.inl (by decide))]

/-- The table of `-[1]B … -[15]B` copied from the static, the points at bytes 7680 and 7808 kept. -/
theorem bTable_stage {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s)
    (hy : s.syms = s₀.syms) :
    WP isa bTable s fun b => Saved s₀ (arg s₀ 3) b ∧
      tablePoint b.mem (arg s₀ 3) 7680 = tablePoint s.mem (arg s₀ 3) 7680 ∧
      tablePoint b.mem (arg s₀ 3) 7808 = tablePoint s.mem (arg s₀ 3) 7808 ∧
      ∀ j < 15, Rep (tablePoint b.mem (arg s₀ 3) (3072 + 128 * j)) ((j + 1) • (-baseAff)) := by
  have hfit := hp.scratch.fit
  have hc := hs.ctx hfit hp.scratch.wr hp.scratch.stk
  have Ts : BTblAt s (arg s₀ 3) (s₀.syms bSym) := hp.tbl.of_frame hs.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hp.tbl.sc, hp.tblStk]) (by rw [hs.rd, hs.wr])
  refine WP.mono (bTable_ok hc Ts (by rw [hy]) (by rw [callStk, hs.esp]; exact hp.tblStk))
    fun b ⟨kb, fb, tb, _, _⟩ => ?_
  have fb' : Frame [sub (arg s₀ 3) 3072 1920, sub (arg s₀ 3) 3072 1920, callStk s] s.mem b.mem :=
    fb.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp
  exact ⟨hs.frame2s hfit kb fb' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    tablePoint_frame2s hc fb' (by decide) (by decide) (by decide) (Or.inr (by decide)) (Or.inr (by decide)),
    tablePoint_frame2s hc fb' (by decide) (by decide) (by decide) (Or.inr (by decide)) (Or.inr (by decide)), tb⟩

theorem verifyEquationPoints_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s)
    (hy : s.syms = s₀.syms) {Aa Ra : EPoint dZ} (hA : Rep (tablePoint s.mem (arg s₀ 3) 7680) Aa)
    (hR : Rep (tablePoint s.mem (arg s₀ 3) 7808) Ra) :
    WP isa verifyEquationPoints s fun t => Saved s₀ (arg s₀ 3) t ∧ t.gpr .eax = signWord
      (Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul (verificationScalar s₀) Spec.Ed25519.basePoint)
        (Spec.Ed25519.pointAdd (tablePoint s.mem (arg s₀ 3) 7808)
          (Spec.Ed25519.pointMul (verificationChallenge s₀) (tablePoint s.mem (arg s₀ 3) 7680)))) := by
  refine WP.seq (WP.mono (bTable_stage hp hs hy) fun b ⟨sb, ab, rb, tb⟩ => ?_)
  refine WP.seq (WP.mono (windowMultiply_ok hp sb hA ab rb tb) fun u ⟨wu, ru⟩ => ?_)
  refine WP.seq (WP.mono (negR_ok wu.ctx) fun v ⟨kv, qv, pv⟩ => ?_)
  have sv := wu.saved.ikeep hp.scratch.fit kv
  refine WP.mono (pointEqual_ok (sv.ctx hp.scratch.fit hp.scratch.wr hp.scratch.stk)) fun t ⟨kt, et⟩ =>
    ⟨sv.ikeep hp.scratch.fit kt, ?_⟩
  rw [et, pv, qv, wu.r]
  congr 1
  exact window_equation hA hR ru.proj (hR.neg.proj)

end VG.Proof.Ed25519.X86
