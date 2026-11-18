module

public import VerifiedGarbage.Proof.Ed25519.X86.WindowLoop
public import VerifiedGarbage.Impl.Ed25519.X86.Verify
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
import VerifiedGarbage.Proof.Ed25519.Window
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ed25519.X86.PowerEnv
public import VerifiedGarbage.Proof.Ed25519.X86.RecoverParity
import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd

/-! ### `Ed25519.X86.PointEqual`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

private theorem eqOps_eval (e : Env) :
    evalOps pointEqualOps e 8 = e 0 * e 6 ∧ evalOps pointEqualOps e 9 = e 4 * e 2 ∧
    evalOps pointEqualOps e 10 = e 1 * e 6 ∧ evalOps pointEqualOps e 11 = e 5 * e 2 := ⟨rfl, rfl, rfl, rfl⟩

/-- One pass of `equalStep`, with `esi = n` for `n` of 1 or 2. -/
theorem equalStep_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 2)
    (hn : s.gpr .esi = BitVec.ofNat 32 n) :
    WP isa equalStep s fun t => IKeep x s t ∧
      (env s.mem x 8 = env s.mem x 9 → t.gpr .eax = 1 ∧ t.gpr .esi = BitVec.ofNat 32 (n - 1) ∧
        isa.eval .ne t = some (decide (n - 1 ≠ 0)) ∧
        env t.mem x 8 = env s.mem x 10 ∧ env t.mem x 9 = env s.mem x 11) ∧
      (env s.mem x 8 ≠ env s.mem x 9 → t.gpr .eax = 0 ∧ isa.eval .ne t = some false) := by
  refine WP.seq (WP.mono (fieldEqual_ok hc 8 9) fun a ⟨ka, ea, za⟩ => ?_)
  apply WP.ite (decide (env s.mem x 8 = env s.mem x 9)) za
  · intro heq
    rw [WP.block_append_iff]
    refine WP.mono (fieldCode_ok [.copy 8 10, .copy 9 11] (ka.ctx hc)) fun b ⟨kb, eb⟩ => ?_
    refine Wp.wp_movi fun c u₁ => Wp.wp_subi fun t u₂ _ z₂ => WP.block_nil ?_
    have kab := IKeep.of_field (ka.trans kb)
    have esi_b : b.gpr .esi = BitVec.ofNat 32 n := by rw [kb.keep.esi, ka.keep.esi, hn]
    refine ⟨kab.trans ((IKeep.of_field (FieldKeep.of_mem (updKeep u₁) u₁.mem)).trans (IKeep.of_counter u₂)),
      fun _ => ⟨by rw [u₂.other _ (by decide), u₁.gpr], ?_, ?_, ?_, ?_⟩,
      fun hne => absurd (of_decide_eq_true heq) hne⟩
    · rw [u₂.gpr, u₁.other _ (by decide), esi_b, Wp.ofNat_pred h1]
    · show t.zf.map (!·) = _
      rw [z₂, u₁.other _ (by decide), esi_b, Wp.ofNat_pred h1, Wp.ofNat_beq_zero (by omega_using [h2])]
      cases h : decide (n - 1 = 0) <;> simp_all
    · rw [u₂.mem, u₁.mem, eb]; exact ea 10 (by decide)
    · rw [u₂.mem, u₁.mem, eb]; exact ea 11 (by decide)
  · intro hne
    refine Wp.wp_movi fun c u₁ => Wp.wp_movi fun d u₂ => Wp.wp_test fun t ft zt => WP.block_nil ?_
    refine ⟨(IKeep.of_field ka).trans ((IKeep.of_field (FieldKeep.of_mem (updKeep u₁) u₁.mem)).trans
        ((IKeep.of_counter u₂).trans (IKeep.of_field (FieldKeep.of_mem ⟨by rw [ft.gpr], by rw [ft.gpr],
          by rw [ft.gpr], ft.rd, ft.wr⟩ ft.mem)))),
      fun heq => absurd heq (of_decide_eq_false hne), fun _ => ⟨?_, ?_⟩⟩
    · rw [ft.gpr, u₂.other _ (by decide), u₁.gpr]
    · show t.zf.map (!·) = _
      rw [zt, u₂.gpr]; rfl

theorem pointEqual_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa pointEqual s fun t => IKeep x s t ∧ t.gpr .eax = signWord
      (Spec.Ed25519.pointEqual (point (env s.mem x) 0 1 2 3) (point (env s.mem x) 4 5 6 7)) := by
  have ev := eqOps_eval (env s.mem x)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok pointEqualOps hc) fun a ⟨ka, ea⟩ => Wp.wp_movi fun b u => WP.block_nil ?_
  have kb := (IKeep.of_field ka).trans (IKeep.of_counter u)
  have cb : Ctx x b := (IKeep.of_counter u).ctx (ka.ctx hc)
  have e8 : env b.mem x 8 = env s.mem x 0 * env s.mem x 6 := by rw [u.mem, ea, ev.1]
  have e9 : env b.mem x 9 = env s.mem x 4 * env s.mem x 2 := by rw [u.mem, ea, ev.2.1]
  have e10 : env b.mem x 10 = env s.mem x 1 * env s.mem x 6 := by rw [u.mem, ea, ev.2.2.1]
  have e11 : env b.mem x 11 = env s.mem x 5 * env s.mem x 2 := by rw [u.mem, ea, ev.2.2.2]
  -- Before the first pass (`n = 2`) and the second (`n = 1`).
  let I : Nat → State → Prop := fun n t => IKeep x s t ∧ Ctx x t ∧ t.gpr .esi = BitVec.ofNat 32 n ∧
    ((n = 2 ∧ env t.mem x 8 = env s.mem x 0 * env s.mem x 6 ∧ env t.mem x 9 = env s.mem x 4 * env s.mem x 2 ∧
        env t.mem x 10 = env s.mem x 1 * env s.mem x 6 ∧ env t.mem x 11 = env s.mem x 5 * env s.mem x 2) ∨
      (n = 1 ∧ env s.mem x 0 * env s.mem x 6 = env s.mem x 4 * env s.mem x 2 ∧
        env t.mem x 8 = env s.mem x 1 * env s.mem x 6 ∧ env t.mem x 9 = env s.mem x 5 * env s.mem x 2))
  refine WP.loop (M := isa) I (fun n t ⟨kt, ct, nt, ht⟩ => ?_) 2 b
    ⟨kb, cb, u.gpr, .inl ⟨rfl, e8, e9, e10, e11⟩⟩
  have hn : 1 ≤ n ∧ n ≤ 2 := by rcases ht with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  refine WP.mono (equalStep_ok ct hn.1 hn.2 nt) fun t ⟨k, yes, no⟩ => ?_
  have kst := kt.trans k
  simp only [Spec.Ed25519.pointEqual, point]
  rcases ht with ⟨rfl, h8, h9, h10, h11⟩ | ⟨rfl, hx, h8, h9⟩
  · by_cases e : env s.mem x 0 * env s.mem x 6 = env s.mem x 4 * env s.mem x 2
    · obtain ⟨_, ri, rz, r8, r9⟩ := yes (by rw [h8, h9, e])
      exact .inr ⟨rz.trans rfl, 1, by decide, kst, k.ctx ct, ri, .inr ⟨rfl, e, by rw [r8, h10],
        by rw [r9, h11]⟩⟩
    · obtain ⟨ra, rz⟩ := no (by rw [h8, h9]; exact e)
      refine .inl ⟨rz, kst, ?_⟩
      rw [ra, beq_eq_false_iff_ne.mpr e, Bool.false_and]; rfl
  · by_cases e : env s.mem x 1 * env s.mem x 6 = env s.mem x 5 * env s.mem x 2
    · obtain ⟨ra, _, rz, _, _⟩ := yes (by rw [h8, h9, e])
      refine .inl ⟨rz.trans rfl, kst, ?_⟩
      rw [ra]; simp only [hx, e, beq_self_eq_true, Bool.and_self]; rfl
    · obtain ⟨ra, rz⟩ := no (by rw [h8, h9]; exact e)
      refine .inl ⟨rz, kst, ?_⟩
      rw [ra, beq_eq_false_iff_ne.mpr e, Bool.and_false]; rfl

end VG.Proof.Ed25519.X86

end

end

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
