module

import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.Arm.PointEqual
public import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTPublic
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTLit
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTFrom
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ed25519.Arm.PointFromScalar
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.Arm.PointEqual
meta import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTPublic
meta import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTLit
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTFrom
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Ed25519.Arm.PointFromScalar
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.TaintMono
meta import VerifiedGarbage.Proof.Framework.Arm.TaintMono
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport

/-! Merged from `Proof.Ed25519.Arm.PointEqualCT`. -/

@[expose] public section

section
/-! Point comparison branches depend only on the public projective points. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

/-- The comparison's operands: the left one any representative of `P`. -/
def EqualCTPre (base : BitVec 32) (P : Edwards.EPoint dZ) (q : Spec.Ed25519.Point) (s : State) : Prop :=
  Ctx base s ∧ AllLim s.mem base ∧ Rep (point (env s.mem base) 0 1 2 3) P ∧ point (env s.mem base) 4 5 6 7 = q

theorem equalFirstCT_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa (.seq (fieldCode pointEqualOps) (fieldEqual 8 9)) s fun t =>
      Keep base s t ∧ AllLim t.mem base ∧
      t.z = decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2) ∧
      env t.mem base 10 = env s.mem base 1 * env s.mem base 6 ∧
      env t.mem base 11 = env s.mem base 5 * env s.mem base 2 := by
  refine WP.seq (WP.mono (fieldCode_ok pointEqualOps hc hl) fun a ⟨ka, la, va⟩ => ?_)
  refine WP.mono (fieldEqual_ok (ka.ctx hc) la 8 9) fun t ⟨kt, lt, te, tz⟩ => ?_
  refine ⟨ka.trans kt, lt, ?_, ?_, ?_⟩
  · rw [tz, va, (equalOps_eval _).1, (equalOps_eval _).2.1]
  · rw [te 10 (by decide), va, (equalOps_eval _).2.2.1]
  · rw [te 11 (by decide), va, (equalOps_eval _).2.2.2]

theorem equalSecond_ct (base : BitVec 32) (e : Bool) :
    CT (fun s t => (Ctx base s ∧ AllLim s.mem base ∧ decide (env s.mem base 10 = env s.mem base 11) = e) ∧
      (Ctx base t ∧ AllLim t.mem base ∧ decide (env t.mem base 10 = env t.mem base 11) = e))
      (.seq (fieldEqual 10 11) (.ite .eq (.block [.mov .r9 (.imm 1)]) recoverInvalid)) (fun _ _ => True) := by
  have ht : CT (fun s t => (Ctx base s ∧ AllLim s.mem base ∧ decide (env s.mem base 10 = env s.mem base 11) = e) ∧
      (Ctx base t ∧ AllLim t.mem base ∧ decide (env t.mem base 10 = env t.mem base 11) = e))
      (fieldEqual 10 11) (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by native_taint_decide)
    exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : Ctx base s ∧ AllLim s.mem base ∧ decide (env s.mem base 10 = env s.mem base 11) = e) :
      WP isa (fieldEqual 10 11) s fun t => t.z = e :=
    WP.mono (fieldEqual_ok h.1 h.2.1 10 11) fun t ⟨_, _, _, hz⟩ => hz.trans h.2.2
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    exact congrArg some (h.2.1.trans h.2.2.symm)
  · exact (returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem pointEqual_ct (base : BitVec 32) (P : Edwards.EPoint dZ) (q : Spec.Ed25519.Point) :
    CT (fun s t => EqualCTPre base P q s ∧ EqualCTPre base P q t)
      Impl.Ed25519.Arm.pointEqual (fun _ _ => True) := by
  have ht : CT (fun s t => EqualCTPre base P q s ∧ EqualCTPre base P q t)
      (.seq (fieldCode pointEqualOps) (fieldEqual 8 9)) (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by native_taint_decide)
    exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : EqualCTPre base P q s) :
      WP isa (.seq (fieldCode pointEqualOps) (fieldEqual 8 9)) s fun t =>
        Ctx base t ∧ AllLim t.mem base ∧ t.z = decide (P.x * toZ q.Z = toZ q.X) ∧
          decide (env t.mem base 10 = env t.mem base 11) = decide (P.y * toZ q.Z = toZ q.Y) := by
    refine WP.mono (equalFirstCT_ok h.1 h.2.1) fun t ⟨kt, lt, tz, tu, tv⟩ => ?_
    obtain hq := h.2.2.2
    refine ⟨kt.ctx h.1, lt, ?_, ?_⟩
    · rw [tz, ← hq]
      exact decide_eq_decide.mpr (rep_cross_x (q := point (env s.mem base) 4 5 6 7) h.2.2.1)
    · rw [tu, tv, ← hq]
      exact decide_eq_decide.mpr (rep_cross_y (q := point (env s.mem base) 4 5 6 7) h.2.2.1)
  rw [Impl.Ed25519.Arm.pointEqual]
  apply ctSeqAssoc
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    exact congrArg some (h.2.1.2.2.1.trans h.2.2.2.2.1.symm)
  · exact (equalSecond_ct base (decide (P.y * toZ q.Z = toZ q.Y))).mono
      (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.1, h.1.2.1.2.2.2⟩,
        ⟨h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyCTMul`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyCTLhs`. -/
section
/-! Both scalar pointer reload and [S]B have a public trace. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyLoadScalar_ct (T b pk sig challenge : BitVec 32) :
    CT (fun s t => (VerifyContext b pk sig challenge s ∧ AllLim s.mem b ∧ VerifyTbl b T s) ∧
      (VerifyContext b pk sig challenge t ∧ AllLim t.mem b ∧ VerifyTbl b T t))
      (.block (loadHeader 8164 ++ ([.dp .add .r12 .r12 (.imm 32)] : List Instr)))
      (fun s t => CombCTPre b (sig + 32) T s ∧ CombCTPre b (sig + 32) T t) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by native_taint_decide)
    intro s t h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1.ctx.r0.trans h.2.1.ctx.r0.symm
  · intro s ⟨hc, hl, ht⟩
    rw [WP.block_append_iff]
    refine WP.mono_syms (loadHeader_ok hc.ctx 8164 (by decide)) fun u ⟨ur, um, up⟩ syu => ?_
    refine WP.mono_syms (addInput32_ok u) fun t ⟨tr, tm, tp⟩ syt => ?_
    have kt : VerifyKeep b s t := (VerifyKeep.of_rest ur (by decide) um).trans
      (VerifyKeep.of_rest tr (by decide) tm)
    have hi := (hc.keep kt).sigInput.suffix32
    have tt := ht.keep kt (syt.trans syu)
    exact ⟨⟨kt.ctx hc.ctx, by rw [tp, up, hc.sigHeader], hi.fit, hi.readable, hi.separate, tt.tbl, tt.sym,
      tt.apart⟩, by rw [tm, um]; exact hl⟩

theorem verifyLhs_ct (T b pk sig challenge : BitVec 32) :
    CT (fun s t => (VerifyContext b pk sig challenge s ∧ AllLim s.mem b ∧ VerifyTbl b T s) ∧
      (VerifyContext b pk sig challenge t ∧ AllLim t.mem b ∧ VerifyTbl b T t)) verifyLhs (fun _ _ => True) := by
  refine RelCT.seq (verifyLoadScalar_ct T b pk sig challenge)
    (RelCT.seq (combMultiply_ct b (sig + 32) T) ?_)
  apply ctRegs [.r0] _ (by native_taint_decide)
  intro s t h r hr
  rw [List.mem_singleton] at hr
  subst r
  exact h.1.r0.trans h.2.r0.symm

end VG.Proof.Ed25519.Arm
end

/-! Verification multiplies A by the first 256 bits of the public challenge. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def verifyRhsMul : Prog isa :=
  .seq (.block (pointTableRead 7776 ++ loadHeader 8168)) (pointFromScalar 16)

theorem verifyLoadChallenge_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => (VerifyContext b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyContext b pk sig challenge t ∧ AllLim t.mem b))
      (.block (pointTableRead 7776 ++ loadHeader 8168))
      (fun s t => FromCTPre b challenge 16 s ∧ FromCTPre b challenge 16 t) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by native_taint_decide)
    intro s t h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1.ctx.r0.trans h.2.1.ctx.r0.symm
  · intro s ⟨hc, hl⟩
    rw [WP.block_append_iff]
    refine WP.mono (pointTableRead_ok hc.ctx hl 7776 (by decide) (by decide)) fun u ⟨uk, ul, _, _⟩ => ?_
    refine WP.mono (loadHeader_ok (uk.ctx hc.ctx) 8168 (by decide)) fun t ⟨tr, tm, tp⟩ => ?_
    have ku := VerifyKeep.of_acc uk
    have kt := ku.trans (VerifyKeep.of_rest tr (by decide) tm)
    have hi := (hc.keep kt).challengeInput.prefix (n := 32) (by decide)
    exact ⟨kt.ctx hc.ctx, tm ▸ ul, tp.trans (hc.keep ku).challengeHeader, hi.fit, hi.readable, hi.separate⟩

theorem verifyRhsMul_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => (VerifyContext b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyContext b pk sig challenge t ∧ AllLim t.mem b)) verifyRhsMul (fun _ _ => True) :=
  RelCT.seq (verifyLoadChallenge_ct b pk sig challenge) (pointFromScalar_ct b challenge 16 (.inl rfl))

theorem verifyRhsMul_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyRhsMul s fun t => PointKeep b s t ∧ AllLim t.mem b ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      point (env t.mem b) 0 1 2 3 = Spec.Ed25519.pointMul
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64)) (tablePoint s.mem b 7776) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointTableRead_ok hc.ctx hl 7776 (by decide) (by decide)) fun a ⟨ak, al, ap, _⟩ => ?_
  refine WP.mono (loadHeader_ok (ak.ctx hc.ctx) 8168 (by decide)) fun c ⟨cr, cm, cp⟩ => ?_
  have kc := ak.trans (AccKeep.of_rest cr (by decide) cm)
  have cpk := PointKeep.of_mul (MulKeep.of_powers (PowersKeep.of_acc kc))
  have cc := hc.keep (VerifyKeep.of_acc kc)
  have cp' : c.gpr .r12 = challenge := cp.trans (hc.keep (VerifyKeep.of_acc ak)).challengeHeader
  have capp : point (env c.mem b) 0 1 2 3 = tablePoint s.mem b 7776 :=
    (congrArg (fun m => point (env m b) 0 1 2 3) cm).trans ap
  have ci := cc.challengeInput.prefix (n := 32) (by decide)
  refine WP.mono (pointFromScalar_ok cc.ctx (cm ▸ al) cp' 16 (by decide) (by decide)
    ci.fit ci.readable ci.separate) fun t ⟨tk, tl, td, tp⟩ => ?_
  refine ⟨cpk.trans tk, tl, td, ?_⟩
  rw [show 2 * 16 = 32 from rfl, decodeLE_low cc.challengeTop,
    hc.challengeInput.bytes (VerifyKeep.of_acc kc), capp] at tp
  exact tp

end VG.Proof.Ed25519.Arm
end

/-! Verification branches only on points determined by the public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def RhsCTPre (m : Mem) (T b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) (lhs : Edwards.EPoint dZ)
    (s : State) : Prop :=
  VerifyPublic m T b pk sig challenge s ∧ AllLim s.mem b ∧ tablePoint s.mem b 7776 = a ∧
    tablePoint s.mem b 7904 = r ∧ Rep (tablePoint s.mem b 8032) lhs

def CombineCTPre (b : BitVec 32) (ka r : Spec.Ed25519.Point) (lhs : Edwards.EPoint dZ) (s : State) : Prop :=
  Ctx b s ∧ AllLim s.mem b ∧ env s.mem b 16 = Spec.Ed25519.d ∧
    point (env s.mem b) 0 1 2 3 = ka ∧ tablePoint s.mem b 7904 = r ∧ Rep (tablePoint s.mem b 8032) lhs

theorem verifyMul_public_ct (m : Mem) (T b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point)
    (lhs : Edwards.EPoint dZ) :
    CT (fun s t => RhsCTPre m T b pk sig challenge a r lhs s ∧ RhsCTPre m T b pk sig challenge a r lhs t)
      verifyRhsMul (fun s t =>
        CombineCTPre b (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr challenge) 64)) a) r lhs s ∧
        CombineCTPre b (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr challenge) 64)) a) r lhs t) := by
  apply ctBoth
  · exact (verifyRhsMul_ct b pk sig challenge).mono (fun _ _ h =>
      ⟨⟨h.1.1.ctx, h.1.2.1⟩, ⟨h.2.1.ctx, h.2.2.1⟩⟩) (fun _ _ h => h)
  · intro s ⟨hp, hl, ha, hr, hh⟩
    refine WP.mono (verifyRhsMul_ok hp.ctx hl) fun t ⟨tk, tl, td, tp⟩ => ?_
    refine ⟨tk.ctx hp.ctx.ctx, tl, td, ?_, (tk.table (by decide) (by decide)).trans hr,
      by rw [tk.table (by decide) (by decide)]; exact hh⟩
    exact tp.trans (congrArg₂ Spec.Ed25519.pointMul (congrArg Spec.Ed25519.decodeLE hp.challengeBytes) ha)

theorem verifyCombine_ct (b : BitVec 32) (ka r : Spec.Ed25519.Point) (lhs : Edwards.EPoint dZ) :
    CT (fun s t => CombineCTPre b ka r lhs s ∧ CombineCTPre b ka r lhs t)
      verifyCombine (fun s t => EqualCTPre b lhs (Spec.Ed25519.pointAdd r ka) s ∧
        EqualCTPre b lhs (Spec.Ed25519.pointAdd r ka) t) := by
  apply ctBoth
  · apply ctRegsS [.r0] _ (by taint_decide_sum [addSum])
    intro s t h reg hr
    rw [List.mem_singleton] at hr
    subst reg
    exact h.1.1.r0.trans h.2.1.r0.symm
  · intro s ⟨hc, hl, hd, hp, hr, hh⟩
    refine WP.mono (verifyCombine_ok hc hl hd) fun t ⟨tk, tl, tp, tq⟩ => ?_
    exact ⟨tk.ctx hc, tl, by rw [tp]; exact hh, tq.trans (congrArg₂ Spec.Ed25519.pointAdd hr hp)⟩

theorem verifyRhs_ct (m : Mem) (T b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point)
    (lhs : Edwards.EPoint dZ) :
    CT (fun s t => RhsCTPre m T b pk sig challenge a r lhs s ∧ RhsCTPre m T b pk sig challenge a r lhs t)
      verifyRhs (fun _ _ => True) := by
  apply ctSeqAssoc
  exact RelCT.seq (verifyMul_public_ct m T b pk sig challenge a r lhs)
    (RelCT.seq (verifyCombine_ct b _ r lhs) (pointEqual_ct b lhs _))

end VG.Proof.Ed25519.Arm
