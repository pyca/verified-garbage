module

import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.Arm.PointDecode
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.Arm.InitFields
import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.Arm.PointDecode
meta import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTLit
meta import VerifiedGarbage.Proof.Ed25519.Arm.InitFields
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
public import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTPublic
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTPublic
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit
import VerifiedGarbage.Proof.Framework.Arm.TaintMono
meta import VerifiedGarbage.Proof.Framework.Arm.TaintMono
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
public import VerifiedGarbage.Proof.Ed25519.Arm.FieldProg
public import VerifiedGarbage.Proof.Ed25519.Recover
import VerifiedGarbage.Proof.Ed25519.Arm.PointEncode
import VerifiedGarbage.Proof.Ed25519.Arm.DecodeCTLit
public import VerifiedGarbage.Impl.Ed25519.Arm.RecoverSign
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.Arm.FieldProg
meta import VerifiedGarbage.Proof.Ed25519.Recover
meta import VerifiedGarbage.Proof.Ed25519.Arm.PointEncode
meta import VerifiedGarbage.Proof.Ed25519.Arm.DecodeCTLit
meta import VerifiedGarbage.Impl.Ed25519.Arm.RecoverSign
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Ed25519.Arm.RecoverCTRoot`, which only this module used -/

section

/-! Merged from `Proof.Ed25519.Arm.RecoverCTSign`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.Arm.RecoverCTAdjust`. -/
section
/-! The sign-adjustment branch depends only on the public coordinate and sign. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {umaal : Bool}

def SignCTPre (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) (s : State) : Prop :=
  Ctx base s ∧ AllLim s.mem base ∧
    s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat ∧ env s.mem base 0 = x

theorem parityBlockCT_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa (.block (freeze 0 ++ recoverParity)) s fun t =>
      Ctx base t ∧ t.z = (((env s.mem base 0).val % 2 == 1) == b) := by
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hc hl 0) fun a ⟨ak, _, _, af, av⟩ => ?_
  refine WP.mono (recoverParity_ok (ak.ctx hc) b af (ak.sign.trans hb)) fun t ⟨tr, _, tz⟩ => ?_
  exact ⟨(ak.ctx hc).of_rest tr (by decide), by rw [tz, av]⟩

theorem adjustTail_ct :
    CT (fun x y => x.gpr .r0 = y.gpr .r0 ∧ x.z = y.z)
      (.seq (.ite .eq (.block []) (fieldCode false [.const 5 0, .sub 0 5 0])) (recoverSuccess umaal)) (fun _ _ => True) := by
  refine RelCT.seq (R := fun (x y : State) => ∀ r ∈ ([.r0] : List Reg), x.gpr r = y.gpr r)
    (RelCT.ite (fun _ _ h => congrArg some h.2) ?_ ?_) ?_
  · apply ctRegsKeeping [.r0] [.r0] _ (by native_taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1
  · apply ctRegsKeeping [.r0] [.r0] _ (by native_taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1
  · cases umaal <;> [apply ctRegs [.r0] _ (by native_taint_decide); apply ctRegsU [.r0] _ (by taint_decide)]
    all_goals exact fun _ _ h => h

theorem recoverAdjustSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t) (recoverAdjustSign umaal) (fun _ _ => True) := by
  have ht : CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.block (freeze 0 ++ recoverParity)) (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by native_taint_decide)
    exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (freeze 0 ++ recoverParity)) s fun t =>
        Ctx base t ∧ t.z = ((x.val % 2 == 1) == b) := by
    refine WP.mono (parityBlockCT_ok h.1 h.2.1 b h.2.2.1) fun t ⟨hc, hz⟩ => ?_
    exact ⟨hc, by rw [hz, h.2.2.2]⟩
  have hp := (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono (fun _ _ h => h)
    (fun _ _ h => And.intro (h.2.1.1.r0.trans h.2.2.1.r0.symm) (h.2.1.2.trans h.2.2.2.symm))
  exact RelCT.seq hp adjustTail_ct

end VG.Proof.Ed25519.Arm
end

/-! The negative-zero rejection depends only on the public coordinate and sign. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {umaal : Bool}

theorem signTestThen_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.seq (.block signTest) (.ite .ne recoverInvalid (recoverAdjustSign umaal))) (fun _ _ => True) := by
  have ht : CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.block signTest) (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by native_taint_decide)
    exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block signTest) s fun t => SignCTPre base b x t ∧ t.z = !b := by
    refine WP.mono (signTest_ok h.1 b h.2.2.1) fun t ⟨tr, tm, tz⟩ => ?_
    exact ⟨⟨h.1.of_rest tr (by decide), tm ▸ h.2.1, tm ▸ h.2.2.1, tm ▸ h.2.2.2⟩, tz⟩
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    simp only [VG.Arm.eval, h.2.1.2, h.2.2.2]
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact (recoverAdjustSign_ct base b x).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

theorem recoverSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t) (recoverSign umaal) (fun _ _ => True) := by
  have ht : CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (fieldZero 0) (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by native_taint_decide)
    exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (fieldZero 0) s fun t => SignCTPre base b x t ∧ t.z = decide (x = 0) := by
    refine WP.mono (fieldZero_ok h.1 h.2.1 0) fun t ⟨tk, tl, te, tz⟩ => ?_
    refine ⟨⟨tk.ctx h.1, tl, tk.sign.trans h.2.2.1, ?_⟩, ?_⟩
    · rw [te]; exact h.2.2.2
    · rw [tz, h.2.2.2]
  rw [recoverSign]
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.2.1.2.trans h.2.2.2.symm)
  · exact (signTestThen_ct base b x).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact (recoverAdjustSign_ct base b x).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm
end

/-! Candidate validation branches only on the public encoded coordinate. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {umaal : Bool}

def RootCTState (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  SignCTPre base b (rootX y) s ∧ env s.mem base 11 = rootV y * rootX y * rootX y ∧
    env s.mem base 6 = rootU y ∧ env s.mem base 12 = 0 - rootU y

def rootCheckValue (y : Spec.X25519.Fe) (minus : Bool) : Bool :=
  decide (rootV y * rootX y * rootX y = if minus then 0 - rootU y else rootU y)

theorem rootCheck_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (minus : Bool) :
    CT (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (fieldEqual 11 (if minus then 12 else 6))
      (fun s t => (RootCTState base b y s ∧ s.z = rootCheckValue y minus) ∧
        (RootCTState base b y t ∧ t.z = rootCheckValue y minus)) := by
  apply ctBoth
  · cases minus
    · apply ctRegs [.r0] _ (by native_taint_decide)
      exact fun _ _ h => r0_agree h.1.1.1.r0 h.2.1.1.r0
    · apply ctRegs [.r0] _ (by native_taint_decide)
      exact fun _ _ h => r0_agree h.1.1.1.r0 h.2.1.1.r0
  · intro s h
    refine WP.mono (fieldEqual_ok h.1.1 h.1.2.1 11 (if minus then 12 else 6)) fun t ⟨kt, lt, te, tz⟩ => ?_
    refine ⟨⟨⟨kt.ctx h.1.1, lt, kt.sign.trans h.1.2.2.1,
      (te 0 (by decide)).trans h.1.2.2.2⟩, (te 11 (by decide)).trans h.2.1,
      (te 6 (by decide)).trans h.2.2.1, (te 12 (by decide)).trans h.2.2.2⟩, ?_⟩
    rw [tz, rootCheckValue, h.2.1]
    cases minus <;> simp only [Bool.false_eq_true, ite_false, ite_true, h.2.2.1, h.2.2.2]

theorem rootAdjustSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.seq (fieldCode umaal [.const 18 Spec.Ed25519.sqrtM1, .mulc 0 0 18]) (recoverSign umaal)) (fun _ _ => True) := by
  have hp : CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (fieldCode umaal [.const 18 Spec.Ed25519.sqrtM1, .mulc 0 0 18])
      (fun s t => SignCTPre base b (x * Spec.Ed25519.sqrtM1) s ∧ SignCTPre base b (x * Spec.Ed25519.sqrtM1) t) := by
    apply ctBoth
    · cases umaal <;> [apply ctRegs [.r0] _ (by native_taint_decide); apply ctRegsU [.r0] _ (by taint_decide)]
      all_goals exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
    · intro s h
      refine WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mulc 0 0 18] h.1 h.2.1)
        fun t ⟨kt, lt, te⟩ => ?_
      refine ⟨kt.ctx h.1, lt, kt.sign.trans h.2.2.1, ?_⟩
      rw [te]
      change env s.mem base 0 * Spec.Ed25519.sqrtM1 = _
      rw [h.2.2.2]
  exact RelCT.seq hp (recoverSign_ct base b (x * Spec.Ed25519.sqrtM1))

theorem recoverMinus_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) :
    CT (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.seq (fieldEqual 11 12) (.ite .eq
        (.seq (fieldCode umaal [.const 18 Spec.Ed25519.sqrtM1, .mulc 0 0 18]) (recoverSign umaal)) recoverInvalid)) (fun _ _ => True) := by
  refine RelCT.seq (rootCheck_ct base b y true) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.1.2.trans h.2.2.symm)
  · exact (rootAdjustSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem recoverChecks_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) :
    CT (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.seq (fieldEqual 11 6) (.ite .eq (recoverSign umaal)
        (.seq (fieldEqual 11 12) (.ite .eq
          (.seq (fieldCode umaal [.const 18 Spec.Ed25519.sqrtM1, .mulc 0 0 18]) (recoverSign umaal)) recoverInvalid)))) (fun _ _ => True) := by
  refine RelCT.seq (rootCheck_ct base b y false) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.1.2.trans h.2.2.symm)
  · exact (recoverSign_ct base b (rootX y)).mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact (recoverMinus_ct base b y).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)

def RecoverCTPre (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  Ctx base s ∧ AllLim s.mem base ∧
    s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat ∧ env s.mem base 1 = y

theorem recoverPoint_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) :
    CT (fun s t => RecoverCTPre base b y s ∧ RecoverCTPre base b y t) (recoverPoint umaal) (fun _ _ => True) := by
  have hp : CT (fun s t => RecoverCTPre base b y s ∧ RecoverCTPre base b y t)
      (recoverCandidate umaal) (fun s t => RootCTState base b y s ∧ RootCTState base b y t) := by
    apply ctBoth
    · cases umaal <;> [apply ctRegs [.r0] _ (by native_taint_decide); apply ctRegsU [.r0] _ (by taint_decide)]
      all_goals exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
    · intro s h
      refine WP.mono (recoverCandidate_ok h.1 h.2.1) fun t ⟨kt, lt, tx, _, _, tu, _, tv, tn⟩ => ?_
      refine ⟨⟨kt.ctx h.1, lt, kt.sign.trans h.2.2.1, ?_⟩, ?_, ?_, ?_⟩
      · rw [tx, h.2.2.2]
      · rw [tv, h.2.2.2]
      · rw [tu, h.2.2.2]
      · rw [tn, h.2.2.2]
  exact RelCT.seq hp (recoverChecks_ct base b y)

end VG.Proof.Ed25519.Arm

end

end

/-! ### `Ed25519.Arm.VerifyCTRhs`, which only this module used -/

section

/-! Merged from `Proof.Ed25519.Arm.PointEqualCT`. -/

@[expose] public section

section
/-! Point comparison branches depend only on the public projective points. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {umaal : Bool}

/-- The comparison's operands: the left one any representative of `P`. -/
def EqualCTPre (base : BitVec 32) (P : Edwards.EPoint dZ) (q : Spec.Ed25519.Point) (s : State) : Prop :=
  Ctx base s ∧ AllLim s.mem base ∧ Rep (point (env s.mem base) 0 1 2 3) P ∧ point (env s.mem base) 4 5 6 7 = q

theorem equalFirstCT_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa (.seq (fieldCode umaal pointEqualOps) (fieldEqual 8 9)) s fun t =>
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
      (Impl.Ed25519.Arm.pointEqual umaal) (fun _ _ => True) := by
  have ht : CT (fun s t => EqualCTPre base P q s ∧ EqualCTPre base P q t)
      (.seq (fieldCode umaal pointEqualOps) (fieldEqual 8 9)) (fun _ _ => True) := by
    cases umaal <;> [apply ctRegs [.r0] _ (by native_taint_decide); apply ctRegsU [.r0] _ (by taint_decide)]
    all_goals exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : EqualCTPre base P q s) :
      WP isa (.seq (fieldCode umaal pointEqualOps) (fieldEqual 8 9)) s fun t =>
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

variable {umaal : Bool}

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
      (VerifyContext b pk sig challenge t ∧ AllLim t.mem b ∧ VerifyTbl b T t)) (verifyLhs umaal) (fun _ _ => True) := by
  refine RelCT.seq (verifyLoadScalar_ct T b pk sig challenge)
    (RelCT.seq (combMultiply_ct b (sig + 32) T) ?_)
  apply ctRegs [.r0] _ (by native_taint_decide)
  intro s t h r hr
  rw [List.mem_singleton] at hr
  subst r
  exact h.1.r0.trans h.2.r0.symm

end VG.Proof.Ed25519.Arm
end

/-! Verification multiplies `A` by the first 256 bits of the public challenge, with a sliding window. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {umaal : Bool}

def verifyRhsMul (umaal : Bool) : Prog isa :=
  .seq (.block (pointTableRead 7776 ++ loadHeader 8168)) (publicMul umaal)

/-- What `publicMul` needs in each run: the same bytes of `k`, which are public, and the same `A`. -/
def PubMulPre (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) (s : State) : Prop :=
  Ctx b s ∧ AllLim s.mem b ∧ s.gpr .r12 = ptr ∧ VerifyInput b ptr 32 s ∧
    Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32 = ks ∧ point (env s.mem b) 0 1 2 3 = a

/-- `k`: its pointer at word 52, and its bytes. -/
def KAt (ks : List Byte) (b ptr : BitVec 32) (s : State) : Prop :=
  lw s.mem b 52 = ptr ∧ VerifyInput b ptr 32 s ∧ Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32 = ks

theorem KAt.keep {ks : List Byte} {b ptr : BitVec 32} {s t : State} (h : KAt ks b ptr s)
    (k : MulKeep b 1632 6144 s t) : KAt ks b ptr t :=
  have kv := VerifyKeep.of_point (PointKeep.of_mul k)
  ⟨(k.word (by decide) (by decide) 52 (.inr rfl)).trans h.1, h.2.1.keep kv, (h.2.1.bytes kv).trans h.2.2⟩

/-! ### The table -/

/-- A run before entry `m` of the table. -/
def TabRun (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) (m : Nat) (s : State) : Prop :=
  TabAt a b m s ∧ KAt ks b ptr s

theorem savePtr_ct (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) :
    CT (fun x y => PubMulPre ks a b ptr x ∧ PubMulPre ks a b ptr y) (.block [.str .r12 .r0 52])
      (fun x y => (Ctx b x ∧ AllLim x.mem b ∧ point (env x.mem b) 0 1 2 3 = a ∧ KAt ks b ptr x) ∧
        (Ctx b y ∧ AllLim y.mem b ∧ point (env y.mem b) 0 1 2 3 = a ∧ KAt ks b ptr y)) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by native_taint_decide)
    exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
  · intro s ⟨hc, hl, hp, hin, hb, ha⟩
    refine strLow_ok hc (d := 52) (by decide) .r12 fun u hu => WP.block_nil ?_
    obtain uf : Frame [⟨State.addr b + BitVec.ofNat 64 52, 4⟩] s.mem u.mem := by
      rw [hu.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    obtain uk : PointKeep b s u := PointKeep.of_small (hu.rest []) (by decide) uf (by decide) (by decide)
    refine ⟨uk.ctx hc, smallFrame_lim uf (by decide) hl, by rw [smallFrame_env uf (by decide)]; exact ha,
      by rw [hu.mem]; exact (Mem.readW_writeW_self32 _ _ _).trans hp, hin.keep (VerifyKeep.of_point uk),
      (hin.bytes (VerifyKeep.of_point uk)).trans hb⟩

theorem oddTableInit_ct (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) :
    CT (fun x y => (Ctx b x ∧ AllLim x.mem b ∧ point (env x.mem b) 0 1 2 3 = a ∧ KAt ks b ptr x) ∧
        (Ctx b y ∧ AllLim y.mem b ∧ point (env y.mem b) 0 1 2 3 = a ∧ KAt ks b ptr y)) (oddTableInit umaal)
      (fun x y => TabRun ks a b ptr 1 x ∧ TabRun ks a b ptr 1 y) := by
  apply ctBoth
  · cases umaal <;> [apply ctRegsS [.r0] _ (by taint_decide_sum [doubleSum]); apply ctRegsU [.r0] _ (by taint_decide)]
    all_goals exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
  · intro s ⟨hc, hl, ha, hk⟩
    refine WP.mono (oddTableInit_ok hc hl) fun t ⟨tk, tt⟩ => ?_
    rw [ha] at tt
    exact ⟨tt, hk.keep tk⟩

theorem oddTableStep_ct (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) {m : Nat} (h1 : 1 ≤ m)
    (h8 : m < 8) :
    CT (fun x y => TabRun ks a b ptr m x ∧ TabRun ks a b ptr m y) (oddTableStep umaal)
      (fun x y => (TabRun ks a b ptr (m + 1) x ∧ x.z = decide (m + 1 = 8)) ∧
        (TabRun ks a b ptr (m + 1) y ∧ y.z = decide (m + 1 = 8))) := by
  apply ctBoth
  · cases umaal <;>
      [apply ctRegsS [.r0, .r11] _ (by taint_decide_sum [addSum]); apply ctRegsU [.r0, .r11] _ (by taint_decide)]
    all_goals
      intro x y h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.1.ctx.r0.trans h.2.1.ctx.r0.symm
      · exact h.1.1.r11.trans h.2.1.r11.symm
  · intro s ⟨ht, hk⟩
    exact WP.mono (oddTableStep_ok ht h1 h8) fun t ⟨tk, tt, tz⟩ => ⟨⟨tt, hk.keep tk⟩, tz⟩

theorem oddTable_ct (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) :
    CT (fun x y => (Ctx b x ∧ AllLim x.mem b ∧ point (env x.mem b) 0 1 2 3 = a ∧ KAt ks b ptr x) ∧
        (Ctx b y ∧ AllLim y.mem b ∧ point (env y.mem b) 0 1 2 3 = a ∧ KAt ks b ptr y)) (oddTable umaal)
      (fun x y => TabRun ks a b ptr 8 x ∧ TabRun ks a b ptr 8 y) := by
  rw [oddTable]
  refine RelCT.seq (oddTableInit_ct ks a b ptr) ?_
  refine (RelCT.loop (M := isa) (Q := fun x y => TabRun ks a b ptr 8 x ∧ TabRun ks a b ptr 8 y)
    (fun n x y => 0 < n ∧ n ≤ 7 ∧ TabRun ks a b ptr (8 - n) x ∧ TabRun ks a b ptr (8 - n) y)
    (fun n => ?_) 7).mono (fun x y h => ⟨by decide, le_rfl, (show TabRun ks a b ptr (8 - 7) x from h.1),
      (show TabRun ks a b ptr (8 - 7) y from h.2)⟩) fun _ _ h => h
  by_cases hn : 0 < n ∧ n ≤ 7
  · refine (oddTableStep_ct ks a b ptr (m := 8 - n) (by omega_using [hn]) (by omega_using [hn])).mono
      (fun x y h => ⟨h.2.2.1, h.2.2.2⟩) fun u v h => ?_
    obtain ⟨⟨ru, zu⟩, ⟨rv, zv⟩⟩ := h
    refine ⟨by show some (!u.z) = some (!v.z); rw [zu, zv], fun hf => ?_, fun ht => ?_⟩
    · have e : some (!u.z) = some false := hf
      rw [zu] at e
      have e8 : 8 - n + 1 = 8 := by simpa using e
      rw [e8] at ru rv
      exact ⟨ru, rv⟩
    · have e : some (!u.z) = some true := ht
      rw [zu] at e
      have e8 : 8 - n + 1 ≠ 8 := by simpa using e
      refine ⟨n - 1, by omega_using [hn], by omega_using [hn, e8], by omega_using [hn], ?_, ?_⟩
      · rw [show 8 - (n - 1) = 8 - n + 1 by omega_using [hn]]; exact ru
      · rw [show 8 - (n - 1) = 8 - n + 1 by omega_using [hn]]; exact rv
  · exact RelCT.of_false fun x y h => hn ⟨h.1, h.2.1⟩

/-! ### The digits -/

/-- A run of the recoding after `i` bits. -/
def RecRun (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) (i : Nat) (s : State) : Prop :=
  RecAt (Spec.Ed25519.decodeLE ks) b ptr i s ∧ VerifyInput b ptr 32 s ∧
    Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32 = ks ∧ TabDone a b s.mem

/-- A run of the recoding before bit `t` of byte `j`, which is in `r10`. -/
def RecBitRun (ks : List Byte) (b ptr : BitVec 32) (j t : Nat) (s : State) : Prop :=
  RecAt (Spec.Ed25519.decodeLE ks) b ptr (8 * j + t) s ∧
    s.gpr .r10 = BitVec.ofNat 32 (Spec.Ed25519.decodeLE ks / 256 ^ j % 256 / 2 ^ t)

theorem recInit_ct (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) :
    CT (fun x y => TabRun ks a b ptr 8 x ∧ TabRun ks a b ptr 8 y) (.block recInit)
      (fun x y => RecRun ks a b ptr 0 x ∧ RecRun ks a b ptr 0 y) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by native_taint_decide)
    exact fun _ _ h => r0_agree h.1.1.ctx.r0 h.2.1.ctx.r0
  · intro s ⟨ht, hp, hin, hb⟩
    refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
      wp_mov (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_
    obtain r4 : Rest recClob s s₄ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans
      ((u₃.rest (by decide)).trans (u₄.rest (by decide))))
    obtain m4 : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    obtain k4 : VerifyKeep b s s₄ := VerifyKeep.of_rest r4 (by decide) m4
    refine ⟨⟨ht.ctx.of_rest r4 (by decide), by rw [m4]; exact hp,
        by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl,
        by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl,
        by rw [u₄.other _ (by decide), u₃.gpr]; rfl,
        by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ht.ctx.r0]
           exact (BitVec.add_zero b).symm,
        fun q hq => absurd hq (Nat.not_lt_zero _)⟩, hin.keep k4, (hin.bytes k4).trans hb,
      by rw [m4]; exact ht.lim, by rw [m4]; exact ht.d, fun j hj => by rw [m4]; exact ht.tab j hj⟩

/-- The byte's load: its address is `k`'s pointer and the public count of bits, and both runs
load the same byte. -/
theorem recLoad_ct (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) {j : Nat} (hj : j < 32) :
    CT (fun x y => RecRun ks a b ptr (8 * j) x ∧ RecRun ks a b ptr (8 * j) y) (.block recLoad)
      (fun x y => RecBitRun ks b ptr j 0 x ∧ RecBitRun ks b ptr j 0 y) := by
  have loadWP (s : State) (h : RecRun ks a b ptr (8 * j) s) :
      WP isa (.block recLoad) s fun t => Rest [.r2, .r3, .r10] s t ∧ t.mem = s.mem ∧
        t.gpr .r10 = BitVec.ofNat 32 (Spec.Ed25519.decodeLE ks / 256 ^ j % 256) :=
    recLoad_ok h.1 hj h.2.1 (congrArg Spec.Ed25519.decodeLE h.2.2.1)
  have head : CT (fun x y => RecRun ks a b ptr (8 * j) x ∧ RecRun ks a b ptr (8 * j) y) (.block recAddr)
      (fun x y => (x.gpr .r0 = b ∧ x.gpr .r3 = ptr + BitVec.ofNat 32 j) ∧
        (y.gpr .r0 = b ∧ y.gpr .r3 = ptr + BitVec.ofNat 32 j)) := by
    apply ctBoth
    · apply ctRegs [.r0, .r9] _ (by native_taint_decide)
      intro x y h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.1.ctx.r0.trans h.2.1.ctx.r0.symm
      · exact h.1.1.r9.trans h.2.1.r9.symm
    · intro s h
      exact WP.mono (recAddr_ok h.1 hj) fun _ ht => ht.1
  have tail : CT (fun x y => (x.gpr .r0 = b ∧ x.gpr .r3 = ptr + BitVec.ofNat 32 j) ∧
      (y.gpr .r0 = b ∧ y.gpr .r3 = ptr + BitVec.ofNat 32 j)) (.block [.ldrb .r10 .r3 0]) (fun _ _ => True) := by
    apply ctRegs [.r0, .r3] _ (by native_taint_decide)
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.trans h.2.2.symm
  have whole : CT (fun x y => RecRun ks a b ptr (8 * j) x ∧ RecRun ks a b ptr (8 * j) y) (.block recLoad)
      (fun _ _ => True) := ctBlockAppend head tail
  refine ctBoth whole fun s h => WP.mono (loadWP s h) fun t ⟨rt, mt, t10⟩ => ?_
  exact ⟨⟨h.1.ctx.of_rest rt (by decide), by rw [mt]; exact h.1.ptr, (rt.gpr _ (by decide)).trans h.1.r9,
    (rt.gpr _ (by decide)).trans h.1.r8, (rt.gpr _ (by decide)).trans h.1.r7, (rt.gpr _ (by decide)).trans h.1.r6,
    fun q hq => by rw [mt]; exact h.1.dig q hq⟩, by rw [t10, Nat.pow_zero, Nat.div_one]⟩

/-- The byte's eight bits: the branches are on the window's weight and on the byte, the same in
both runs, and the stores at the digits' addresses, which are those of the count of bits and of
the window. -/
theorem recBits_ct (ks : List Byte) (b ptr : BitVec 32) (j : Nat) :
    CT (fun x y => RecBitRun ks b ptr j 0 x ∧ RecBitRun ks b ptr j 0 y)
      (repeatThen 8 recBit (.block [.cmp .r9 (.imm 256)])) (fun _ _ => True) := by
  apply ctRegs [.r0, .r6, .r8, .r9, .r10] _ (by native_taint_decide)
  intro x y h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.1.1.ctx.r0.trans h.2.1.ctx.r0.symm
  · exact h.1.1.r6.trans h.2.1.r6.symm
  · exact h.1.1.r8.trans h.2.1.r8.symm
  · exact h.1.1.r9.trans h.2.1.r9.symm
  · exact h.1.2.trans h.2.2.symm

theorem recRun_step {ks : List Byte} {a : Spec.Ed25519.Point} {b ptr : BitVec 32} {j : Nat} {s : State}
    (h : RecRun ks a b ptr (8 * j) s) (hj : j < 32) :
    WP isa recByte s fun t => RecRun ks a b ptr (8 * (j + 1)) t ∧ t.z = decide (j + 1 = 32) :=
  WP.mono (recByte_ok h.1 hj h.2.1 (congrArg Spec.Ed25519.decodeLE h.2.2.1)) fun t ⟨tr, tf, ta, tz⟩ =>
    have kt : VerifyKeep b s t := VerifyKeep.of_small tr (by decide) tf (by decide) (by decide)
    ⟨⟨ta, h.2.1.keep kt, (h.2.1.bytes kt).trans h.2.2.1, h.2.2.2.digits tf⟩, tz⟩

theorem recByte_ct (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) {j : Nat} (hj : j < 32) :
    CT (fun x y => RecRun ks a b ptr (8 * j) x ∧ RecRun ks a b ptr (8 * j) y) recByte
      (fun x y => (RecRun ks a b ptr (8 * (j + 1)) x ∧ x.z = decide (j + 1 = 32)) ∧
        (RecRun ks a b ptr (8 * (j + 1)) y ∧ y.z = decide (j + 1 = 32))) :=
  ctBoth (RelCT.seq (recLoad_ct ks a b ptr hj) (recBits_ct ks b ptr j)) fun _ h => recRun_step h hj

theorem recode_ct (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) :
    CT (fun x y => TabRun ks a b ptr 8 x ∧ TabRun ks a b ptr 8 y) recode
      (fun x y => RecRun ks a b ptr 256 x ∧ RecRun ks a b ptr 256 y) := by
  rw [recode]
  refine RelCT.seq (recInit_ct ks a b ptr) ?_
  refine (RelCT.loop (M := isa) (Q := fun x y => RecRun ks a b ptr 256 x ∧ RecRun ks a b ptr 256 y)
    (fun n x y => 0 < n ∧ n ≤ 32 ∧ RecRun ks a b ptr (8 * (32 - n)) x ∧ RecRun ks a b ptr (8 * (32 - n)) y)
    (fun n => ?_) 32).mono (fun x y h => ⟨by decide, le_rfl, (show RecRun ks a b ptr (8 * (32 - 32)) x from h.1),
      (show RecRun ks a b ptr (8 * (32 - 32)) y from h.2)⟩) fun _ _ h => h
  by_cases hn : 0 < n ∧ n ≤ 32
  · refine (recByte_ct ks a b ptr (j := 32 - n) (by omega_using [hn])).mono
      (fun x y h => ⟨h.2.2.1, h.2.2.2⟩) fun u v h => ?_
    obtain ⟨⟨ru, zu⟩, ⟨rv, zv⟩⟩ := h
    refine ⟨by show some (!u.z) = some (!v.z); rw [zu, zv], fun hf => ?_, fun ht => ?_⟩
    · have e : some (!u.z) = some false := hf
      rw [zu] at e
      have e32 : 32 - n + 1 = 32 := by simpa using e
      rw [e32] at ru rv
      exact ⟨ru, rv⟩
    · have e : some (!u.z) = some true := ht
      rw [zu] at e
      have e32 : 32 - n + 1 ≠ 32 := by simpa using e
      refine ⟨n - 1, by omega_using [hn], by omega_using [hn, e32], by omega_using [hn], ?_, ?_⟩
      · rw [show 32 - (n - 1) = 32 - n + 1 by omega_using [hn]]; exact ru
      · rw [show 32 - (n - 1) = 32 - n + 1 by omega_using [hn]]; exact rv
  · exact RelCT.of_false fun x y h => hn ⟨h.1, h.2.1⟩

/-! ### The top digit -/

/-- What the sum needs in each run: the table and the digits. -/
def SumPre (a : Spec.Ed25519.Point) (D : Nat → Nat) (b : BitVec 32) (s : State) : Prop :=
  Ctx b s ∧ TabDone a b s.mem ∧
    ∀ q < 256, s.mem (State.addr b + BitVec.ofNat 64 (DIG + q)) = BitVec.ofNat 8 (D q)

/-- A run of the search for the top digit, at position `n`. -/
def TopRun (a : Spec.Ed25519.Point) (D : Nat → Nat) (b : BitVec 32) (n : Nat) (s : State) : Prop :=
  SumPre a D b s ∧ s.gpr .r11 = BitVec.ofNat 32 n

/-- A run with the top digit found: its position in `r11` and the digit in `r10`. -/
def TopDone (a : Spec.Ed25519.Point) (D : Nat → Nat) (b : BitVec 32) (s : State) : Prop :=
  TopRun a D b (Proof.Ed25519.Slide.topPos D 256) s ∧
    s.gpr .r10 = BitVec.ofNat 32 (D (Proof.Ed25519.Slide.topPos D 256))

theorem SumPre.keep {a : Spec.Ed25519.Point} {D : Nat → Nat} {b : BitVec 32} {s t : State}
    (h : SumPre a D b s) (hr : Rest [.r3, .r10, .r11] s t) (hm : t.mem = s.mem) : SumPre a D b t :=
  ⟨h.1.of_rest hr (by decide), by rw [hm]; exact h.2.1, fun q hq => by rw [hm]; exact h.2.2 q hq⟩

theorem topStep_ct (a : Spec.Ed25519.Point) (D : Nat → Nat) (b : BitVec 32) {p : Nat} (hp : p < 256)
    (hD : D p < 16) :
    CT (fun x y => TopRun a D b (p + 1) x ∧ TopRun a D b (p + 1) y) topStep
      (fun x y => (TopRun a D b p x ∧ x.z = topZ (D p) p) ∧ (TopRun a D b p y ∧ y.z = topZ (D p) p)) := by
  have head : CT (fun x y => TopRun a D b (p + 1) x ∧ TopRun a D b (p + 1) y)
      (.block (([.dp .sub .r11 .r11 (.imm 1)] : List Instr) ++ digitLoad))
      (fun x y => x.z = decide (D p = 0) ∧ y.z = decide (D p = 0)) := by
    apply ctBoth
    · apply ctRegs [.r0, .r11] _ (by native_taint_decide)
      intro x y h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.1.1.r0.trans h.2.1.1.r0.symm
      · exact h.1.2.trans h.2.2.symm
    · intro s h
      exact WP.mono (topHead_ok h.1.1 hp h.2 h.1.2.2 hD) fun _ ht => ht.2.2.2.2
  have tail : CT (fun x y => x.z = decide (D p = 0) ∧ y.z = decide (D p = 0))
      (.ite .eq (.block [.cmp .r11 (.imm 0)]) (.block [.cmp .r10 (.reg .r10)])) (fun _ _ => True) := by
    refine RelCT.ite ?_ ?_ ?_
    · intro x y h
      show some x.z = some y.z
      rw [h.1, h.2]
    · apply ctRegs [] _ (by native_taint_decide)
      intro _ _ _ r h
      exact (List.not_mem_nil h).elim
    · apply ctRegs [] _ (by native_taint_decide)
      intro _ _ _ r h
      exact (List.not_mem_nil h).elim
  exact ctBoth (RelCT.seq head tail) fun s h =>
    WP.mono (topStep_ok h.1.1 hp h.2 h.1.2.2 hD) fun t ⟨tr, tm, t11, _, tz⟩ => ⟨⟨h.1.keep tr tm, t11⟩, tz⟩

/-- The search stops at the same position in both runs: at the top digit, which is `k`'s. -/
theorem topDigit_ct (a : Spec.Ed25519.Point) (D : Nat → Nat) (b : BitVec 32) (hD : ∀ q, D q < 16) :
    CT (fun x y => SumPre a D b x ∧ SumPre a D b y) topDigit
      (fun x y => TopDone a D b x ∧ TopDone a D b y) := by
  have initCT : CT (fun x y => SumPre a D b x ∧ SumPre a D b y) (.block [.mov .r11 (.imm 256)])
      (fun x y => TopRun a D b 256 x ∧ TopRun a D b 256 y) := by
    apply ctBoth
    · apply ctRegs [] _ (by native_taint_decide)
      intro _ _ _ r h
      exact (List.not_mem_nil h).elim
    · intro s h
      exact wp_mov (op2_imm (by decide)) fun t ut => WP.block_nil
        ⟨h.keep (ut.rest (by decide)) ut.mem, ut.gpr⟩
  have loopCT : CT (fun x y => TopRun a D b 256 x ∧ TopRun a D b 256 y) (.loop topStep .ne)
      (fun _ _ => True) := by
    refine (RelCT.loop (M := isa) (Q := fun _ _ => True)
      (fun n x y => 0 < n ∧ n ≤ 256 ∧ TopRun a D b n x ∧ TopRun a D b n y)
      (fun n => ?_) 256).mono (fun x y h => ⟨by decide, le_rfl, h.1, h.2⟩) fun _ _ h => h
    by_cases hn : 0 < n ∧ n ≤ 256
    · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega_using [hn]⟩
      refine (topStep_ct a D b (by omega_using [hn]) (hD p)).mono (fun x y h => ⟨h.2.2.1, h.2.2.2⟩)
        fun u v h => ?_
      obtain ⟨⟨ru, zu⟩, ⟨rv, zv⟩⟩ := h
      refine ⟨by show some (!u.z) = some (!v.z); rw [zu, zv], fun _ => trivial, fun ht => ?_⟩
      have e : some (!u.z) = some true := ht
      rw [zu] at e
      have hp0 : p ≠ 0 := by
        rintro rfl
        have h1 : topZ (D 0) 0 = true := by rw [topZ]; split <;> rfl
        rw [h1] at e
        exact absurd e (by decide)
      exact ⟨p, by omega_arith, by omega_using [hp0], by omega_using [hn], ru, rv⟩
    · exact RelCT.of_false fun x y h => hn ⟨h.1, h.2.1⟩
  exact ctBoth (RelCT.seq initCT loopCT) fun s h =>
    WP.mono (topDigit_ok h.1 h.2.2 hD) fun t ⟨tr, tm, t11, t10⟩ => ⟨⟨h.keep tr tm, t11⟩, t10⟩

/-! ### The sum -/

/-- The sum's start: the branch is on the top digit, and the entry's address is the digit's. -/
theorem slideStart_ct (a : Spec.Ed25519.Point) (D : Nat → Nat) (b : BitVec 32)
    (hD : ∀ q, D q = 0 ∨ (D q % 2 = 1 ∧ D q < 16)) :
    CT (fun x y => TopDone a D b x ∧ TopDone a D b y) slideStart
      (fun x y => SlideAt a D b (Proof.Ed25519.Slide.topPos D 256) (Proof.Ed25519.Slide.topPos D 256) x ∧
        SlideAt a D b (Proof.Ed25519.Slide.topPos D 256) (Proof.Ed25519.Slide.topPos D 256) y) := by
  generalize hp : Proof.Ed25519.Slide.topPos D 256 = p₀
  obtain hlt : D p₀ < 16 := by rcases hD p₀ with e | e <;> omega_using [e]
  have head : CT (fun x y => TopDone a D b x ∧ TopDone a D b y) (.block [.cmp .r10 (.imm 0)])
      (fun x y => (x.gpr .r0 = b ∧ x.gpr .r10 = BitVec.ofNat 32 (D p₀) ∧ x.z = decide (D p₀ = 0)) ∧
        (y.gpr .r0 = b ∧ y.gpr .r10 = BitVec.ofNat 32 (D p₀) ∧ y.z = decide (D p₀ = 0))) := by
    apply ctBoth
    · apply ctRegs [] _ (by native_taint_decide)
      intro _ _ _ r h
      exact (List.not_mem_nil h).elim
    · intro s h
      rw [TopDone, hp] at h
      refine wp_cmp (op2_imm (by decide)) fun t ft zt => WP.block_nil
        ⟨by rw [ft.gpr]; exact h.1.1.1.r0, by rw [ft.gpr]; exact h.2, ?_⟩
      rw [zt, h.2]
      show (BitVec.ofNat 32 (D p₀) - 0#32 == 0#32) = _
      rw [BitVec.sub_zero]
      exact ofNat_beq_zero (by omega_using [hlt])
  have tail : CT (fun x y => (x.gpr .r0 = b ∧ x.gpr .r10 = BitVec.ofNat 32 (D p₀) ∧ x.z = decide (D p₀ = 0)) ∧
        (y.gpr .r0 = b ∧ y.gpr .r10 = BitVec.ofNat 32 (D p₀) ∧ y.z = decide (D p₀ = 0)))
      (.ite .ne (.block (digitAddr ++ pointFromTable)) (constPoint Spec.Ed25519.identity)) (fun _ _ => True) := by
    refine RelCT.ite ?_ ?_ ?_
    · intro x y h
      show some (!x.z) = some (!y.z)
      rw [h.1.2.2, h.2.2.2]
    · apply ctRegs [.r0, .r10] _ (by native_taint_decide)
      intro x y h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.1.1.trans h.1.2.1.symm
      · exact h.1.1.2.1.trans h.1.2.2.1.symm
    · apply ctRegs [.r0] _ (by native_taint_decide)
      exact fun _ _ h => r0_agree h.1.1.1 h.1.2.1
  refine ctBoth (RelCT.seq head tail) fun s h => ?_
  rw [TopDone, hp] at h
  exact WP.mono (slideStart_ok h.1.1.1 h.1.1.2.1.1 h.1.1.2.1.2.1 h.1.1.2.1.2.2 h.1.1.2.2 h.1.2 h.2 (hD p₀))
    fun _ ht => ht.2

/-- After the doubling of `X : Y : Z` for digit `p`: the digit, the same in both runs, and Z set
if it is zero. -/
def HeadRun (a : Spec.Ed25519.Point) (D : Nat → Nat) (b : BitVec 32) (p₀ p : Nat) (s : State) : Prop :=
  HeadAt a D b p₀ p s ∧ s.z = decide (D p = 0)

theorem slideHead_ct (a : Spec.Ed25519.Point) (D : Nat → Nat) (b : BitVec 32) (p₀ : Nat) {p : Nat}
    (hp : p < 256) (hD : D p < 16) :
    CT (fun x y => SlideAt a D b p₀ (p + 1) x ∧ SlideAt a D b p₀ (p + 1) y) (slideHead umaal)
      (fun x y => HeadRun a D b p₀ p x ∧ HeadRun a D b p₀ p y) := by
  apply ctBoth
  · cases umaal <;>
      [apply ctRegsS [.r0, .r11] _ (by taint_decide_sum [doubleSum]); apply ctRegsU [.r0, .r11] _ (by taint_decide)]
    all_goals
      intro x y h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.ctx.r0.trans h.2.ctx.r0.symm
      · exact h.1.r11.trans h.2.r11.symm
  · intro s h
    exact WP.mono (slideHead_ok h hp hD) fun t ⟨_, th, tz⟩ => ⟨th, tz⟩

/-- The sum's `T` and the addition of the digit's entry: its address is the digit's, the same in
both runs. -/
theorem addDigit_ct (a : Spec.Ed25519.Point) (D : Nat → Nat) (b : BitVec 32) (p₀ p : Nat) :
    CT (fun x y => HeadAt a D b p₀ p x ∧ HeadAt a D b p₀ p y)
      (.seq (fieldCode umaal doubleTOps) (addEntry umaal)) (fun _ _ => True) := by
  cases umaal <;>
    [apply ctRegsS [.r0, .r10] _ (by taint_decide_sum [addSum]); apply ctRegsU [.r0, .r10] _ (by taint_decide)]
  all_goals
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.ctx.r0.trans h.2.ctx.r0.symm
    · exact h.1.r10.trans h.2.r10.symm

/-- A digit that is zero: the sum's `T` after digit 0, a branch on the position. -/
theorem lastT_ct (a : Spec.Ed25519.Point) (D : Nat → Nat) (b : BitVec 32) (p₀ p : Nat) :
    CT (fun x y => HeadAt a D b p₀ p x ∧ HeadAt a D b p₀ p y)
      (.seq (.block [.cmp .r11 (.imm 0)]) (.ite .eq (fieldCode umaal doubleTOps) (.block [])))
      (fun _ _ => True) := by
  cases umaal <;>
    [apply ctRegs [.r0, .r11] _ (by native_taint_decide); apply ctRegsU [.r0, .r11] _ (by taint_decide)]
  all_goals
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.ctx.r0.trans h.2.ctx.r0.symm
    · exact h.1.r11.trans h.2.r11.symm

theorem slideStep_ct (a : Spec.Ed25519.Point) (D : Nat → Nat) (b : BitVec 32) {p₀ p : Nat} (hp₀ : p < p₀)
    (hp : p < 256) (hD : ∀ q, D q = 0 ∨ (D q % 2 = 1 ∧ D q < 16)) :
    CT (fun x y => SlideAt a D b p₀ (p + 1) x ∧ SlideAt a D b p₀ (p + 1) y) (slideStep umaal)
      (fun x y => (SlideAt a D b p₀ p x ∧ x.z = decide (p = 0)) ∧
        (SlideAt a D b p₀ p y ∧ y.z = decide (p = 0))) := by
  obtain hDp : D p < 16 := by rcases hD p with e | e <;> omega_using [e]
  have tail : CT (fun x y => HeadRun a D b p₀ p x ∧ HeadRun a D b p₀ p y)
      (.seq (slideTail umaal) (.block [.cmp .r11 (.imm 0)])) (fun _ _ => True) := by
    rw [slideTail]
    refine RelCT.seq (R := fun _ _ => True) (RelCT.ite ?_ ?_ ?_) ?_
    · intro x y h
      show some (!x.z) = some (!y.z)
      rw [h.1.2, h.2.2]
    · exact (addDigit_ct a D b p₀ p).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
    · exact (lastT_ct a D b p₀ p).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
    · apply ctRegs [] _ (by native_taint_decide)
      intro _ _ _ r h
      exact (List.not_mem_nil h).elim
  exact ctBoth (RelCT.seq (slideHead_ct a D b p₀ hp hDp) tail) fun s h =>
    WP.mono (slideStep_ok h hp₀ hp hD) fun t ⟨_, ta, tz⟩ => ⟨ta, tz⟩

theorem slideLoop_ct (a : Spec.Ed25519.Point) (D : Nat → Nat) (b : BitVec 32) {p₀ : Nat} (h256 : p₀ ≤ 256)
    (hD : ∀ q, D q = 0 ∨ (D q % 2 = 1 ∧ D q < 16)) :
    CT (fun x y => (0 < p₀ ∧ SlideAt a D b p₀ p₀ x) ∧ (0 < p₀ ∧ SlideAt a D b p₀ p₀ y))
      (.loop (slideStep umaal) .ne) (fun _ _ => True) := by
  refine (RelCT.loop (M := isa) (Q := fun _ _ => True)
    (fun n x y => 0 < n ∧ n ≤ p₀ ∧ SlideAt a D b p₀ n x ∧ SlideAt a D b p₀ n y)
    (fun n => ?_) p₀).mono (fun x y h => ⟨h.1.1, le_rfl, h.1.2, h.2.2⟩) fun _ _ h => h
  by_cases hn : 0 < n ∧ n ≤ p₀
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega_using [hn]⟩
    refine (slideStep_ct a D b (by omega_using [hn]) (by omega_using [hn, h256]) hD).mono
      (fun x y h => ⟨h.2.2.1, h.2.2.2⟩) fun u v h => ?_
    obtain ⟨⟨ru, zu⟩, ⟨rv, zv⟩⟩ := h
    refine ⟨by show some (!u.z) = some (!v.z); rw [zu, zv], fun _ => trivial, fun ht => ?_⟩
    have e : some (!u.z) = some true := ht
    rw [zu] at e
    have hp0 : p ≠ 0 := by simpa using e
    exact ⟨p, by omega_arith, by omega_using [hp0], by omega_using [hn], ru, rv⟩
  · exact RelCT.of_false fun x y h => hn ⟨h.1, h.2.1⟩

/-- The digits below the top one's: the branch is on its position, the same in both runs. -/
theorem slideRest_ct (a : Spec.Ed25519.Point) (D : Nat → Nat) (b : BitVec 32) {p₀ : Nat} (hp₀ : p₀ < 256)
    (hD : ∀ q, D q = 0 ∨ (D q % 2 = 1 ∧ D q < 16)) :
    CT (fun x y => SlideAt a D b p₀ p₀ x ∧ SlideAt a D b p₀ p₀ y) (slideRest umaal) (fun _ _ => True) := by
  have head : CT (fun x y => SlideAt a D b p₀ p₀ x ∧ SlideAt a D b p₀ p₀ y) (.block [.cmp .r11 (.imm 0)])
      (fun x y => (SlideAt a D b p₀ p₀ x ∧ x.z = decide (p₀ = 0)) ∧
        (SlideAt a D b p₀ p₀ y ∧ y.z = decide (p₀ = 0))) := by
    apply ctBoth
    · apply ctRegs [] _ (by native_taint_decide)
      intro _ _ _ r h
      exact (List.not_mem_nil h).elim
    · intro s h
      exact WP.mono (slideTest_ok h hp₀) fun _ ht => ht.2
  rw [slideRest]
  refine RelCT.seq head (RelCT.ite ?_ ?_ ?_)
  · intro x y h
    show some (!x.z) = some (!y.z)
    rw [h.1.2, h.2.2]
  · refine (slideLoop_ct a D b (p₀ := p₀) (by omega_using [hp₀]) hD).mono (fun x y h => ?_) fun _ _ h => h
    have e : some (!x.z) = some true := h.2
    rw [h.1.1.2] at e
    have hne : p₀ ≠ 0 := by simpa using e
    exact ⟨⟨by omega_using [hne], h.1.1.1⟩, ⟨by omega_using [hne], h.1.2.1⟩⟩
  · apply ctRegs [] _ (by native_taint_decide)
    intro _ _ _ r h
    exact (List.not_mem_nil h).elim

theorem publicMul_ct (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) :
    CT (fun x y => PubMulPre ks a b ptr x ∧ PubMulPre ks a b ptr y) (publicMul umaal) (fun _ _ => True) := by
  obtain hD := Proof.Ed25519.Slide.digits_odd 256 (Spec.Ed25519.decodeLE ks)
  have pre (s : State) (h : RecRun ks a b ptr 256 s) :
      SumPre a (Proof.Ed25519.Slide.digits 256 (Spec.Ed25519.decodeLE ks)) b s :=
    ⟨h.1.ctx, h.2.2.2, fun q hq => by rw [Proof.Ed25519.Slide.digits_eq]; exact h.1.dig q hq⟩
  rw [publicMul]
  exact RelCT.seq (savePtr_ct ks a b ptr) (RelCT.seq (oddTable_ct ks a b ptr) (RelCT.seq (recode_ct ks a b ptr)
    (RelCT.seq ((topDigit_ct a _ b fun q => by rcases hD q with e | e <;> omega_using [e]).mono
        (fun x y h => ⟨pre x h.1, pre y h.2⟩) fun _ _ h => h)
      (RelCT.seq (slideStart_ct a _ b hD)
        (slideRest_ct a _ b (Proof.Ed25519.Slide.topPos_lt _ (by decide)) hD)))))

theorem VerifyPublic.kBytes {m : Mem} {T b pk sig challenge : BitVec 32} {s : State}
    (h : VerifyPublic m T b pk sig challenge s) :
    Spec.Ed25519.bytesAt s.mem (State.addr challenge) 32 = Spec.Ed25519.bytesAt m (State.addr challenge) 32 := by
  obtain he := congrArg (List.take 32) h.challengeBytes
  simpa only [Proof.Ed25519.signatureBytes_take] using he

theorem verifyLoadChallenge_ct (m : Mem) (T b pk sig challenge : BitVec 32) (a : Spec.Ed25519.Point) :
    CT (fun s t => (VerifyPublic m T b pk sig challenge s ∧ AllLim s.mem b ∧ tablePoint s.mem b 7776 = a) ∧
      (VerifyPublic m T b pk sig challenge t ∧ AllLim t.mem b ∧ tablePoint t.mem b 7776 = a))
      (.block (pointTableRead 7776 ++ loadHeader 8168))
      (fun s t => PubMulPre (Spec.Ed25519.bytesAt m (State.addr challenge) 32) a b challenge s ∧
        PubMulPre (Spec.Ed25519.bytesAt m (State.addr challenge) 32) a b challenge t) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by native_taint_decide)
    intro s t h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1.ctx.ctx.r0.trans h.2.1.ctx.ctx.r0.symm
  · intro s ⟨hp, hl, ha⟩
    have hc := hp.ctx
    rw [WP.block_append_iff]
    refine WP.mono (pointTableRead_ok hc.ctx hl 7776 (by decide) (by decide)) fun u ⟨uk, ul, up, _⟩ => ?_
    refine WP.mono (loadHeader_ok (uk.ctx hc.ctx) 8168 (by decide)) fun t ⟨tr, tm, tp⟩ => ?_
    have ku := VerifyKeep.of_acc uk
    have kt := ku.trans (VerifyKeep.of_rest tr (by decide) tm)
    have hi := (hc.keep kt).challengeInput.prefix (n := 32) (by decide)
    exact ⟨kt.ctx hc.ctx, tm ▸ ul, tp.trans (hc.keep ku).challengeHeader, hi,
      ((hc.challengeInput.prefix (n := 32) (by decide)).bytes kt).trans hp.kBytes,
      (congrArg (fun m => point (env m b) 0 1 2 3) tm).trans (up.trans ha)⟩

theorem verifyRhsMul_ct (m : Mem) (T b pk sig challenge : BitVec 32) (a : Spec.Ed25519.Point) :
    CT (fun s t => (VerifyPublic m T b pk sig challenge s ∧ AllLim s.mem b ∧ tablePoint s.mem b 7776 = a) ∧
      (VerifyPublic m T b pk sig challenge t ∧ AllLim t.mem b ∧ tablePoint t.mem b 7776 = a))
      (verifyRhsMul umaal) (fun _ _ => True) :=
  RelCT.seq (verifyLoadChallenge_ct m T b pk sig challenge a) (publicMul_ct _ a b challenge)

theorem verifyRhsMul_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa (verifyRhsMul umaal) s fun t => PointKeep b s t ∧ AllLim t.mem b ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      point (env t.mem b) 0 1 2 3 = slide (tablePoint s.mem b 7776)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 32)) := by
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
  refine WP.mono (publicMul_ok cc.ctx (cm ▸ al) cp' ci) fun t ⟨tk, tl, td, tp⟩ => ?_
  refine ⟨cpk.trans tk, tl, td, ?_⟩
  rw [(hc.challengeInput.prefix (n := 32) (by decide)).bytes (VerifyKeep.of_acc kc), capp] at tp
  exact tp

end VG.Proof.Ed25519.Arm
end

/-! Verification branches only on points determined by the public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {umaal : Bool}

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
      (verifyRhsMul umaal) (fun s t =>
        CombineCTPre b (slide a (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr challenge) 32))) r lhs s ∧
        CombineCTPre b (slide a (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr challenge) 32))) r lhs t) := by
  apply ctBoth
  · exact (verifyRhsMul_ct m T b pk sig challenge a).mono (fun _ _ h =>
      ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1⟩, ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩⟩) (fun _ _ h => h)
  · intro s ⟨hp, hl, ha, hr, hh⟩
    refine WP.mono (verifyRhsMul_ok hp.ctx hl) fun t ⟨tk, tl, td, tp⟩ => ?_
    refine ⟨tk.ctx hp.ctx.ctx, tl, td, ?_, (tk.table (by decide) (by decide)).trans hr,
      by rw [tk.table (by decide) (by decide)]; exact hh⟩
    rw [tp, hp.kBytes, ha]

theorem verifyCombine_ct (b : BitVec 32) (ka r : Spec.Ed25519.Point) (lhs : Edwards.EPoint dZ) :
    CT (fun s t => CombineCTPre b ka r lhs s ∧ CombineCTPre b ka r lhs t)
      (verifyCombine umaal) (fun s t => EqualCTPre b lhs (Spec.Ed25519.pointAdd r ka) s ∧
        EqualCTPre b lhs (Spec.Ed25519.pointAdd r ka) t) := by
  apply ctBoth
  · cases umaal <;> [apply ctRegsS [.r0] _ (by taint_decide_sum [addSum]); apply ctRegsU [.r0] _ (by taint_decide)]
    all_goals
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
      (verifyRhs umaal) (fun _ _ => True) := by
  apply ctSeqAssoc
  exact RelCT.seq (verifyMul_public_ct m T b pk sig challenge a r lhs)
    (RelCT.seq (verifyCombine_ct b _ r lhs) (pointEqual_ct b lhs _))

end VG.Proof.Ed25519.Arm

end

end

/-! Merged from `Proof.Ed25519.Arm.VerifyCT`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.Arm.VerifyCTPoints`. -/
section
/-! The strict equation has identical traces for identical public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {umaal : Bool}

def EquationCTPre (m : Mem) (T b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic m T b pk sig challenge s ∧ AllLim s.mem b ∧ tablePoint s.mem b 7776 = a ∧ tablePoint s.mem b 7904 = r

theorem verifyLhs_public_ct (m : Mem) (T b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) :
    CT (fun s t => EquationCTPre m T b pk sig challenge a r s ∧ EquationCTPre m T b pk sig challenge a r t)
      (verifyLhs umaal) (fun s t => RhsCTPre m T b pk sig challenge a r
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32) • Proof.Ed25519.baseAff) s ∧
        RhsCTPre m T b pk sig challenge a r
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32) • Proof.Ed25519.baseAff) t) := by
  apply ctBoth
  · exact (verifyLhs_ct T b pk sig challenge).mono (fun _ _ h =>
      ⟨⟨h.1.1.ctx, h.1.2.1, h.1.1.tbl⟩, ⟨h.2.1.ctx, h.2.2.1, h.2.1.tbl⟩⟩) (fun _ _ h => h)
  · intro s ⟨hp, hl, ha, hr⟩
    refine WP.mono_syms (verifyLhs_ok hp.ctx hl hp.tbl) fun t ⟨tk, tl, tp, ta, tr⟩ syt => ?_
    exact ⟨hp.keep tk syt, tl, ta.trans ha, tr.trans hr, by rw [← hp.sBytes]; exact tp⟩

theorem verifyEquationPoints_ct (m : Mem) (T b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) :
    CT (fun s t => EquationCTPre m T b pk sig challenge a r s ∧ EquationCTPre m T b pk sig challenge a r t)
      (verifyEquationPoints umaal) (fun _ _ => True) :=
  RelCT.seq (verifyLhs_public_ct m T b pk sig challenge a r) (verifyRhs_ct m T b pk sig challenge a r _)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyCTDecodeSupport`. -/
section

/-! Merged from `Proof.Ed25519.Arm.PointDecodeCT`. -/
section
/-! Strict point decoding leaks only its public encoded bytes and pointers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {umaal : Bool}

def DecodeCTPre (base ptr : BitVec 32) (bs : List Byte) (s : State) : Prop :=
  Ctx base s ∧ AllLim s.mem base ∧ s.gpr .r12 = ptr ∧ ptr.toNat + 32 ≤ 2 ^ 32 ∧
    (∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1) ∧
    (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩ ∧
    Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32 = bs

theorem pointDecode_ct (base ptr : BitVec 32) (bs : List Byte) :
    CT (fun s t => DecodeCTPre base ptr bs s ∧ DecodeCTPre base ptr bs t) (pointDecode umaal) (fun _ _ => True) := by
  let b := Spec.Ed25519.decodeLE bs / 2 ^ 255 == 1
  let y := VG.Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255)
  have ht : CT (fun s t => DecodeCTPre base ptr bs s ∧ DecodeCTPre base ptr bs t)
      pointDecodeLoad (fun _ _ => True) := by
    apply ctRegs [.r0, .r12] _ (by native_taint_decide)
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.r0.trans h.2.1.r0.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
  have hw (s : State) (h : DecodeCTPre base ptr bs s) :
      WP isa pointDecodeLoad s fun t => RecoverCTPre base b y t ∧
        t.z = decide (Spec.Ed25519.decodeLE bs % 2 ^ 255 < Spec.X25519.P) := by
    obtain ⟨hc, hl, hp, hf, hr, hsep, hbs⟩ := h
    refine WP.mono (pointDecodeLoad_ok hc hl hp hf hr hsep) fun t ⟨kt, lt, tb, ty, tz⟩ => ?_
    refine ⟨⟨kt.ctx hc, lt, ?_, ?_⟩, ?_⟩
    · rw [tb, hbs]
    · rw [ty, hbs]
    · rw [tz, hbs]
  rw [pointDecode]
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.2.1.2.trans h.2.2.2.symm)
  · exact (recoverPoint_ct base b y).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm
end

/-! Untrusted: the loop decoding `A` and `R` is determined by public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {umaal : Bool}

theorem VerifyPublic.inBytes {m : Mem} {T b pk sig challenge : BitVec 32} {s : State}
    (h : VerifyPublic m T b pk sig challenge s) {j : Nat} (hj : j < 2) :
    Spec.Ed25519.bytesAt s.mem (State.addr (inPtr pk sig j)) 32 =
      Spec.Ed25519.bytesAt m (State.addr (inPtr pk sig j)) 32 := by
  rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl
  · exact h.pkBytes
  · exact h.rBytes

theorem VerifyPublic.decOk_eq {m : Mem} {T b pk sig challenge : BitVec 32} {s : State}
    (h : VerifyPublic m T b pk sig challenge s) : decOk s.mem pk sig 2 = decOk m pk sig 2 := by
  rw [decOk_two, decOk_two]
  unfold inPoint
  rw [h.inBytes (j := 0) (by decide), h.inBytes (j := 1) (by decide)]

/-- Before the decoding `k`, from some state before the loop with the public inputs. -/
def DecCT (m : Mem) (T b pk sig challenge : BitVec 32) (k : Nat) (s : State) : Prop :=
  ∃ s₀, VerifyPublic m T b pk sig challenge s₀ ∧ DecAt s₀ b pk sig k s ∧ s.syms = s₀.syms

theorem DecCT.r0 {m : Mem} {T b pk sig challenge : BitVec 32} {k : Nat} {s : State}
    (h : DecCT m T b pk sig challenge k s) : s.gpr .r0 = b := by
  obtain ⟨_, hp, hd, _⟩ := h
  exact (hp.ctx.keep hd.keep).ctx.r0

/-- What the iteration `k` needs public, after the pointer's load, and after the decoding. -/
def BodyCT (m : Mem) (T b pk sig challenge : BitVec 32) (k : Nat) (s : State) : Prop :=
  VerifyPublic m T b pk sig challenge s ∧ AllLim s.mem b ∧ lw s.mem b DPTR = inPtr pk sig k ∧
    lw s.mem b DTAB = BitVec.ofNat 32 (7776 + 128 * k)

def LoadedCT (m : Mem) (T b pk sig challenge : BitVec 32) (k : Nat) (s : State) : Prop :=
  VerifyPublic m T b pk sig challenge s ∧ AllLim s.mem b ∧ s.gpr .r12 = inPtr pk sig k ∧
    lw s.mem b DTAB = BitVec.ofNat 32 (7776 + 128 * k)

def DecodedCT (m : Mem) (T b pk sig challenge : BitVec 32) (k : Nat) (s : State) : Prop :=
  VerifyPublic m T b pk sig challenge s ∧ AllLim s.mem b ∧ lw s.mem b DTAB = BitVec.ofNat 32 (7776 + 128 * k)

theorem DecCT.body {m : Mem} {T b pk sig challenge : BitVec 32} {k : Nat} {s : State}
    (h : DecCT m T b pk sig challenge k s) (hk : k < 2) : BodyCT m T b pk sig challenge k s := by
  obtain ⟨_, hp, hd, hsy⟩ := h
  exact ⟨hp.keep hd.keep hsy, hd.lim, hd.ptr hk, hd.tab⟩

theorem decodeLoad_ct (m : Mem) (T b pk sig challenge : BitVec 32) (k : Nat) :
    CT (fun x y => BodyCT m T b pk sig challenge k x ∧ BodyCT m T b pk sig challenge k y)
      (.block [.ldr .r12 .r0 DPTR])
      (fun x y => LoadedCT m T b pk sig challenge k x ∧ LoadedCT m T b pk sig challenge k y) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by native_taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1.ctx.ctx.r0.trans h.2.1.ctx.ctx.r0.symm
  · intro s ⟨hp, hl, hptr, htab⟩
    refine WP.of_syms (ldrLow_ok hp.ctx.ctx (d := DPTR) (by decide) .r12 fun t ht => WP.block_nil fun syt => ?_)
    have kt : VerifyKeep b s t := VerifyKeep.of_rest (ht.rest (ws := [.r12]) (by decide)) (by decide) ht.mem
    exact ⟨hp.keep kt syt, by rw [ht.mem]; exact hl, by rw [ht.gpr]; exact hptr, by rw [ht.mem]; exact htab⟩

theorem pointDecode_public_ct (m : Mem) (T b pk sig challenge : BitVec 32) {k : Nat} (hk : k < 2) :
    CT (fun x y => LoadedCT m T b pk sig challenge k x ∧ LoadedCT m T b pk sig challenge k y) (pointDecode umaal)
      (fun x y => DecodedCT m T b pk sig challenge k x ∧ DecodedCT m T b pk sig challenge k y) := by
  have pre (x : State) (h : LoadedCT m T b pk sig challenge k x) :
      DecodeCTPre b (inPtr pk sig k) (Spec.Ed25519.bytesAt m (State.addr (inPtr pk sig k)) 32) x := by
    have hi := h.1.ctx.input hk
    exact ⟨h.1.ctx.ctx, h.2.1, h.2.2.1, hi.fit, hi.readable, hi.separate, h.1.inBytes hk⟩
  apply ctBoth
  · exact (pointDecode_ct b (inPtr pk sig k) _).mono (fun x y h => ⟨pre x h.1, pre y h.2⟩) (fun _ _ h => h)
  · intro s ⟨hp, hl, hr, htab⟩
    have hi := hp.ctx.input hk
    refine WP.mono_syms (pointDecode_ok hp.ctx.ctx hl hr hi.fit hi.readable hi.separate) fun t ht syt => ?_
    refine ⟨hp.keep (VerifyKeep.of_decode ht.1) syt, ht.2.1, ?_⟩
    rw [← htab]
    exact ht.1.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (Or.inl (by decide)) (by decide) (by decide)) (by decide)

theorem decodeNext_public_ct (m : Mem) (T b pk sig challenge : BitVec 32) (k : Nat) :
    CT (fun x y => DecodedCT m T b pk sig challenge k x ∧ DecodedCT m T b pk sig challenge k y)
      (.block decodeNext) (fun _ _ => True) := by
  rw [decodeNext_eq]
  have head : CT (fun x y => DecodedCT m T b pk sig challenge k x ∧ DecodedCT m T b pk sig challenge k y)
      (.block ([.ldr .r3 .r0 DOK, .dp .and .r3 .r3 (.reg .r9), .str .r3 .r0 DOK, .ldr .r12 .r0 DTAB,
        .dp .add .r12 .r0 (.reg .r12)] : List Instr))
      (fun x y => (x.gpr .r0 = b ∧ x.gpr .r12 = b + BitVec.ofNat 32 (7776 + 128 * k)) ∧
        (y.gpr .r0 = b ∧ y.gpr .r12 = b + BitVec.ofNat 32 (7776 + 128 * k))) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by native_taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.ctx.ctx.r0.trans h.2.1.ctx.ctx.r0.symm
    · intro s ⟨hp, _, htab⟩
      have cs := hp.ctx.ctx
      refine ldrLow_ok cs (d := DOK) (by decide) .r3 fun u1 h1 => ?_
      have c1 : Ctx b u1 := cs.of_rest (h1.rest (ws := [.r3]) (by decide)) (by decide)
      refine wp_dp (op2_reg _ _) fun u2 h2 => ?_
      have c2 : Ctx b u2 := c1.of_rest (h2.rest (ws := [.r3]) (by decide)) (by decide)
      refine strLow_ok c2 (d := DOK) (by decide) .r3 fun u3 h3 => ?_
      have c3 : Ctx b u3 := c2.of_rest (h3.rest []) (by decide)
      refine ldrLow_ok c3 (d := DTAB) (by decide) .r12 fun u4 h4 => ?_
      have c4 : Ctx b u4 := c3.of_rest (h4.rest (ws := [.r12]) (by decide)) (by decide)
      refine wp_dp (op2_reg _ _) fun u5 h5 => WP.block_nil ⟨?_, ?_⟩
      · exact (c4.of_rest (h5.rest (ws := [.r12]) (by decide)) (by decide)).r0
      · rw [h5.gpr]
        change u4.gpr .r0 + u4.gpr .r12 = _
        rw [h4.gpr, h4.other _ (by decide), c3.r0, h3.mem, h2.mem, h1.mem,
          lw_write _ _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide), htab]
  refine ctBlockAppend head ?_
  apply ctRegs [.r0, .r12] _ (by native_taint_decide)
  intro x y h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem decodeBody_public_ct (m : Mem) (T b pk sig challenge : BitVec 32) {k : Nat} (hk : k < 2) :
    CT (fun x y => BodyCT m T b pk sig challenge k x ∧ BodyCT m T b pk sig challenge k y) (decodeBody umaal)
      (fun _ _ => True) := by
  rw [decodeBody]
  exact RelCT.seq (decodeLoad_ct m T b pk sig challenge k)
    (RelCT.seq (pointDecode_public_ct m T b pk sig challenge hk) (decodeNext_public_ct m T b pk sig challenge k))

theorem decodeBody_dec {m : Mem} {T b pk sig challenge : BitVec 32} {k : Nat} (hk : k < 2) {s : State}
    (h : DecCT m T b pk sig challenge k s) :
    WP isa (decodeBody umaal) s fun t => DecCT m T b pk sig challenge (k + 1) t ∧ t.z = decide (k = 1) := by
  obtain ⟨s₀, hp, hd, hsy⟩ := h
  exact WP.mono_syms (decodeBody_ok hp.ctx hk hd) fun t ⟨ht, zt⟩ syt => ⟨⟨s₀, hp, ht, syt.trans hsy⟩, zt⟩

theorem decodeLoop_ct (m : Mem) (T b pk sig challenge : BitVec 32) :
    CT (fun x y => DecCT m T b pk sig challenge 0 x ∧ DecCT m T b pk sig challenge 0 y) (.loop (decodeBody umaal) .ne)
      (fun x y => DecCT m T b pk sig challenge 2 x ∧ DecCT m T b pk sig challenge 2 y) := by
  refine (RelCT.loop (M := isa) (I := fun n x y => ∃ k, k + n = 2 ∧ k < 2 ∧ DecCT m T b pk sig challenge k x ∧
      DecCT m T b pk sig challenge k y) ?_ 2).mono (fun x y h => ⟨0, rfl, by decide, h.1, h.2⟩) (fun _ _ h => h)
  intro n
  have step (k : Nat) (hk : k < 2) := ((decodeBody_public_ct (umaal := umaal) m T b pk sig challenge hk).mono
    (fun x y (h : DecCT m T b pk sig challenge k x ∧ DecCT m T b pk sig challenge k y) => ⟨h.1.body hk, h.2.body hk⟩)
    (fun _ _ h => h)).wp fun x y h => ⟨decodeBody_dec hk h.1, decodeBody_dec hk h.2⟩
  rcases n with _ | _ | _ | n
  · exact RelCT.of_false fun _ _ ⟨k, hkn, hk, _⟩ => by omega_using [hkn, hk]
  · refine ((step 1 (by decide)).mono (fun x y ⟨k, hkn, _, hx, hy⟩ => by
      obtain rfl : k = 1 := by omega_using [hkn]
      exact ⟨hx, hy⟩) (fun _ _ h => h)).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨hx, zx⟩, ⟨hy, zy⟩⟩
    refine ⟨?_, fun _ => ⟨hx, hy⟩, fun he => ?_⟩
    · show some (!x.z) = some (!y.z)
      rw [zx, zy]
    · have e : some (!x.z) = some true := he
      rw [zx] at e
      cases e
  · refine ((step 0 (by decide)).mono (fun x y ⟨k, hkn, _, hx, hy⟩ => by
      obtain rfl : k = 0 := by omega_using [hkn]
      exact ⟨hx, hy⟩) (fun _ _ h => h)).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨hx, zx⟩, ⟨hy, zy⟩⟩
    refine ⟨?_, fun he => ?_, fun _ => ⟨1, by omega_using [], 1, rfl, by decide, hx, hy⟩⟩
    · show some (!x.z) = some (!y.z)
      rw [zx, zy]
    · have e : some (!x.z) = some false := he
      rw [zx] at e
      cases e
  · exact RelCT.of_false fun _ _ ⟨k, hkn, hk, _⟩ => by omega_using [hkn]

/-- After the test of `DOK`: the branch, and the decoded points. -/
def TestedCT (m : Mem) (T b pk sig challenge : BitVec 32) (s : State) : Prop :=
  VerifyPublic m T b pk sig challenge s ∧ AllLim s.mem b ∧ VG.Arm.eval .ne s = some (decOk m pk sig 2) ∧
    ∀ j < 2, ∀ p, inPoint m pk sig j = some p → tablePoint s.mem b (7776 + 128 * j) = p

theorem okTest_dec {m : Mem} {T b pk sig challenge : BitVec 32} {s : State} (h : DecCT m T b pk sig challenge 2 s) :
    WP isa (.block [.ldr .r9 .r0 DOK, .cmp .r9 (.imm 0)]) s (TestedCT m T b pk sig challenge) := by
  obtain ⟨s₀, hp, ha, hsy⟩ := h
  refine WP.of_syms (ldrLow_ok (hp.ctx.keep ha.keep).ctx (d := DOK) (by decide) .r9 fun c hc =>
    wp_cmp (op2_imm (by decide)) fun d hd hz => WP.block_nil fun syd => ?_)
  have md : d.mem = s.mem := by rw [hd.mem, hc.mem]
  have kd : VerifyKeep b s₀ d := ha.keep.trans (VerifyKeep.of_rest ((hc.rest (ws := [.r9]) (by decide)).trans
    (hd.rest _)) (by decide) md)
  refine ⟨hp.keep kd (syd.trans hsy), by rw [md]; exact ha.lim, ?_, fun j hj p hj' => ?_⟩
  · show some (!d.z) = _
    rw [hz, hc.gpr, ha.ok, hp.decOk_eq]
    cases decOk m pk sig 2 <;> rfl
  · rw [md]
    refine ha.pts j hj p ?_
    unfold inPoint at hj' ⊢
    rw [hp.inBytes hj]
    exact hj'

theorem verifyDecode_ct (m : Mem) (T b pk sig challenge : BitVec 32) :
    CT (fun s t => (VerifyPublic m T b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyPublic m T b pk sig challenge t ∧ AllLim t.mem b)) (verifyDecode umaal) (fun _ _ => True) := by
  have start : CT (fun s t => (VerifyPublic m T b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyPublic m T b pk sig challenge t ∧ AllLim t.mem b)) (.block decodeStart)
      (fun x y => DecCT m T b pk sig challenge 0 x ∧ DecCT m T b pk sig challenge 0 y) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by native_taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.ctx.ctx.r0.trans h.2.1.ctx.ctx.r0.symm
    · intro s ⟨hp, hl⟩
      exact WP.mono_syms (decodeStart_ok hp.ctx hl) fun t ht syt => ⟨s, hp, ht, syt⟩
  have test : CT (fun x y => DecCT m T b pk sig challenge 2 x ∧ DecCT m T b pk sig challenge 2 y)
      (.block [.ldr .r9 .r0 DOK, .cmp .r9 (.imm 0)])
      (fun x y => TestedCT m T b pk sig challenge x ∧ TestedCT m T b pk sig challenge y) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by native_taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.r0.trans h.2.r0.symm
    · exact fun s h => okTest_dec h
  rw [verifyDecode, decodeBoth]
  refine RelCT.seq (RelCT.seq start (decodeLoop_ct m T b pk sig challenge)) (RelCT.seq test (RelCT.ite ?_ ?_ ?_))
  · exact fun _ _ h => h.1.2.2.1.trans h.2.2.2.1.symm
  · cases ha : inPoint m pk sig 0 with
    | none =>
      exact RelCT.of_false fun x y hh => by
        have e : some (decOk m pk sig 2) = some true := hh.1.1.2.2.1.symm.trans hh.2
        rw [decOk_two, ha] at e
        cases e
    | some a =>
      cases hr : inPoint m pk sig 1 with
      | none =>
        exact RelCT.of_false fun x y hh => by
          have e : some (decOk m pk sig 2) = some true := hh.1.1.2.2.1.symm.trans hh.2
          rw [decOk_two, ha, hr] at e
          cases e
      | some r =>
        refine (verifyEquationPoints_ct m T b pk sig challenge a r).mono ?_ (fun _ _ h => h)
        intro x y ⟨⟨hx, hy⟩, _⟩
        exact ⟨⟨hx.1, hx.2.1, hx.2.2.2 0 (by decide) a ha, hx.2.2.2 1 (by decide) r hr⟩,
          ⟨hy.1, hy.2.1, hy.2.2.2 0 (by decide) a ha, hy.2.2.2 1 (by decide) r hr⟩⟩
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyCTBody`. -/
section

/-! Merged from `Proof.Ed25519.Arm.VerifyCTScalar`. -/
section
/-! Canonical scalar checking loads through the public signature pointer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyScalar_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyContext b pk sig challenge s ∧ VerifyContext b pk sig challenge t)
      (.block verifyScalar) (fun _ _ => True) := by
  have head : CT (fun s t => VerifyContext b pk sig challenge s ∧ VerifyContext b pk sig challenge t)
      (.block (loadHeader 8164 ++ ([.dp .add .r12 .r12 (.imm 32)] : List Instr)))
      (fun s t => (s.gpr .r0 = b ∧ s.gpr .r12 = sig + 32) ∧ (t.gpr .r0 = b ∧ t.gpr .r12 = sig + 32)) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by native_taint_decide)
      intro s t h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.ctx.r0.trans h.2.ctx.r0.symm
    · intro s hc
      rw [WP.block_append_iff]
      refine WP.mono (loadHeader_ok hc.ctx 8164 (by decide)) fun u ⟨ur, um, up⟩ => ?_
      refine WP.mono (addInput32_ok u) fun t ⟨tr, _, tp⟩ => ?_
      exact ⟨(tr.gpr _ (by decide)).trans ((ur.gpr _ (by decide)).trans hc.ctx.r0), by rw [tp, up, hc.sigHeader]⟩
  have tail : CT (fun s t => (s.gpr .r0 = b ∧ s.gpr .r12 = sig + 32) ∧ (t.gpr .r0 = b ∧ t.gpr .r12 = sig + 32))
      (.block (unpackField SR 0 ++ scalarCompare ++ ([.cmp .r5 (.imm 0)] : List Instr))) (fun _ _ => True) := by
    apply ctRegs [.r0, .r12] _ (by native_taint_decide)
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.trans h.2.2.symm
  simpa only [verifyScalar, List.append_assoc] using ctBlockAppend head tail

theorem verifyScalar_public_ct (m : Mem) (T b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyPublic m T b pk sig challenge s ∧ VerifyPublic m T b pk sig challenge t)
      (.block verifyScalar) (fun s t =>
        (VerifyPublic m T b pk sig challenge s ∧ s.z = decide (Spec.Ed25519.decodeLE
          (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32) < Spec.Ed25519.L)) ∧
        (VerifyPublic m T b pk sig challenge t ∧ t.z = decide (Spec.Ed25519.decodeLE
          (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32) < Spec.Ed25519.L))) := by
  apply ctBoth
  · exact (verifyScalar_ct b pk sig challenge).mono (fun _ _ h => ⟨h.1.ctx, h.2.ctx⟩) (fun _ _ h => h)
  · intro s hs
    refine WP.mono_syms (verifyScalar_ok hs.ctx) fun t ⟨tk, tz⟩ syt => ?_
    exact ⟨hs.keep tk syt, tz.trans (congrArg (fun bs => decide (Spec.Ed25519.decodeLE bs < Spec.Ed25519.L)) hs.sBytes)⟩

end VG.Proof.Ed25519.Arm
end

/-! The complete strict verifier leaks only its declared public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {umaal : Bool}

theorem verifyInit_ct (m : Mem) (T b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyPublic m T b pk sig challenge s ∧ VerifyPublic m T b pk sig challenge t)
      (.block initFields) (fun s t => (VerifyPublic m T b pk sig challenge s ∧ AllLim s.mem b) ∧
        (VerifyPublic m T b pk sig challenge t ∧ AllLim t.mem b)) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by native_taint_decide)
    intro s t h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.ctx.ctx.r0.trans h.2.ctx.ctx.r0.symm
  · intro s hs
    refine WP.mono_syms (initFields_ok hs.ctx.ctx) fun t ⟨tk, tl, _⟩ syt => ?_
    exact ⟨hs.keep (VerifyKeep.of_keep tk) syt, tl⟩

theorem verifyBody_ct (m : Mem) (T b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyPublic m T b pk sig challenge s ∧ VerifyPublic m T b pk sig challenge t)
      (verifyBody umaal) (fun _ _ => True) := by
  refine RelCT.seq (verifyScalar_public_ct m T b pk sig challenge) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.1.2.trans h.2.2.symm)
  · exact (RelCT.seq (verifyInit_ct m T b pk sig challenge) (verifyDecode_ct m T b pk sig challenge)).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm
end

/-! The verifier's ABI wrapper preserves the public input relation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {umaal : Bool}

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

structure VerifyWrapPublic (m : Mem) (T b pk sig challenge : BitVec 32) (s : State) : Prop where
  pre : verifyLocal.pre s
  r0 : s.gpr .r0 = pk
  r1 : s.gpr .r1 = sig
  r2 : s.gpr .r2 = challenge
  r3 : s.gpr .r3 = b
  sym : s.syms combSym = T
  pkBytes : Spec.Ed25519.bytesAt s.mem (State.addr pk) 32 = Spec.Ed25519.bytesAt m (State.addr pk) 32
  sigBytes : Spec.Ed25519.bytesAt s.mem (State.addr sig) 64 = Spec.Ed25519.bytesAt m (State.addr sig) 64
  challengeBytes : Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64 = Spec.Ed25519.bytesAt m (State.addr challenge) 64

theorem verifySetup_ct (m : Mem) (T b pk sig challenge : BitVec 32) :
    CT (fun x y => VerifyWrapPublic m T b pk sig challenge x ∧ VerifyWrapPublic m T b pk sig challenge y)
      (.block verifySetup) (fun x y => VerifyPublic m T b pk sig challenge x ∧ VerifyPublic m T b pk sig challenge y) := by
  apply ctBoth
  · apply ctRegs [.r0, .r1, .r2, .r3] _ (by native_taint_decide)
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.1.r0.trans h.2.r0.symm
    · exact h.1.r1.trans h.2.r1.symm
    · exact h.1.r2.trans h.2.r2.symm
    · exact h.1.r3.trans h.2.r3.symm
  · intro s h
    have hp := VerifyPre.of h.pre
    refine WP.mono_syms (verifySetup_ok hp) fun t ⟨tc, _, _, tk, tf⟩ syt => ?_
    have tc' : VerifyContext b pk sig challenge t := by rw [h.r0, h.r1, h.r2, h.r3] at tc; exact tc
    have tt : VerifyTbl (s.gpr .r3) (s.syms combSym) t :=
      ⟨hp.tbl.of_frame (by rw [tk.rd, tk.wr]) tf fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.tbl_ws,
        hp.tbl_ws, congrFun syt _⟩
    rw [h.r3, h.sym] at tt
    have bytes (p : BitVec 32) (n : Nat) (hn : n ≤ 64)
        (hd : (⟨State.addr p, n⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
        Spec.Ed25519.bytesAt t.mem (State.addr p) n = Spec.Ed25519.bytesAt s.mem (State.addr p) n := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun i hi => tf.bytes (R := ⟨State.addr p, n⟩)
        (fun r hr => ?_) (by omega_using [hn] : n ≤ 2 ^ 64) (List.mem_range.mp hi)
      rw [List.mem_singleton.mp hr, h.r3]
      exact hd
    exact ⟨tc', tt, (bytes pk 32 (by decide) tc'.pkInput.separate).trans h.pkBytes,
      (bytes sig 64 (by decide) tc'.sigInput.separate).trans h.sigBytes,
      (bytes challenge 64 (by decide) tc'.challengeInput.separate).trans h.challengeBytes⟩

theorem verify_ct_of_body
    (bodyCT : ∀ (m : Mem) (T b pk sig challenge : BitVec 32),
      CT (fun s t => VerifyPublic m T b pk sig challenge s ∧ VerifyPublic m T b pk sig challenge t)
        (verifyBody umaal) (fun _ _ => True)) :
    ConstantTime isa verifyLocal.pre verifyLocal.pub (verifyEquation umaal) := by
  have hct (m : Mem) (T b pk sig challenge : BitVec 32) :
      CT (fun x y => VerifyWrapPublic m T b pk sig challenge x ∧ VerifyWrapPublic m T b pk sig challenge y)
        (verifyEquation umaal) (fun _ _ => True) := by
    have hb := (bodyCT m T b pk sig challenge).wpDep (fun x y h => ⟨verifyBody_ok h.1.ctx h.1.tbl, verifyBody_ok h.2.ctx h.2.tbl⟩)
    have hb' := hb.mono (fun _ _ h => h) (fun x y ⟨_, a, c, h, hx, hy⟩ =>
      And.intro (hx.1.ctx h.1.ctx.ctx).r0 (hy.1.ctx h.2.ctx.ctx).r0)
    refine RelCT.seq (verifySetup_ct m T b pk sig challenge) (RelCT.seq hb' ?_)
    apply ctRegs [.r0] _ (by native_taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.trans h.2.symm
  intro s t tx ty u v hs ht ⟨_, h0, h1, h2, h3, hsym, hbytes⟩ ex ey
  have hb := byteMap_inj hbytes
  obtain ⟨first, last⟩ := List.append_inj' hb (by simp only [bytesAt_length])
  obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [bytesAt_length])
  rw [← h0] at first
  rw [← h1] at middle
  rw [← h2] at last
  exact (hct s.mem (s.syms combSym) (s.gpr .r3) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) _ _ _ _ _ _
    ⟨⟨hs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨ht, h0.symm, h1.symm, h2.symm, h3.symm, hsym.symm, first.symm, middle.symm, last.symm⟩⟩ ex ey).1

theorem verify_ct : ConstantTime isa verifyLocal.pre verifyLocal.pub (verifyEquation umaal) :=
  verify_ct_of_body verifyBody_ct

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyLit`. -/
section
namespace VG.Impl.Ed25519.Arm
materialize_code verifyEquationPlain := verifyEquation false
materialize_code verifyEquationUmaal := verifyEquation true
end VG.Impl.Ed25519.Arm
end

/-! The verification equation meets the reviewed contract and preserves the ARM ABI. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {umaal : Bool}

theorem verify_ok (s : State) (hs : verifyLocal.pre s) :
    ∃ t s', Exec isa (verifyEquation umaal) s t s' ∧ abiPreserved s s' ∧ verifyLocal.post s s' :=
  verifyEquation_correct (VerifyPre.of hs)

end VG.Proof.Ed25519.Arm
