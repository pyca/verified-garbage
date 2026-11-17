module

import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTBlocks
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Ed25519.Arm.PointEqual
public import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTPublic
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTLit
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTFrom
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.Arm.PointEqual
meta import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTPublic
meta import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTLit
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTFrom
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
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

/-! Verification multiplies A by the first 256 bits of the public challenge. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {umaal : Bool}

def verifyRhsMul (umaal : Bool) : Prog isa :=
  .seq (.block (pointTableRead 7776 ++ loadHeader 8168)) (publicMul umaal)

/-- What `publicMul` needs in each run: the same bytes of `k`, which are public, and the same `A`. -/
def PubMulPre (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) (s : State) : Prop :=
  Ctx b s ∧ AllLim s.mem b ∧ s.gpr .r12 = ptr ∧ VerifyInput b ptr 32 s ∧
    Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32 = ks ∧ point (env s.mem b) 0 1 2 3 = a

/-- A run before a byte of `k`, with `m` bytes left. -/
def PubRun (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) (m : Nat) (s : State) : Prop :=
  ByteAt (Spec.Ed25519.decodeLE ks) b ptr a m s ∧ VerifyInput b ptr 32 s ∧
    Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32 = ks

theorem pubRun_step {ks : List Byte} {a : Spec.Ed25519.Point} {b ptr : BitVec 32} {m : Nat} {s : State}
    (h : PubRun ks a b ptr (m + 1) s) (hm : m < 32) :
    WP isa (byteStep umaal) s fun t => PubRun ks a b ptr m t ∧ t.z = decide (m = 0) :=
  WP.mono (byteStep_ok h.1 hm h.2.1 (congrArg Spec.Ed25519.decodeLE h.2.2)) fun _ ⟨tk, tb, tz⟩ =>
    ⟨⟨tb, h.2.1.keep (VerifyKeep.of_point tk), (h.2.1.bytes (VerifyKeep.of_point tk)).trans h.2.2⟩, tz⟩

/-- The byte's load: its address is `k`'s pointer and the public index, and both runs load the
same byte. -/
theorem bitsLoad_ct (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) {m : Nat} (hm : m < 32) :
    CT (fun x y => PubRun ks a b ptr (m + 1) x ∧ PubRun ks a b ptr (m + 1) y) (.block bitsLoad)
      (fun x y => BitAt (Spec.Ed25519.decodeLE ks) b ptr a m 0 x ∧
        BitAt (Spec.Ed25519.decodeLE ks) b ptr a m 0 y) := by
  have head : CT (fun x y => PubRun ks a b ptr (m + 1) x ∧ PubRun ks a b ptr (m + 1) y) (.block bitsAddr)
      (fun x y => (x.gpr .r0 = b ∧ x.gpr .r3 = ptr + BitVec.ofNat 32 m) ∧
        (y.gpr .r0 = b ∧ y.gpr .r3 = ptr + BitVec.ofNat 32 m)) := by
    apply ctBoth
    · apply ctRegs [.r0, .r11] _ (by native_taint_decide)
      intro x y h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.1.ctx.r0.trans h.2.1.ctx.r0.symm
      · exact h.1.1.r11.trans h.2.1.r11.symm
    · intro s h
      exact WP.mono (bitsAddr_ok h.1) fun t ⟨tr, _, _, t3⟩ => ⟨(tr.gpr _ (by decide)).trans h.1.ctx.r0, t3⟩
  have tail : CT (fun x y => (x.gpr .r0 = b ∧ x.gpr .r3 = ptr + BitVec.ofNat 32 m) ∧
      (y.gpr .r0 = b ∧ y.gpr .r3 = ptr + BitVec.ofNat 32 m)) (.block bitsByte) (fun _ _ => True) := by
    apply ctRegs [.r0, .r3] _ (by native_taint_decide)
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.trans h.2.2.symm
  have whole : CT (fun x y => PubRun ks a b ptr (m + 1) x ∧ PubRun ks a b ptr (m + 1) y) (.block bitsLoad)
      (fun _ _ => True) := ctBlockAppend head tail
  exact ctBoth whole fun s h =>
    WP.mono (bitsLoad_ok h.1 hm h.2.1 (congrArg Spec.Ed25519.decodeLE h.2.2)) fun _ ht => ht.2

/-- The byte's eight bits: the branches are on `r10`, the same in both runs. -/
theorem bitsRun_ct (K : Nat) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) (m : Nat) :
    CT (fun x y => BitAt K b ptr a m 0 x ∧ BitAt K b ptr a m 0 y)
      (repeatThen 8 (bitStep umaal) (.block [.cmp .r11 (.imm 0)])) (fun _ _ => True) := by
  cases umaal <;> [apply ctRegsS [.r0, .r10, .r11] _ (by taint_decide_sum [addSum, doubleSum]);
    apply ctRegsU [.r0, .r10, .r11] _ (by taint_decide)]
  all_goals
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.ctx.r0.trans h.2.ctx.r0.symm
    · exact h.1.r10.trans h.2.r10.symm
    · exact h.1.r11.trans h.2.r11.symm

theorem byteStep_ct (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) {m : Nat} (hm : m < 32) :
    CT (fun x y => PubRun ks a b ptr (m + 1) x ∧ PubRun ks a b ptr (m + 1) y) (byteStep umaal)
      (fun x y => (PubRun ks a b ptr m x ∧ x.z = decide (m = 0)) ∧
        (PubRun ks a b ptr m y ∧ y.z = decide (m = 0))) :=
  ctBoth (RelCT.seq (bitsLoad_ct ks a b ptr hm) (bitsRun_ct _ a b ptr m)) fun _ h => pubRun_step h hm

theorem publicLoop_ct (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) :
    CT (fun x y => PubRun ks a b ptr 32 x ∧ PubRun ks a b ptr 32 y) (.loop (byteStep umaal) .ne)
      (fun _ _ => True) := by
  refine (RelCT.loop (M := isa) (Q := fun _ _ => True)
    (fun n x y => 0 < n ∧ n ≤ 32 ∧ PubRun ks a b ptr n x ∧ PubRun ks a b ptr n y)
    (fun n => ?_) 32).mono (fun x y h => ⟨by decide, le_rfl, h.1, h.2⟩) fun _ _ h => h
  by_cases hn : 0 < n ∧ n ≤ 32
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_using [hn]⟩
    refine (byteStep_ct ks a b ptr (by omega_using [hn])).mono (fun x y h => ⟨h.2.2.1, h.2.2.2⟩)
      fun u v h => ?_
    obtain ⟨⟨ru, zu⟩, ⟨rv, zv⟩⟩ := h
    refine ⟨by show some (!u.z) = some (!v.z); rw [zu, zv], fun _ => trivial, fun ht => ?_⟩
    have e : some (!u.z) = some true := ht
    rw [zu] at e
    have hm0 : m ≠ 0 := by
      intro h0
      subst h0
      cases e
    exact ⟨m, by omega_arith, by omega_using [hm0], by omega_using [hn], ru, rv⟩
  · exact RelCT.of_false fun x y h => hn ⟨h.1, h.2.1⟩

theorem publicMul_ct (ks : List Byte) (a : Spec.Ed25519.Point) (b ptr : BitVec 32) :
    CT (fun x y => PubMulPre ks a b ptr x ∧ PubMulPre ks a b ptr y) (publicMul umaal) (fun _ _ => True) := by
  have hi : CT (fun x y => PubMulPre ks a b ptr x ∧ PubMulPre ks a b ptr y) publicMulInit
      (fun x y => PubRun ks a b ptr 32 x ∧ PubRun ks a b ptr 32 y) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by native_taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.r0.trans h.2.1.r0.symm
    · intro s ⟨hc, hl, hp, hin, hb, ha⟩
      refine WP.mono (publicMulInit_ok hc hl hp) fun w ⟨kw, hw⟩ => ?_
      rw [hb, ha] at hw
      exact ⟨hw, hin.keep (VerifyKeep.of_point kw), (hin.bytes (VerifyKeep.of_point kw)).trans hb⟩
  rw [publicMul]
  exact RelCT.seq hi (publicLoop_ct ks a b ptr)

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
      point (env t.mem b) 0 1 2 3 = ladder (tablePoint s.mem b 7776)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 32)) 256 := by
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
        CombineCTPre b (ladder a (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr challenge) 32)) 256) r lhs s ∧
        CombineCTPre b (ladder a (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr challenge) 32)) 256) r lhs t) := by
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
