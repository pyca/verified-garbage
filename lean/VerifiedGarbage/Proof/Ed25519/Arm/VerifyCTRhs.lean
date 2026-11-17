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
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit
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
  obtain hD := Proof.Ed25519.Slide.digits_odd (Spec.Ed25519.decodeLE ks)
  have pre (s : State) (h : RecRun ks a b ptr 256 s) :
      SumPre a (Proof.Ed25519.Slide.digits (Spec.Ed25519.decodeLE ks)) b s :=
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
