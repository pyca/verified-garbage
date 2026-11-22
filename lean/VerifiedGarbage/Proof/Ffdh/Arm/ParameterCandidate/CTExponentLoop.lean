module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ExponentStep
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
public import VerifiedGarbage.Proof.Ffdh.Arm.RegistersCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
public import VerifiedGarbage.Proof.Framework.Arm.Inline
meta import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
meta import VerifiedGarbage.Proof.Ffdh.Arm.RegistersCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
meta import VerifiedGarbage.TCB.Arm.Isa
meta import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Inline
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Bignum.Arm.R2
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Bignum.Arm.CallStack
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout

/-! ### `Ffdh.Arm.ParameterCandidate.CTMontOne`, which this module and modules that import it used -/

section

/-! Montgomery one is prepared through the same constant-trace RSA operations. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

structure MontMathData where
  base : BitVec 32
  capacity : Nat
  words : Nat

def MontR2 (p : MontMathData) (s : State) : Prop := ArithmeticReady p.base p.capacity p.words s ∧
  numAt s.mem (State.addr p.base) p.words 4 < numAt s.mem (State.addr p.base) p.words 0 ∧
  CallStack p.base p.capacity s

theorem smallOne_ready (p : MontMathData) (s : State) (h : MontR2 p s) :
    WP isa (VG.Impl.Bignum.Arm.smallConst 1 1) s (MontR2 p) := by
  refine WP.mono (smallConst_ok s 1 h.1 (o := 1) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro t ⟨ready, _, _, keeps, _, rest⟩
  have fits : arrAt p.words 8 ≤ 8 * p.capacity := h.1.width ▸ h.1.layout.2.2.1
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine ⟨ready, ?_, h.2.2.of_rest rest⟩
  rw [keeps_array_num keeps fits op4 (by decide), keeps_array_num keeps fits op0 (by decide)]
  exact h.2.1

theorem montOne_ready (b : MontBackend) (p : MontMathData) (s : State) (h : MontR2 p s) :
    WP isa (.seq (VG.Impl.Bignum.Arm.smallConst 1 1) (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul 1 1 4)) s
      (ArithmeticReady p.base p.capacity p.words) := by
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.seq (WP.mono (smallOne_ready p s h) ?_)
  intro u ready
  refine WP.mono (montCallOp_ok b.name b.mul (fun v input => b.correct v input op1 op1 op4) b.stackOk u
    ready.1 ready.2.2 op1 op1 op4 (by decide) ready.2.1) ?_
  rintro t ⟨result, _⟩
  exact result

theorem montOne_ct (b : MontBackend) : RelCT isa (Two MontR2)
    (.seq (VG.Impl.Bignum.Arm.smallConst 1 1) (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul 1 1 4))
      (fun _ _ => True) := by
  have smallTrace : RelCT isa (Two MontR2) (VG.Impl.Bignum.Arm.smallConst 1 1) (fun _ _ => True) := by
    intro s t trS trT u v h runS runT
    obtain ⟨p, left, right, sp⟩ := h
    exact smallConst_ct 1 (o := 1) (by decide) (by decide) (by decide) _ _ _ _ _ _ ⟨left.1, right.1, sp⟩ runS runT
  have small : RelCT isa (Two MontR2) (VG.Impl.Bignum.Arm.smallConst 1 1) (Two MontR2) :=
    two_post smallTrace smallOne_ready
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have encode : RelCT isa (Two MontR2) (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul 1 1 4)
      (fun _ _ => True) := by
    intro s t trS trT u v h runS runT
    obtain ⟨p, left, right, sp⟩ := h
    exact (montCallOp_ct b.name b.mul (b.rawCT op1 op1 op4) op1 op1 op4).mono (fun _ _ h => h)
      (fun _ _ _ => trivial) _ _ _ _ _ _
      ⟨left.1, right.1, left.2.2, right.2.2, left.2.1, right.2.1, sp⟩ runS runT
  exact small.seq encode

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CTKeyRegisters`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.CTPolicy`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.CTLocalBlock`, which only this module used -/

section

/-! Fixed local-frame blocks retain public stack addresses while their values may vary. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm

def localOnlyInstr : Instr → Bool
  | .addSp _ _ => true
  | .str _ base _ => base == .r12
  | .ldrSp dst _ => dst != .r12
  | .ldr .. | .ldrb .. | .strb .. | .strd .. | .push .. | .pop .. | .alloc .. | .free .. => false
  | op => !(clobbers op .r12)

private theorem localOnly_addresses {i : Instr} (allowed : localOnlyInstr i = true)
    {s t : State} (h : LocalAddress s t) : addrs i s = addrs i t := by
  cases i <;> simp only [localOnlyInstr] at allowed <;> try cases allowed
  all_goals try rfl
  all_goals try exact congrArg (fun sp => [State.addr (sp + _)]) h.2
  case str source base d =>
    have equal : base = .r12 := eq_of_beq allowed
    subst base
    simp only [addrs, h.1]

private theorem localOnly_keep {i : Instr} (allowed : localOnlyInstr i = true)
    {s t u v : State} (h : LocalAddress s t) (left : exec i s = some u) (right : exec i t = some v) :
    LocalAddress u v := by
  refine ⟨?_, (exec_sp left).trans (h.2.trans (exec_sp right).symm)⟩
  by_cases add : ∃ dst n, i = .addSp dst n
  · obtain ⟨dst, n, rfl⟩ := add
    by_cases small : n < 256
    · simp only [exec, small, ite_true, Option.some.injEq] at left right
      subst u
      subst v
      by_cases same : dst = .r12
      · subst dst
        simp only [State.setReg, ite_true, h.2]
      · simp only [State.setReg, Ne.symm same, ite_false]
        exact h.1
    · simp only [exec, small, ite_false] at left
      cases left
  · have stable : clobbers i .r12 = false := by
      cases i <;> simp_all [localOnlyInstr, clobbers, dstOf]
    exact (exec_gpr stable left).trans (h.1.trans (exec_gpr stable right).symm)

theorem localBlock_ct (code : List Instr) (allowed : code.all localOnlyInstr = true) :
    RelCT isa LocalAddress (.block code) LocalAddress := by
  induction code with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons op rest ih =>
    have valid : localOnlyInstr op = true ∧ rest.all localOnlyInstr = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using allowed
    exact RelCT.block_append ((single_ct (fun _ _ h => localOnly_addresses valid.1 h)
      (fun _ _ _ _ h left right => localOnly_keep valid.1 h left right)).seq (ih valid.2))

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! Public phase setup and sieve flags write only fixed local-frame addresses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm

theorem save_ct (r : Reg) (slot : Nat) : RelCT isa (fun s t => s.sp = t.sp)
    (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.save r slot)) (fun s t => s.sp = t.sp) :=
  RelCT.block_append (stackAddr_ct.seq ((localBlock_ct [.str r .r12 slot] rfl).mono
    (fun _ _ h => h) (fun _ _ h => h.2)))

theorem saveWord_ct (r : Reg) (slot : Nat) (value : BitVec 32) : RelCT isa (fun s t => s.sp = t.sp)
    (.block (([.mov r (.imm value)] : List Instr) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.save r slot)) (fun s t => s.sp = t.sp) :=
  RelCT.block_append ((stackOnly_ct [.mov r (.imm value)] rfl).seq (save_ct r slot))

private def phaseRead (q : Bool) : List Instr := [.ldrSp .r3 24] ++
  if q then [.dp .sub .r3 .r3 (.imm 1)] else []

private def phaseTail : List Instr := [.str .r3 .r12 44] ++ VG.Impl.Ffdh.Arm.ParameterCandidate.phaseWidth ++
  VG.Impl.Ffdh.Arm.ParameterCandidate.phaseChecks ++ VG.Impl.Ffdh.Arm.ParameterCandidate.phasePassed

theorem phaseHead_ct (q : Bool) : RelCT isa (fun s t => s.sp = t.sp)
    (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead q)) (fun s t => s.sp = t.sp) := by
  have read : RelCT isa (fun s t => s.sp = t.sp) (.block (phaseRead q)) (fun s t => s.sp = t.sp) :=
    stackOnly_ct _ (by cases q <;> decide)
  have tail : RelCT isa LocalAddress (.block phaseTail) (fun s t => s.sp = t.sp) :=
    (localBlock_ct _ (by decide)).mono (fun _ _ h => h) (fun _ _ h => h.2)
  have trace := RelCT.block_append (read.seq (RelCT.block_append (stackAddr_ct.seq tail)))
  cases q <;> exact trace

theorem sieveFlag_ct : RelCT isa (fun s t => s.sp = t.sp ∧ s.z = t.z)
    VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFlag (fun s t => s.sp = t.sp) := by
  refine RelCT.ite (fun s t h => by change some s.z = some t.z; rw [h.2]) ?_ ?_
  · exact (saveWord_ct .r1 64 1).mono (fun _ _ h => h.1.1) (fun _ _ h => h)
  · exact RelCT.block_nil (fun _ _ h => h.1.1)

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! RSA's compact array operations retain the three public workspace-view registers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm

def keyRegs : List Reg := [.r7, .r8, .r9]
def KeyRegEq (s t : State) : Prop := RegistersEqual keyRegs s t ∧ s.sp = t.sp

def keepsKeyRegs (code : Prog isa) : Bool :=
  (instrs code).all fun op => !(clobbers op .r7 || clobbers op .r8 || clobbers op .r9)

private theorem keyRegs_untouched {code : Prog isa} (kept : keepsKeyRegs code = true) :
    ∀ r ∈ keyRegs, ∀ op ∈ instrs code, clobbers op r = false := by
  intro r hr op hop
  have valid := List.all_eq_true.mp kept op hop
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at valid
  simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact valid.1.1
  · exact valid.1.2
  · exact valid.2

theorem keyRegs_keep_ct {P : State → State → Prop} {code : Prog isa}
    (trace : RelCT isa P code (fun _ _ => True))
    (publicRegs : ∀ s t, P s t → KeyRegEq s t)
    (kept : keepsKeyRegs code = true) (noCalls : code.noCalls = true) :
    RelCT isa P code KeyRegEq :=
  registers_keep_ct keyRegs trace (fun s t h => (publicRegs s t h).1)
    (fun s t h => (publicRegs s t h).2) (keyRegs_untouched kept) noCalls

theorem keyRegs_stack_ct {code : Prog isa}
    (trace : RelCT isa (fun s t => s.sp = t.sp) code (fun s t => s.sp = t.sp))
    (kept : keepsKeyRegs code = true) (noCalls : code.noCalls = true) : RelCT isa KeyRegEq code KeyRegEq :=
  registers_keep_ct keyRegs (trace.mono (fun _ _ h => h.2) (fun _ _ _ => trivial))
    (fun _ _ h => h.1) (fun _ _ h => h.2) (keyRegs_untouched kept) noCalls

theorem keyRegs_taint_ct {code : Prog isa} (cert : CandidateCert keyRegs code)
    (kept : keepsKeyRegs code = true) (noCalls : code.noCalls = true) : RelCT isa KeyRegEq code KeyRegEq := by
  obtain ⟨hint, checked⟩ := cert
  have trace : RelCT isa KeyRegEq code (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs keyRegs) (fun _ _ h => Taint.agree_ofRegs h.1) checked
  exact registers_keep_ct keyRegs trace (fun _ _ h => h.1) (fun _ _ h => h.2) (keyRegs_untouched kept) noCalls

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CTExponentStep`, which only this module used -/

section

/-! Native exponent halving uses public array addresses and fixed stack slots. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm

private theorem half27_taint : CandidateCert keyRegs (VG.Impl.Rsa.Arm.Keys.half 27) := ⟨_, by taint_decide⟩

theorem exponentHalf_ct : RelCT isa KeyRegEq VG.Impl.Ffdh.Arm.ParameterCandidate.exponentHalf KeyRegEq :=
  (keyRegs_stack_ct (stackOnly_ct [.mov .r11 (.imm 0)] rfl) (by decide) (by decide)).seq
    ((keyRegs_taint_ct half27_taint (by decide) (by decide)).seq
      ((keyRegs_stack_ct
        (RelCT.block_append ((stackOnly_ct [.ldrSp .r1 64, .subs .r1 .r1 (.imm 1)] rfl).seq (save_ct .r1 64)))
        (by decide) (by decide)).seq (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! The exponent halving loop follows its public countdown in both runs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Keys (num)
open VG.Proof.Ffdh.Arm.KeySearch (Two)

structure ExponentCountData where
  math : MontMathData
  count : Nat

structure ExponentCountState (p : ExponentCountData) (s : State) : Prop where
  workspace : Workspace s p.math.base (8 * p.math.capacity)
  ready : KeyReady p.math.base p.math.capacity p.math.words s
  data : MontData p.math.base p.math.capacity p.math.words s.mem
  stack : Workspace s s.sp 72
  separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.math.base, 8 * p.math.capacity⟩
  positive : 0 < p.count
  bound : p.count ≤ 4
  saved : s.mem.readW (State.addr (s.sp + 64#32)) 32 = BitVec.ofNat 32 p.count

private structure ExponentCountAfter (p : ExponentCountData) (s : State) : Prop where
  workspace : Workspace s p.math.base (8 * p.math.capacity)
  ready : KeyReady p.math.base p.math.capacity p.math.words s
  data : MontData p.math.base p.math.capacity p.math.words s.mem
  stack : Workspace s s.sp 72
  separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.math.base, 8 * p.math.capacity⟩
  saved : s.mem.readW (State.addr (s.sp + 64#32)) 32 = BitVec.ofNat 32 (p.count - 1)
  zero : s.z = decide (p.count = 1)

private theorem exponentCountAfter_ok (p : ExponentCountData) (s : State) (h : ExponentCountState p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.exponentHalf s (ExponentCountAfter p) := by
  refine WP.mono (exponentHalfStep_ok h.workspace h.ready h.data h.stack h.positive h.bound h.saved h.separate) ?_
  rintro t ⟨ready, data, _, saved, zero, _, _, _, rest⟩
  exact ⟨h.workspace.congr rest.wr, ready, data, by rw [rest.sp]; exact h.stack.congr rest.wr,
    by rw [rest.sp]; exact h.separate, saved, zero⟩

private theorem exponentCountPair_keyRegs {p : ExponentCountData} {s t : State}
    (left : ExponentCountState p s) (right : ExponentCountState p t) (sp : s.sp = t.sp) : KeyRegEq s t := by
  refine ⟨?_, sp⟩
  intro r hr
  simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact left.ready.r7.trans right.ready.r7.symm
  · exact left.ready.r8.trans right.ready.r8.symm
  · exact left.ready.r9.trans right.ready.r9.symm

private theorem exponentCountStep_fixed (p : ExponentCountData) :
    RelCT isa (fun s t => ExponentCountState p s ∧ ExponentCountState p t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.ParameterCandidate.exponentHalf
      (fun s t => ExponentCountAfter p s ∧ ExponentCountAfter p t ∧ s.sp = t.sp) := by
  intro s t trS trT u v h runS runT
  have leak := (exponentHalf_ct _ _ _ _ _ _ (exponentCountPair_keyRegs h.1 h.2.1 h.2.2) runS runT).1
  obtain ⟨_, u', execS, postS⟩ := exponentCountAfter_ok p s h.1
  obtain ⟨_, v', execT, postT⟩ := exponentCountAfter_ok p t h.2.1
  obtain ⟨_, rfl⟩ := Exec.det runS execS
  obtain ⟨_, rfl⟩ := Exec.det runT execT
  exact ⟨leak, postS, postT, (Exec.rdwr runS).2.2.trans (h.2.2.trans (Exec.rdwr runT).2.2.symm)⟩

private def ExponentLoopPair (remaining : Nat) (s t : State) : Prop :=
  ∃ p : ExponentCountData, p.count = remaining ∧ ExponentCountState p s ∧ ExponentCountState p t ∧ s.sp = t.sp

private theorem ExponentCountAfter.continue {p : ExponentCountData} {s : State}
    (h : ExponentCountAfter p s) (positive : 0 < p.count) (bound : p.count ≤ 4)
    (go : isa.eval .ne s = some true) : ExponentCountState ⟨p.math, p.count - 1⟩ s := by
  have notLast : p.count ≠ 1 := by
    change some (!s.z) = some true at go
    rw [h.zero] at go
    simpa using go
  have nextPositive : 0 < p.count - 1 := by omega_using [positive, notLast]
  have nextBound : p.count - 1 ≤ 4 := by omega_using [bound]
  exact ⟨h.workspace, h.ready, h.data, h.stack, h.separate, nextPositive, nextBound, h.saved⟩

theorem exponentHalfLoop_ct : RelCT isa (Two ExponentCountState)
    (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.exponentHalf .ne) (fun _ _ => True) := by
  have step : ∀ n, RelCT isa (ExponentLoopPair n) VG.Impl.Ffdh.Arm.ParameterCandidate.exponentHalf
      (fun u v => isa.eval .ne u = isa.eval .ne v ∧
        (isa.eval .ne u = some false → True) ∧
        (isa.eval .ne u = some true → ∃ m, m < n ∧ ExponentLoopPair m u v)) := by
    intro n s t trS trT u v h runS runT
    obtain ⟨p, remaining, left, right, sp⟩ := h
    obtain ⟨leak, postU, postV, spUV⟩ := exponentCountStep_fixed p _ _ _ _ _ _ ⟨left, right, sp⟩ runS runT
    refine ⟨leak, ?_, by intro _; trivial, ?_⟩
    · change some (!u.z) = some (!v.z)
      rw [postU.zero, postV.zero]
    · intro go
      have goV : isa.eval .ne v = some true := by
        change some (!v.z) = some true
        change some (!u.z) = some true at go
        rw [postV.zero, ← postU.zero]
        exact go
      exact ⟨p.count - 1, by rw [← remaining]; have := left.positive; omega_using [this],
        ⟨p.math, p.count - 1⟩, rfl, postU.continue left.positive left.bound go,
        postV.continue right.positive right.bound goV, spUV⟩
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  exact RelCT.loop ExponentLoopPair step p.count _ _ _ _ _ _ ⟨p, rfl, left, right, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
