module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeFinish
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Bignum.Arm.ExportBECT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
meta import VerifiedGarbage.Impl.Ffdh.Arm.Domain
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
meta import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT

/-! ### `Ffdh.Arm.MaskOutputCT`, which this module and modules that import it used -/

section

/-! Shared-value rejection changes output bytes and status but never the masking trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem maskOutputArgs_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.ldrSp .r0 4, .ldrSp .lr 32, .ldrSp .r2 64,
      .mov .r3 (.imm 0), .dp .sub .r2 .r3 (.reg .r2)]) (fun _ _ => True) := by
  have tail : RelCT isa (fun _ _ => True)
      (.block [.mov .r3 (.imm 0), .dp .sub .r2 .r3 (.reg .r2)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append ((stackLoads_ct [(.r0, 4), (.lr, 32), (.r2, 64)]).seq
    (tail.mono (fun _ _ _ => trivial) (fun _ _ h => h)))

theorem maskOutput_ct {p : Inputs} {flag1 flag2 : BitVec 32} :
    RelCT isa (fun s t => MaskOutputInput p flag1 s ∧ MaskOutputInput p flag2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.Exchange.maskOutput (fun _ _ => True) := by
  let Q := fun s : State => s.gpr .r0 = p.output ∧ s.gpr .lr = BitVec.ofNat 32 p.k
  have args := maskOutputArgs_ct.mono
    (P' := fun (s t : State) => MaskOutputInput p flag1 s ∧ MaskOutputInput p flag2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (s : State) {flag : BitVec 32} (h : MaskOutputInput p flag s) :
      WP isa (.block [.ldrSp .r0 4, .ldrSp .lr 32, .ldrSp .r2 64,
        .mov .r3 (.imm 0), .dp .sub .r2 .r3 (.reg .r2)]) s Q :=
    WP.mono (maskOutputArgs_ok s h) fun _ j => ⟨j.1.1, j.1.2.1⟩
  have loop : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp) VG.Impl.Bignum.Arm.maskBytes
      (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨maskBytes_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.1.trans h.2.1.1.symm, h.1.2.trans h.2.1.2.symm⟩ e1 e2, trivial⟩
  have finish := ((relCT_keep_sp loop (fun _ _ h => h.2.2)).seq (loadStack_ct .r0 64)).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)
  unfold VG.Impl.Ffdh.Arm.Domain.Exchange.maskOutput
  exact relCT_chain args (fun s h => wp s h) (fun s h => wp s h) finish

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.ExportResultCT`, which this module and modules that import it used -/

section

/-! Shared-value encoding uses public output pointers and fixed lengths. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure ExportArgsReady (p : Inputs) (s : State) : Prop where
  ready : SmallFnReady p.base p.len p.w 6 s
  dst : s.gpr .r4 = p.output
  count : s.gpr .r6 = BitVec.ofNat 32 p.k

theorem exportResultArgs_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.mov .r2 (.imm 6), .ldrSp .r4 4, .ldrSp .r6 32]) (fun _ _ => True) := by
  have index : RelCT isa (fun s t => s.sp = t.sp) (.block [.mov .r2 (.imm 6)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact (RelCT.block_append ((relCT_keep_sp index (fun _ _ h => h)).seq
    (stackLoads_ct [(.r4, 4), (.r6, 32)]))).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem exportResult_ct {p : Inputs} {slots : List Nat} (h4 : 4 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t => ImportAtInput p slots s ∧ ImportAtInput p slots t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult (fun _ _ => True) := by
  have args := exportResultArgs_ct.mono
    (P' := fun (s t : State) => ImportAtInput p slots s ∧ ImportAtInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (s : State) (h : ImportAtInput p slots s) :
      WP isa (.block [.mov .r2 (.imm 6), .ldrSp .r4 4, .ldrSp .r6 32]) s (ExportArgsReady p) := by
    refine WP.mono (exportResultArgs_ok s h.context h4 h32) ?_
    rintro u ⟨⟨index, dst, count, mem⟩, rest⟩
    have ready := h.ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr)
    exact ⟨⟨ready.workspace, ready.layout, ready.width, ready.ptr, index⟩, dst, count⟩
  have bytes := (exportBE_ct (base := p.base) (dst := p.output) (len := p.len) (w := p.w)
    (o := 6) (k := p.k) (by decide) (by have := p.minLength; omega_using [this])).mono
    (P' := fun (s t : State) => ExportArgsReady p s ∧ ExportArgsReady p t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.1.dst, h.2.1.dst, h.1.count, h.2.1.count⟩)
    (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult
  exact relCT_chain args wp wp bytes

end VG.Proof.Ffdh.Arm

end

end

/-! Export and rejection masking have the same trace for every shared value and status. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)

structure ExchangeFinishInput (p : Inputs) (slots : List Nat) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  output : OutputBuffer p.output p.k s
  workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩
  stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩
  valueFit : numAt s.mem (State.addr p.base) p.w 6 < 2 ^ (8 * p.k)

def AnyMaskInput (p : Inputs) (s : State) : Prop := ∃ flag, MaskOutputInput p flag s

theorem exchangeSave_ready (s : State) {p : Inputs} {slots : List Nat}
    (h : ExchangeFinishInput p slots s) (stable : stableSlots slots = true)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.Exchange.saveResult) s (ExchangeFinishInput p slots) := by
  refine WP.mono (saveResult_ok s h.context.locals) ?_
  rintro u ⟨⟨_, _, frame⟩, rest⟩
  have ptr := (rest.gpr .r0 (by simp)).trans h.context.ptr
  have context := h.context.after_local (by decide : 64 + 4 ≤ 72) frame rest ptr
    (fun d hd => (stableSlots_at stable hd).1) saved
  have ready := h.ready.after_external frame (by
    intro r hr
    rw [List.mem_singleton] at hr; subst r
    exact h.context.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))) (by
    intro r hr
    rw [List.mem_singleton] at hr; subst r
    simpa only [off, BitVec.add_zero] using
      (Offset.disjoint (State.addr s.sp) (d := 0) (n := 4) (e := 64) (k := 4) (by left; decide) (by decide) (by decide))) rest ptr
  have fits : arrAt p.w 8 ≤ 8 * p.len := h.ready.width ▸ h.ready.layout.2.2.1
  exact ⟨context, ready.1, h.output.after rest, h.workspaceSep, by rw [rest.sp]; exact h.stackSep,
    by rw [ready.2.number fits (by decide : 6 < 8)]; exact h.valueFit⟩

theorem exchangeExport_ready (s : State) {p : Inputs} {slots : List Nat}
    (h : ExchangeFinishInput p slots s) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots) :
    WP isa VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult s (AnyMaskInput p) := by
  refine WP.mono (exportResult_ok s h.context h4 h32 h.ready h.output h.workspaceSep h.valueFit) ?_
  rintro u ⟨_, frame, rest⟩
  have word (d : Nat) (hd : d + 4 ≤ 72) :
      u.mem.readW (off (State.addr s.sp) d) 32 = s.mem.readW (off (State.addr s.sp) d) 32 :=
    frame.readW (w := 32) (r := ⟨off (State.addr s.sp) d, 4⟩) (Region.contains_self _ _) (by
      intro r hr
      rw [List.mem_singleton] at hr; subst r
      exact h.stackSep.sub_left (Offset.sub_base _ hd)) (by decide)
  refine ⟨u.mem.readW (off (State.addr u.sp) 64) 32,
    h.context.locals.after rest, h.output.after rest, by rw [rest.sp]; exact h.stackSep, ?_, ?_, rfl⟩
  · rw [rest.sp, word 4 (by decide)]; exact h.context.saved 4 h4
  · rw [rest.sp, word 32 (by decide)]; exact h.context.saved 32 h32

theorem exchangeFinish_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d) :
    RelCT isa (fun s t => ExchangeFinishInput p slots s ∧ ExchangeFinishInput p slots t ∧ s.sp = t.sp)
      (.seq (.block VG.Impl.Ffdh.Arm.Domain.Exchange.saveResult)
        (.seq VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult VG.Impl.Ffdh.Arm.Domain.Exchange.maskOutput))
      (fun _ _ => True) := by
  have save := (RelCT.block_append (stackAddr_ct.seq (storeLocal_ct .r11 64))).mono
    (P' := fun (s t : State) => ExchangeFinishInput p slots s ∧ ExchangeFinishInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have exportCT := (exportResult_ct h4 h32).mono
    (P' := fun (s t : State) => ExchangeFinishInput p slots s ∧ ExchangeFinishInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have mask : RelCT isa (fun s t => AnyMaskInput p s ∧ AnyMaskInput p t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.Exchange.maskOutput (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨f1, h1⟩ := h.1
    obtain ⟨f2, h2⟩ := h.2.1
    exact maskOutput_ct s t tr1 tr2 u v ⟨h1, h2, h.2.2⟩ e1 e2
  exact relCT_chain save (fun s h => exchangeSave_ready s h stable saved)
    (fun s h => exchangeSave_ready s h stable saved)
    (relCT_chain exportCT (fun s h => exchangeExport_ready s h h4 h32)
      (fun s h => exchangeExport_ready s h h4 h32) mask)

end VG.Proof.Ffdh.Arm
