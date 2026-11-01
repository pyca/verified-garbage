module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.ExportResult
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ExportResultCT
import VerifiedGarbage.Proof.Ffdh.Arm.MaskOutputCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.MaskOutput
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Proof.Framework.RelCT

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
