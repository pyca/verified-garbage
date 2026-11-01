module

public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
public import VerifiedGarbage.Proof.Dsa.X86.StreamTiming
public import VerifiedGarbage.Proof.Dsa.X86.CoreReduce
import VerifiedGarbage.Proof.Dsa.X86.CoreReduceTiming
import VerifiedGarbage.Proof.Dsa.X86.StageArithmetic
import VerifiedGarbage.Proof.Dsa.X86.StageValues
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # Streaming reduction stages retain the public call layout -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem CallReady.stream {L : CallLayout} {s : State} {p : Pointer} {len n : Nat}
    (R : CallReady L s) (O : CallOperand L p len) (hl : ∀ o, p = .local o → 0 < len) (hn : n ≤ 48) :
    StreamInput s L.base (contextBytes n) (pointerValue L.base s p) len := by
  rcases O with ⟨full, member, le⟩ | ⟨offset, rfl, lo, hi⟩
  · exact ((R.buffers (p, full) member).prefix le).stream (R.moduli.context hn)
  · exact localStream R.moduli.scr (hl _ rfl) (Nat.le_trans hi R.moduli.extent)
      (Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn) (Nat.le_trans (by decide : 7048 ≤ r) lo))

theorem CallReady.stack {L : CallLayout} {s : State} {p : Pointer} {len : Nat}
    (R : CallReady L s) (O : CallOperand L p len) (hl : ∀ o, p = .local o → 0 < len) :
    Region.Disjoint ⟨(pointerValue L.base s p).setWidth 64, len⟩ (callStack (s.gpr .esp)) := by
  rcases O with ⟨full, member, le⟩ | ⟨offset, rfl, lo, hi⟩
  · exact ((R.buffers (p, full) member).prefix le).stack
  · exact localStack R.moduli.scr R.moduli.room (hl _ rfl) (Nat.le_trans hi R.moduli.extent)

theorem callReduce_relCT (L : CallLayout) (input : Pointer) (src : Src) (len output : Nat) (hf : LenForm src)
    (hsrc : ∀ s, CallReady L s → LenOperand L.base L.size ((L.qLen + 7) / 8) s src len)
    (Q : CallOperand L (.input .q) L.qLen) (I : CallOperand L input len)
    (hl : ∀ o, input = .local o → 0 < len) (hlen : len < 2 ^ 32)
    (ho : r ≤ output) (hb : output + L.qLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Core.reduce L.qLen src input output) (CallPair L) := by
  have W := L.lengths
  have N : (L.qLen + 7) / 8 ≤ 48 := by omega
  have hw4 : L.qLen % 4 = 0 := by have H := L.widths; unfold Spec.Dsa.lengthsValid at H; omega
  have pre (s : State) (R : CallReady L s) : ReductionPre L.base L.size L.qLen len input src s := by
    refine ⟨R.moduli.scr, R.moduli.qReady, R.stream I hl N, hsrc s R, ?_, ?_, R.moduli.room, R.stack I hl, hlen⟩
    · change 255 < operandValue s L.base (.input .q) L.qLen
      rw [R.moduli.qValue]; exact R.moduli.qLarge
    · change operandValue s L.base (.input .q) L.qLen % 2 = 1
      rw [R.moduli.qValue]; exact R.moduli.qOdd
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · apply (coreReduce_relCT L.base L.size L.qLen len output input src hf L.saved L.extent (by omega) (by omega)
      hw4).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨pre s H.1, pre t H.2, H.pointer Q, H.pointer I, H.1.sp.trans H.2.sp.symm⟩
  · intro s R
    exact WP.mono (stageReduce_ok (hsrc s R) R.moduli (R.stream I hl N) (R.stack I hl) hlen ho hb)
      fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

/-- The saved digest prefix, as a length operand. -/
theorem CallReady.prefixOperand {L : CallLayout} {s : State} (R : CallReady L s) :
    LenOperand L.base L.size ((L.qLen + 7) / 8) s Core.digestPrefix L.digestPrefix :=
  LenOperand.prefix L.saved (by have := L.lengths; omega) R.prefixLen

end VG.Proof.Dsa.X86
