module

public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # Public call layout and caller buffers retained across arithmetic stages -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure CallLayout where
  sp : BitVec 32
  base : Addr
  size : Nat
  pLen : Nat
  qLen : Nat
  p : Nat
  q : Nat
  widths : Spec.Dsa.lengthsValid pLen qLen
  extent : usedBytes ≤ size
  inputs : List (Pointer × Nat)
  pointers : Pointer → BitVec 32
  stable : ∀ input ∈ inputs, StablePointer input.1
  /-- The digest prefix the shape check saves: the bytes of the digest reduced. -/
  digestPrefix : Nat

theorem CallLayout.lengths (L : CallLayout) :
    128 ≤ L.pLen ∧ L.pLen ≤ 384 ∧ 20 ≤ L.qLen ∧ L.qLen ≤ 32 ∧ L.qLen ≤ L.pLen := by
  have H := L.widths
  unfold Spec.Dsa.lengthsValid at H
  omega

theorem CallLayout.aligned (L : CallLayout) : L.pLen % 4 = 0 ∧ L.qLen % 4 = 0 := by
  have H := L.widths
  unfold Spec.Dsa.lengthsValid at H
  omega

theorem CallLayout.saved (L : CallLayout) : Layout.saved ≤ L.size := by
  have H : 15712 ≤ L.size := L.extent
  change 8256 ≤ L.size
  omega

structure CallReady (L : CallLayout) (s : State) : Prop where
  sp : s.gpr .esp = L.sp
  moduli : Moduli L.base L.size L.pLen L.qLen L.p L.q s
  buffers : ∀ input ∈ L.inputs, CallerBuffer s L.base L.size input.1 input.2
  pointers : ∀ input ∈ L.inputs, pointerValue L.base s input.1 = L.pointers input.1
  prefixLen : pointerValue L.base s (.input .digestPrefixLen) = BitVec.ofNat 32 L.digestPrefix

def CallPair (L : CallLayout) (s t : State) : Prop := CallReady L s ∧ CallReady L t

theorem CallReady.keep {L : CallLayout} {s t : State} (R : CallReady L s) (E : Execution L.base s t) :
    CallReady L t := by
  refine ⟨(E.keeps.1 .esp (by decide)).trans R.sp, R.moduli.keep E.mem E.keeps (by decide) (by decide), ?_, ?_, ?_⟩
  · intro input hi
    exact E.buffer (R.buffers input hi) (L.stable input hi)
  · intro input hi
    exact (runFrame_pointer E.mem E.keeps (by decide) (L.stable input hi)).trans (R.pointers input hi)
  · exact (runFrame_pointer E.mem E.keeps (by decide) (p := .input .digestPrefixLen) (by decide)).trans R.prefixLen

/-- Caller operands may be shortened to a public prefix; internal operands lie
in the persistent suffix beyond the shared arithmetic context. -/
def CallOperand (L : CallLayout) (p : Pointer) (len : Nat) : Prop :=
  (∃ full, (p, full) ∈ L.inputs ∧ len ≤ full) ∨
  (∃ offset, p = .local offset ∧ r ≤ offset ∧ offset + len ≤ usedBytes)

theorem CallReady.operand {L : CallLayout} {s : State} {p : Pointer} {len n : Nat}
    (R : CallReady L s) (O : CallOperand L p len) (hl : 0 < len) (hn : n ≤ 48) :
    OperandReady s L.base n p len := by
  rcases O with ⟨full, member, le⟩ | ⟨offset, rfl, lo, hi⟩
  · exact ((R.buffers (p, full) member).prefix le).ready (R.moduli.context hn)
  · exact localReady R.moduli.scr hl (Nat.le_trans hi R.moduli.extent)
      (Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn) (Nat.le_trans (by decide : 7048 ≤ r) lo))

theorem CallPair.pointer {L : CallLayout} {s t : State} {p : Pointer} {len : Nat}
    (R : CallPair L s t) (O : CallOperand L p len) : pointerValue L.base s p = pointerValue L.base t p := by
  rcases O with ⟨full, member, _⟩ | ⟨offset, rfl, _, _⟩
  · exact (R.1.pointers (p, full) member).trans (R.2.pointers (p, full) member).symm
  · have G : s.gpr .edi = t.gpr .edi :=
      BitVec.eq_of_toNat_eq (R.1.moduli.scr.edi_toNat.trans R.2.moduli.scr.edi_toNat.symm)
    simp only [pointerValue, G]

theorem call_stage {L : CallLayout} {code : Prog isa} {Q : State → State → Prop}
    (CT : RelCT isa (CallPair L) code Q)
    (W : ∀ s, CallReady L s → WP isa code s (fun t => Execution L.base s t)) :
    RelCT isa (CallPair L) code (CallPair L) := by
  intro s t tr ur sf tf ⟨S, T⟩ E F
  obtain ⟨Trace, _⟩ := CT _ _ _ _ _ _ ⟨S, T⟩ E F
  exact ⟨Trace, S.keep (wp_result (W s S) E), T.keep (wp_result (W t T) F)⟩

end VG.Proof.Dsa.X86
