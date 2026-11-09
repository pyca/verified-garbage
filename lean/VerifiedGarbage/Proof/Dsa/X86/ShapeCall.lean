module

public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
import VerifiedGarbage.Proof.Dsa.X86.ShapeModuli
public import VerifiedGarbage.Proof.Dsa.X86.DispatchTiming
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.ShapeOperands

/-! # Caller operands before and after public shape validation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

structure ShapeCallReady (L : CallLayout) (digestLen : Nat) (s : State) : Prop where
  sp : s.gpr .esp = L.sp
  scr : Scr s L.base L.size
  buffers : ∀ input ∈ L.inputs, CallerBuffer s L.base L.size input.1 input.2
  pointers : ∀ input ∈ L.inputs, pointerValue L.base s input.1 = L.pointers input.1
  pValue : operandValue s L.base (.input .p) L.pLen = L.p
  qValue : operandValue s L.base (.input .q) L.qLen = L.q
  digest : (pointerValue L.base s (.input .digestLen)).toNat = digestLen

structure ShapedCall (L : CallLayout) (digestLen : Nat) (s : State) : Prop where
  ready : CallReady L s
  mask : flagW L.base (Layout.field .mask) s = BitVec.allOnes 32
  prefixLength : (pointerValue L.base s (.input .digestPrefixLen)).toNat = min digestLen (Spec.Dsa.bitLength L.q / 8)

theorem shapeCall_ok {L : CallLayout} {digestLen : Nat} {s : State}
    (R : ShapeCallReady L digestLen s)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    WP isa (Shape.check L.pLen L.qLen) s fun t =>
      t.zf = some (!decide (shapeValid L.p L.q)) ∧
      (shapeValid L.p L.q → ShapedCall L digestLen t) ∧
      Keeps shapeClob s t ∧ Outs L.base shapeRanges s.mem t.mem := by
  refine WP.mono (shapeModuli_ok R.scr L.extent L.widths (R.buffers _ P) (R.buffers _ Q)
    R.pValue R.qValue) fun t ⟨F, Z, M, K, O⟩ => ?_
  refine ⟨Z, ?_, K, O⟩
  intro valid
  obtain ⟨Mt, D⟩ := M valid
  have Pre : (pointerValue L.base t (.input .digestPrefixLen)).toNat = min digestLen (Spec.Dsa.bitLength L.q / 8) := by
    simpa only [R.digest] using D
  refine ⟨⟨(K.1 .esp (by decide)).trans R.sp, Mt, ?_, ?_, ?_⟩, ?_, Pre⟩
  · intro input hi
    exact (R.buffers input hi).keep_shape O K (by decide) (stable input hi)
  · intro input hi
    exact (shapeFrame_pointer O K (by decide) (stable input hi)).trans (R.pointers input hi)
  · apply BitVec.eq_of_toNat_eq
    have := (pointerValue L.base t (.input .digestPrefixLen)).isLt
    rw [Pre, BitVec.toNat_ofNat, hd, Nat.mod_eq_of_lt (by omega)]
  · simpa only [mask32, valid, ite_true] using F

end VG.Proof.Dsa.X86
