module

public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
import VerifiedGarbage.Proof.Dsa.X86.ShapeModuli
public import VerifiedGarbage.Proof.Dsa.X86.DispatchTiming
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.ShapeOperands
public import VerifiedGarbage.Impl.Dsa.X86.SignVerify
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
import VerifiedGarbage.Proof.Dsa.X86.WriteScalar
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Dsa.X86.BytesTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `Dsa.X86.SignatureTiming`, which the modules that import this one used -/

section

/-! ### `Dsa.X86.OutputTiming`, which this module and modules that import it used -/

section

/-! # Masked signature stores reveal only public addresses -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem outputPointer_relCT (qLen : Nat) (second : Bool) (base : Addr) (size : Nat)
    (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input .out) = pointerValue base t (.input .out))
      (.block (SignVerify.outputPointer qLen second)) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold SignVerify.outputPointer
  apply RelCT.block_append
  refine RelCT.seq (pointer_relCT (.input .out) base size hz) ?_
  cases second
  · exact RelCT.block_nil (fun _ _ h => h)
  · apply checkedBlockInvariant (τ' := { workspaceTaint true with flags := true }) ?_ rfl
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
    change taint.checkBlock (workspaceTaint true) [.alu .add .esi (.imm 0)] = _
    rfl

theorem writeScalar_relCT (qLen input : Nat) (second : Bool) (base : Addr) (size : Nat)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ qLen) (hmax : qLen ≤ 32) (hw4 : qLen % 4 = 0) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      OperandReady s base ((qLen + 7) / 8) (.local input) qLen ∧
      OperandReady t base ((qLen + 7) / 8) (.local input) qLen ∧
      pointerValue base s (.input .out) = pointerValue base t (.input .out))
      (SignVerify.writeScalar qLen input second) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  let n := (qLen + 7) / 8
  have N : n ≤ 48 := by dsimp [n]; omega_using [hmax]
  have B := slot_bound (n := n) (i := 5) (by decide)
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have H : 8256 ≤ size := hz
  have fit : slot n 5 + 8 * n ≤ size := by simp only [stride] at B; omega_using [B, C, H]
  unfold SignVerify.writeScalar
  dsimp only
  refine RelCT.seq (M := isa) (R := fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input .out) = pointerValue base t (.input .out)) ?_ ?_
  · intro s t tr ur sf tf ⟨S, T, A, B, P⟩ E F
    have ptr : pointerValue base s (.local input) = pointerValue base t (.local input) := by
      have G := BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
      simp only [pointerValue, G]
    have trace := (coreLoad_relCT n qLen (slot n 5) (.local input) base size hz _ _ _ _ _ _ ⟨S, T, ptr⟩ E F).1
    obtain ⟨_, K1, O1⟩ := wp_result (coreLoad_ok S hz fit h4 (by dsimp [n]; omega_using []) hw4 A.toReadableComponent (A.slot (by decide))) E
    obtain ⟨_, K2, O2⟩ := wp_result (coreLoad_ok T hz fit h4 (by dsimp [n]; omega_using []) hw4 B.toReadableComponent (B.slot (by decide))) F
    exact ⟨trace, S.of_keeps K1 (by decide), T.of_keeps K2 (by decide),
      (pointerValue_keep K1 (by decide) (slotOutside_whole O1 (by decide)) (by omega_using [C]) (.input .out)).trans
        (P.trans (pointerValue_keep K2 (by decide) (slotOutside_whole O2 (by decide)) (by omega_using [C]) (.input .out)).symm)⟩
  · refine RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint true)) ?_ (storeComponent_relCT qLen (slot n 5))
    apply RelCT.block_append
    exact RelCT.seq (outputPointer_relCT qLen second base size hz)
      (checkedBlockInvariant (τ' := workspaceTaint true) rfl rfl)

theorem result_relCT :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block SignVerify.result)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl

end VG.Proof.Dsa.X86

end

end

/-! # Constant-time release of a complete masked signature -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure SignatureReady (L : CallLayout) (out : BitVec 32) (s : State) : Prop where
  moduli : Moduli L.base L.size L.pLen L.qLen L.p L.q s
  mask : ∃ accepted : Bool, flagW L.base (Layout.field .mask) s = if accepted then BitVec.allOnes 32 else 0
  pointer : pointerValue L.base s (.input .out) = out
  fits : out.toNat + 2 * L.qLen ≤ 2 ^ 32
  write : ∀ e k, e + k ≤ 2 * L.qLen → InRegions s.wr (out.setWidth 64 + BitVec.ofNat 64 e) k
  apart : Region.Disjoint ⟨L.base, L.size⟩ ⟨out.setWidth 64, 2 * L.qLen⟩

theorem signatureFirst_frame {L : CallLayout} {out : BitVec 32} {s0 : State} (R : SignatureReady L out s0) :
    WP isa (SignVerify.writeScalar L.qLen r false) s0 fun s1 =>
      Scr s1 L.base L.size ∧ pointerValue L.base s1 (.input .out) = out ∧
      OperandReady s1 L.base ((L.qLen + 7) / 8) (.local s) L.qLen := by
  have W := L.lengths
  let n := (L.qLen + 7) / 8
  have N : n ≤ 48 := by dsimp [n]; omega_using [W]
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have B := slot_bound (n := n) (i := 5) (by decide)
  simp only [stride] at B
  have hctx := R.moduli.context N
  have slotSub : Region.Sub ⟨off L.base (slot n 5), 8 * n⟩ ⟨L.base, L.size⟩ := Offset.sub_base L.base (by omega_using [B, hctx])
  have firstSub : Region.Sub ⟨out.setWidth 64, L.qLen⟩ ⟨out.setWidth 64, 2 * L.qLen⟩ := by
    simpa only [BitVec.add_zero] using Offset.sub_base (out.setWidth 64) (d := 0) (by omega_using [] : 0 + L.qLen ≤ 2 * L.qLen)
  have A1 := R.apart.sub_right firstSub
  obtain ⟨accepted, mask⟩ := R.mask
  refine WP.mono (writeScalar_ok R.moduli.scr L.saved rfl (by omega_using [W]) (by omega_using [W]) L.aligned.2 hctx
    (R.moduli.scalarReady (by decide) N) false accepted mask (by simpa using R.pointer.symm)
    (by have := R.fits; omega_using [this]) (by intro e k h; exact R.write e k (by omega_using [h])) (A1.sub_left slotSub)) fun s1 ⟨_, K, F⟩ => ?_
  have Frame : OutputFrame L.base (out.setWidth 64) (contextBytes n) L.qLen s0.mem s1.mem := F
  have Scr1 := R.moduli.scr.of_keeps K (by decide)
  refine ⟨Scr1, ?_, localReady Scr1 (by omega_using [W]) (Nat.le_trans (R.moduli.scalarFit (by decide)) L.extent) ?_⟩
  · change s1.mem.readW (off L.base (Layout.field .out)) 32 = out
    rw [Frame.scratch_word A1 (by change contextBytes n ≤ 8224; omega_using [C])
      (by have H : 8256 ≤ L.size := L.saved; change 8228 ≤ L.size; omega_using [H])
      (by have := R.moduli.scr.nowrap; omega_using [this])]
    exact R.pointer
  · change contextBytes n ≤ 14752
    omega_using [C]

theorem writeSignature_relCT (L : CallLayout) (out : BitVec 32) :
    RelCT isa (fun s t => SignatureReady L out s ∧ SignatureReady L out t)
      (.seq (SignVerify.writeScalar L.qLen r false) (SignVerify.writeScalar L.qLen s true))
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  have W := L.lengths
  refine RelCT.seq (M := isa) (R := fun s t => Scr s L.base L.size ∧ Scr t L.base L.size ∧
    OperandReady s L.base ((L.qLen + 7) / 8) (.local VG.Impl.Dsa.Layout.s) L.qLen ∧
    OperandReady t L.base ((L.qLen + 7) / 8) (.local VG.Impl.Dsa.Layout.s) L.qLen ∧
    pointerValue L.base s (.input .out) = pointerValue L.base t (.input .out)) ?_
    (writeScalar_relCT L.qLen s true L.base L.size L.saved (by omega_using [W]) (by omega_using [W]) L.aligned.2)
  intro s t tr ur sf tf ⟨S, T⟩ E F
  have A := S.moduli.scalarReady (d := r) (by decide) (by omega_using [W] : (L.qLen + 7) / 8 ≤ 48)
  have B := T.moduli.scalarReady (d := r) (by decide) (by omega_using [W] : (L.qLen + 7) / 8 ≤ 48)
  have trace := (writeScalar_relCT L.qLen r false L.base L.size L.saved (by omega_using [W]) (by omega_using [W]) L.aligned.2
    _ _ _ _ _ _ ⟨S.moduli.scr, T.moduli.scr, A, B, S.pointer.trans T.pointer.symm⟩ E F).1
  obtain ⟨Scr1, P1, R1⟩ := wp_result (signatureFirst_frame S) E
  obtain ⟨Scr2, P2, R2⟩ := wp_result (signatureFirst_frame T) F
  exact ⟨trace, Scr1, Scr2, R1, R2, P1.trans P2.symm⟩

end VG.Proof.Dsa.X86

end

end

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
    rw [Pre, BitVec.toNat_ofNat, hd, Nat.mod_eq_of_lt (by omega_using [Pre])]
  · simpa only [mask32, valid, ite_true] using F

end VG.Proof.Dsa.X86
