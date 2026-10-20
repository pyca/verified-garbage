module

public import VerifiedGarbage.Impl.Dsa.X86.SignVerify
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Dsa.X86.BytesTiming
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

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
  have N : n ≤ 48 := by dsimp [n]; omega
  have B := slot_bound (n := n) (i := 5) (by decide)
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have H : 8256 ≤ size := hz
  have fit : slot n 5 + 8 * n ≤ size := by simp only [stride] at B; omega
  unfold SignVerify.writeScalar
  dsimp only
  refine RelCT.seq (M := isa) (R := fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input .out) = pointerValue base t (.input .out)) ?_ ?_
  · intro s t tr ur sf tf ⟨S, T, A, B, P⟩ E F
    have ptr : pointerValue base s (.local input) = pointerValue base t (.local input) := by
      have G := BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
      simp only [pointerValue, G]
    have trace := (coreLoad_relCT n qLen (slot n 5) (.local input) base size hz _ _ _ _ _ _ ⟨S, T, ptr⟩ E F).1
    obtain ⟨_, K1, O1⟩ := wp_result (coreLoad_ok S hz fit h4 (by dsimp [n]; omega) hw4 A.toReadableComponent (A.slot (by decide))) E
    obtain ⟨_, K2, O2⟩ := wp_result (coreLoad_ok T hz fit h4 (by dsimp [n]; omega) hw4 B.toReadableComponent (B.slot (by decide))) F
    exact ⟨trace, S.of_keeps K1 (by decide), T.of_keeps K2 (by decide),
      (pointerValue_keep K1 (by decide) (slotOutside_whole O1 (by decide)) (by omega) (.input .out)).trans
        (P.trans (pointerValue_keep K2 (by decide) (slotOutside_whole O2 (by decide)) (by omega) (.input .out)).symm)⟩
  · refine RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint true)) ?_ (storeComponent_relCT qLen (slot n 5))
    apply RelCT.block_append
    exact RelCT.seq (outputPointer_relCT qLen second base size hz)
      (checkedBlockInvariant (τ' := workspaceTaint true) rfl rfl)

theorem result_relCT :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block SignVerify.result)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl

end VG.Proof.Dsa.X86
