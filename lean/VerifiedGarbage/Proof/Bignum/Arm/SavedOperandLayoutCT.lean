module

public import VerifiedGarbage.Impl.Bignum.Arm.SavedOperand
public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandArgs
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Impl.Bignum.Arm.ImportOperand
import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFnCT
meta import VerifiedGarbage.Impl.Bignum.Arm.ImportOperand
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! ### `Bignum.Arm.ImportOperandLayoutCT`, which only this module used -/

section

/-! # Fixed-array operand imports do not expose operand bytes -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem importOperandLayout_ct {base src : BitVec 32} {len w o k : Nat} (ho : o < 8) :
    RelCT isa (fun s t => LayoutFrameReady base len w s ∧ LayoutFrameReady base len w t ∧
      s.gpr .r4 = src ∧ t.gpr .r4 = src ∧ s.gpr .r6 = BitVec.ofNat 32 k ∧
      t.gpr .r6 = BitVec.ofNat 32 k ∧ s.sp = t.sp) (importOperand o) (fun _ _ => True) := by
  let P := fun (s t : State) => LayoutFrameReady base len w s ∧ LayoutFrameReady base len w t ∧
    s.gpr .r4 = src ∧ t.gpr .r4 = src ∧ s.gpr .r6 = BitVec.ofNat 32 k ∧
    t.gpr .r6 = BitVec.ofNat 32 k ∧ s.sp = t.sp
  have args : RelCT isa P (.block [.mov .r2 (.imm (BitVec.ofNat 32 o))]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) (h : LayoutFrameReady base len w s) (source : s.gpr .r4 = src)
      (count : s.gpr .r6 = BitVec.ofNat 32 k) :
      WP isa (.block [.mov .r2 (.imm (BitVec.ofNat 32 o))]) s (LoadFnReady base src len w o k) := by
    have enc : ∀ i : Fin 8, encodable (BitVec.ofNat 32 i.val) = true := by decide
    refine wp_mov (op2_imm (enc ⟨o, ho⟩)) fun t a => WP.block_nil ?_
    refine ⟨⟨h.workspace.congr a.wr, ?_, ?_, (a.other .r0 (by decide)).trans h.ptr, a.gpr⟩,
      (a.other .r4 (by decide)).trans source, (a.other .r6 (by decide)).trans count⟩
    · rw [a.mem]; exact h.layout
    · rw [a.mem]; exact h.width
  have ready := (relCT_keep_sp args (fun _ _ h => h.2.2.2.2.2.2)).wp
    (fun s t h => ⟨wp s h.1 h.2.2.1 h.2.2.2.2.1, wp t h.2.1 h.2.2.2.1 h.2.2.2.2.2.1⟩)
  exact ready.seq ((loadBEFn_ct ho).mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))

end VG.Proof.Bignum.Arm

end

end

/-! # Saved private operand imports reveal no source bytes -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem savedOperandLayout_ct {base src : BitVec 32} {len w k ps cs o : Nat} {bs1 bs2 : List Byte} (ho : o < 8) :
    RelCT isa (fun s t => (LayoutFrameReady base len w s ∧ SavedOperand base src len k ps cs bs1 s) ∧
      (LayoutFrameReady base len w t ∧ SavedOperand base src len k ps cs bs2 t) ∧ s.sp = t.sp)
      (savedOperand o ps cs) (fun _ _ => True) := by
  let P := fun (s t : State) => (LayoutFrameReady base len w s ∧ SavedOperand base src len k ps cs bs1 s) ∧
    (LayoutFrameReady base len w t ∧ SavedOperand base src len k ps cs bs2 t) ∧ s.sp = t.sp
  let Q := fun s : State => LayoutFrameReady base len w s ∧ s.gpr .r4 = src ∧ s.gpr .r6 = BitVec.ofNat 32 k
  have args : RelCT isa P (.block (savedOperandArgs ps cs)) (fun s t => s.sp = t.sp) :=
    (stackLoads_ct [(.r4, ps), (.r6, cs)]).mono (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (s : State) {bs : List Byte} (h : LayoutFrameReady base len w s)
      (source : SavedOperand base src len k ps cs bs s) : WP isa (.block (savedOperandArgs ps cs)) s Q := by
    refine WP.mono (savedOperandArgs_ok s source) ?_
    rintro t ⟨ptr, count, mem, rest⟩
    exact ⟨h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr), ptr, count⟩
  have ready := args.wp (fun s t h => ⟨wp s h.1.1 h.1.2, wp t h.2.1.1 h.2.1.2⟩)
  exact ready.seq ((importOperandLayout_ct ho).mono (fun _ _ h =>
    ⟨h.2.1.1, h.2.2.1, h.2.1.2.1, h.2.2.2.1, h.2.1.2.2, h.2.2.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
