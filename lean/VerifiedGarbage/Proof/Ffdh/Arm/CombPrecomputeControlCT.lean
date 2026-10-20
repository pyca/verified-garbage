module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductStore
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeStoreCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMem
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState

/-! Fixed public counter accesses do not expose the residues being multiplied. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

private theorem add_ct : RelCT isa (fun s t => s.sp=t.sp)
    (.block [.dp .add .r3 .r3 (.reg .r2)]) (fun s t => s.sp=t.sp) := by
  apply relCT_keep_sp _ (fun _ _ h => h)
  apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _
  exact Taint.agree_ofRegs (by simp)

theorem productStore_ct {p : Inputs} {sp : BitVec 32} {high low : Nat} :
    RelCT isa (fun s t =>
      (Memory p sp s ∧ s.mem.readW (off (State.addr s.sp) 36) 32=BitVec.ofNat 32 high ∧
        s.mem.readW (off (State.addr s.sp) 40) 32=BitVec.ofNat 32 low) ∧
      (Memory p sp t ∧ t.mem.readW (off (State.addr t.sp) 36) 32=BitVec.ofNat 32 high ∧
        t.mem.readW (off (State.addr t.sp) 40) 32=BitVec.ofNat 32 low) ∧ s.sp=t.sp)
      VG.Impl.Ffdh.Arm.CombPrecompute.productStore (fun _ _ => True) := by
  have args (s : State) (h : Memory p sp s ∧
      s.mem.readW (off (State.addr s.sp) 36) 32=BitVec.ofNat 32 high ∧
      s.mem.readW (off (State.addr s.sp) 40) 32=BitVec.ofNat 32 low) :
      WP isa (.block [.ldrSp .r3 36,.ldrSp .r2 40,.dp .add .r3 .r3 (.reg .r2)]) s
        (fun t => Memory p sp t ∧ t.gpr .r3=BitVec.ofNat 32 (high+low)) := by
    refine WP.mono (productStoreArgs_ok s h.1.context.locals h.2.1 h.2.2) ?_
    rintro t ⟨⟨index,mem,ptr⟩,rest⟩
    exact ⟨h.1.of_mem mem rest (ptr.trans h.1.ready.ptr),index⟩
  have headCT := RelCT.block_append ((stackLoads_ct [(.r3,36),(.r2,40)]).seq add_ct)
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.productStore
  exact relCT_chain (headCT.mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)) args args
    (store_ct (digit:=high+low) (by decide : 6<8))

private theorem inc_ct : RelCT isa (fun s t => s.sp=t.sp)
    (.block [.dp .add .r3 .r3 (.imm 1)]) (fun s t => s.sp=t.sp) := by
  apply relCT_keep_sp _ (fun _ _ h => h)
  apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _
  exact Taint.agree_ofRegs (by simp)

private theorem cmp_ct : RelCT isa (fun s t => s.sp=t.sp)
    (.block [.cmp .r3 (.reg .r2)]) (fun s t => s.sp=t.sp) := by
  apply relCT_keep_sp _ (fun _ _ h => h)
  apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _
  exact Taint.agree_ofRegs (by simp)

theorem productNext_ct : RelCT isa (fun s t => s.sp=t.sp)
    (.block VG.Impl.Ffdh.Arm.CombPrecompute.productNext) (fun _ _ => True) := by
  have finish := RelCT.block_append ((loadStack_ct .r2 36).seq cmp_ct)
  have store := RelCT.block_append (stackAddr_ct.seq ((storeLocal_ct .r3 40).mono
    (fun _ _ h => h) (fun _ _ h => h.2)))
  exact (RelCT.block_append ((loadStack_ct .r3 40).seq
    (RelCT.block_append (inc_ct.seq (RelCT.block_append (store.seq finish)))))).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem basisNext_ct : RelCT isa (fun s t => s.sp=t.sp)
    (.block VG.Impl.Ffdh.Arm.CombPrecompute.basisNext) (fun _ _ => True) := by
  have double : RelCT isa (fun s t => s.sp=t.sp)
      (.block [.dp .add .r3 .r3 (.reg .r3)]) (fun s t => s.sp=t.sp) := by
    apply relCT_keep_sp _ (fun _ _ h => h)
    apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have compare : RelCT isa (fun _ _ => True) (.block [.cmp .r3 (.imm 32)]) (fun _ _ => True) := by
    apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append ((loadStack_ct .r3 36).seq (RelCT.block_append (double.seq
    (RelCT.block_append (stackAddr_ct.seq (RelCT.block_append (((storeLocal_ct .r3 36).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)).seq compare)))))))


theorem controlInit_ct (value : BitVec 32) (d : Nat) : RelCT isa (fun s t => s.sp=t.sp)
    (.block [.mov .r3 (.imm value),.addSp .r12 0,.str .r3 .r12 d]) (fun _ _ => True) := by
  have mov : RelCT isa (fun s t => s.sp=t.sp) (.block [.mov .r3 (.imm value)])
      (fun s t => s.sp=t.sp) := single_ct (fun _ _ _ => rfl)
        (fun _ _ _ _ h e1 e2 => (exec_sp e1).trans (h.trans (exec_sp e2).symm))
  exact RelCT.block_append (mov.seq (RelCT.block_append (stackAddr_ct.seq
    ((storeLocal_ct .r3 d).mono (fun _ _ h => h) (fun _ _ _ => trivial)))))

theorem basisStore_ct {p : Inputs} {sp : BitVec 32} {high : Nat} :
    RelCT isa (fun s t =>
      (Memory p sp s ∧ s.mem.readW (off (State.addr s.sp) 36) 32=BitVec.ofNat 32 high) ∧
      (Memory p sp t ∧ t.mem.readW (off (State.addr t.sp) 36) 32=BitVec.ofNat 32 high) ∧ s.sp=t.sp)
      (.seq (.block [.ldrSp .r3 36]) (VG.Impl.Ffdh.Arm.CombPrecompute.store 5)) (fun _ _ => True) := by
  have loaded (s : State) (h : Memory p sp s ∧
      s.mem.readW (off (State.addr s.sp) 36) 32=BitVec.ofNat 32 high) :
      WP isa (.block [.ldrSp .r3 36]) s (fun t => Memory p sp t ∧ t.gpr .r3=BitVec.ofNat 32 high) := by
    refine WP.mono (localLoad_ok s .r3 h.1.context.locals (d:=36) (by decide)) ?_
    rintro t ⟨reg,mem,rest⟩
    exact ⟨h.1.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.1.ready.ptr),reg.trans h.2⟩
  exact relCT_chain ((loadStack_ct .r3 36).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial))
    loaded loaded (store_ct (digit:=high) (by decide : 5<8))

end VG.Proof.Ffdh.Arm.CombBuilder
