module

public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.RegistersCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.Arm.Isa
meta import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

/-! ### `Ffdh.Arm.KeyArgsCT`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.KeyOutputs`, which the modules that import this one used -/

section

/-! The two caller-owned key encodings are disjoint from arithmetic, domain,
and local stack storage. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

structure KeyOutputs (p : Inputs) (s : State) : Prop where
  privateBuffer : OutputBuffer p.privateValue p.k s
  publicBuffer : OutputBuffer p.publicValue p.k s
  privateDomain : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.privateValue, p.k⟩
  publicDomain : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.publicValue, p.k⟩
  privateStack : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.privateValue, p.k⟩
  publicStack : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.publicValue, p.k⟩
  privateWorkspace : Region.Disjoint ⟨State.addr p.privateValue, p.k⟩ ⟨State.addr p.base, 8 * p.len⟩
  publicWorkspace : Region.Disjoint ⟨State.addr p.publicValue, p.k⟩ ⟨State.addr p.base, 8 * p.len⟩
  separate : Region.Disjoint ⟨State.addr p.privateValue, p.k⟩ ⟨State.addr p.publicValue, p.k⟩

theorem KeyOutputs.after {p : Inputs} {s t : State} {rs : List Reg}
    (h : KeyOutputs p s) (rest : Rest rs s t) : KeyOutputs p t :=
  ⟨h.privateBuffer.after rest, h.publicBuffer.after rest, h.privateDomain, h.publicDomain,
    by rw [rest.sp]; exact h.privateStack, by rw [rest.sp]; exact h.publicStack,
    h.privateWorkspace, h.publicWorkspace, h.separate⟩

end VG.Proof.Ffdh.Arm

end

end

/-! Fixed local-frame accesses used by native key generation have public addresses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem keyScalarArgs_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalarArgs) (fun _ _ => True) := by
  have derive : RelCT isa (fun _ _ => True)
      (.block [.dp .sub .lr .lr (.reg .r3), .dp .add .r3 .r0 (.reg .lr)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _; exact Taint.agree_ofRegs (by simp)
  have save : RelCT isa (fun s t => s.gpr .r12 = t.gpr .r12 ∧ s.sp = t.sp)
      (.block [.str .r3 .r12 16, .mov .r2 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r12]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact h.1)
  change RelCT isa _ (.block ([.ldrSp .r0 40, .ldrSp .r1 48, .ldrSp .lr 32, .ldrSp .r3 20] ++
    [.dp .sub .lr .lr (.reg .r3), .dp .add .r3 .r0 (.reg .lr)] ++ [.addSp .r12 0] ++
    [.str .r3 .r12 16, .mov .r2 (.imm 0)])) _
  have middle := relCT_keep_sp (derive.mono (fun _ _ _ => trivial) (fun _ _ h => h)) (fun _ _ h => h)
  exact RelCT.block_append ((RelCT.block_append ((RelCT.block_append
    ((stackLoads_ct [(.r0, 40), (.r1, 48), (.lr, 32), (.r3, 20)]).seq middle)).seq stackAddr_ct)).seq save)

theorem keyClearArgs_ct (slot : Nat) : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.ldrSp .r0 slot, .ldrSp .lr 32, .mov .r2 (.imm 0)]) (fun _ _ => True) := by
  have zero : RelCT isa (fun _ _ => True) (.block [.mov .r2 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _; exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append ((stackLoads_ct [(.r0, slot), (.lr, 32)]).seq
    (zero.mono (fun _ _ _ => trivial) (fun _ _ h => h)))

theorem keyMaskArgs_ct (slot : Nat) : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.ldrSp .r0 slot, .ldrSp .lr 32, .ldrSp .r3 64, .mov .r2 (.imm 0), .dp .sub .r2 .r2 (.reg .r3)])
    (fun _ _ => True) := by
  have mask : RelCT isa (fun _ _ => True) (.block [.mov .r2 (.imm 0), .dp .sub .r2 .r2 (.reg .r3)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _; exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append ((stackLoads_ct [(.r0, slot), (.lr, 32), (.r3, 64)]).seq
    (mask.mono (fun _ _ _ => trivial) (fun _ _ h => h)))

theorem keyFinishStatus_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.ldrSp .r3 64, .mov .r0 (.imm 3), .dp .sub .r0 .r0 (.shifted .r3 .lsl 1)]) (fun _ _ => True) := by
  have result : RelCT isa (fun _ _ => True)
      (.block [.mov .r0 (.imm 3), .dp .sub .r0 .r0 (.shifted .r3 .lsl 1)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _; exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append ((loadStack_ct .r3 64).seq (result.mono (fun _ _ _ => trivial) (fun _ _ h => h)))

end VG.Proof.Ffdh.Arm

end

end

/-! The scalar byte loops depend on public pointers and counts; the byte
mask and copied entropy values do not affect their traces. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem keyPrefix_ct : RelCT isa (fun s t => RegistersEqual [.r0, .lr] s t)
    (VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero .lr
      (.loop (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.prefixStep) .ne)) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .lr]) _ (by taint_decide)
  intro s t h; exact Taint.agree_ofRegs h

theorem keyZeros_ct : RelCT isa (fun s t => RegistersEqual [.r0, .lr] s t)
    VG.Impl.Ffdh.Arm.Domain.GenerateKey.zeros (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .lr]) _ (by taint_decide)
  intro s t h; exact Taint.agree_ofRegs h

theorem keyCopy_ct : RelCT isa (fun s t => RegistersEqual [.r0, .r1, .lr] s t)
    (VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero .lr VG.Impl.Bignum.Arm.copyBytes) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1, .lr]) _ (by taint_decide)
  intro s t h; exact Taint.agree_ofRegs h

theorem keyFirst_ct : RelCT isa (fun s t => RegistersEqual [.r0, .r1] s t ∧ s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.first) (fun _ _ => True) := by
  have load : RelCT isa (fun s t => RegistersEqual [.r0, .r1] s t ∧ s.sp = t.sp)
      (.block [.ldrb .r2 .r1 0]) (fun s t => RegistersEqual [.r0] s t ∧ s.sp = t.sp) := by
    apply registers_keep_ct [.r0] ?_ (fun _ _ h r hr => h.1 r (by simp only [List.mem_singleton] at hr; subst r; simp))
      (fun _ _ h => h.2) (by intro r hr i hi; simp only [instrs, List.mem_singleton] at hr hi; subst r; subst i; rfl) (by rfl)
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r1]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (fun r hr => h.1 r (by simp only [List.mem_singleton] at hr; subst r; simp))
  have maskLoad : RelCT isa (fun s t => RegistersEqual [.r0] s t ∧ s.sp = t.sp)
      (.block [.ldrSp .r3 68]) (fun s t => RegistersEqual [.r0] s t ∧ s.sp = t.sp) := by
    apply registers_keep_ct [.r0] ((loadStack_ct .r3 68).mono (fun _ _ h => h.2) (fun _ _ _ => trivial))
      (fun _ _ h => h.1) (fun _ _ h => h.2)
      (by intro r hr i hi; simp only [instrs, List.mem_singleton] at hr hi; subst r; subst i; rfl) (by rfl)
  have store : RelCT isa (fun s t => RegistersEqual [.r0] s t ∧ s.sp = t.sp)
      (.block [.dp .and .r2 .r2 (.reg .r3), .strb .r2 .r0 0,
        .dp .add .r0 .r0 (.imm 1), .dp .add .r1 .r1 (.imm 1)]) (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp ?_ (fun _ _ h => h.2)
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h; exact Taint.agree_ofRegs h.1
  have sub : RelCT isa (fun _ _ => True) (.block [.dp .sub .lr .lr (.imm 1)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _; exact Taint.agree_ofRegs (by simp)
  change RelCT isa _ (.block ([.ldrb .r2 .r1 0] ++ [.ldrSp .r3 68] ++
    [.dp .and .r2 .r2 (.reg .r3), .strb .r2 .r0 0, .dp .add .r0 .r0 (.imm 1), .dp .add .r1 .r1 (.imm 1)] ++
    [.ldrSp .lr 20] ++ [.dp .sub .lr .lr (.imm 1)])) _
  exact RelCT.block_append ((RelCT.block_append ((RelCT.block_append ((RelCT.block_append (load.seq maskLoad)).seq store)).seq
    (loadStack_ct .lr 20))).seq (sub.mono (fun _ _ _ => trivial) (fun _ _ h => h)))

end VG.Proof.Ffdh.Arm
