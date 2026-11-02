module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquareState
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.MontCallOpCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquare
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquare

/-! Basis squaring follows its public saved row count, independent of residue values. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)

structure SquareInput (p : Inputs) (sp : BitVec 32) (n : Nat) (s : State) : Prop where
  core : Core p sp s
  power : ∃E, Power5 p E s
  counter : SquareCount sp n s

private theorem counter_after_square {p : Inputs} {sp : BitVec 32} {s t : State} {n : Nat}
    (h : Memory p sp s) (counter : SquareCount sp n s)
    (frame : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem) :
    SquareCount sp n t := by
  have localEq : WorkspaceEq (State.addr s.sp) 72 s.mem t.mem := by
    apply WorkspaceEq.of_frame (by decide) frame
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact h.context.locals.separate
    · rw [FrameStack.belowA,FrameStack.addr_sub' h.calls.stack.fit]
      exact (Offset.below_disjoint _ (by decide)).symm
  have word := localEq.word (d:=68) (bits:=32) (by decide)
  rw [h.fixed] at word
  exact word.trans counter

theorem power5_bound {p : Inputs} {sp : BitVec 32} {s : State}
    (h : Core p sp s) (power : ∃E,Power5 p E s) :
    numAt s.mem (State.addr p.base) p.w 5<numAt s.mem (State.addr p.base) p.w 0 := by
  obtain ⟨E,power⟩ := power
  rw [h.modulus,power]
  apply Nat.mod_lt
  have positive := h.memory.ready.modulus
  rw [h.modulus] at positive
  omega

private theorem square_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} {n : Nat} :
    RelCT isa (fun s t => SquareInput p sp n s ∧ SquareInput p sp n t ∧ s.sp=t.sp)
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 5 5 5) (fun _ _ => True) := by
  have operand : Proof.Rsa.Mont.Operand 5 := by
    simp [Proof.Rsa.Mont.Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]
  exact (montCallOp_ct backend.name backend.mul (backend.rawCT operand operand operand) operand operand operand).mono
    (fun _ _ h => ⟨h.1.core.memory.ready,h.2.1.core.memory.ready,h.1.core.memory.calls.stack,
      h.2.1.core.memory.calls.stack,power5_bound h.1.core h.1.power,power5_bound h.2.1.core h.2.1.power,h.2.2⟩)
    (fun _ _ _ => trivial)

private theorem square_post (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {n : Nat}
    (h : SquareInput p sp n s) : WP isa (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 5 5 5) s
      (SquareInput p sp n) := by
  obtain ⟨E,power⟩ := h.power
  refine WP.mono (square5_ok backend s h.core power) ?_
  rintro t ⟨core,power,_,frame,_⟩
  exact ⟨core,⟨2*E,power⟩,counter_after_square h.core.memory h.counter frame⟩

private theorem squaresInit_ct : RelCT isa (fun s t => s.sp=t.sp)
    (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresInit) (fun _ _ => True) :=
  RelCT.block_append ((loadStack_ct .r3 44).seq
    (RelCT.block_append (stackAddr_ct.seq ((storeLocal_ct .r3 68).mono (fun _ _ h => h) (fun _ _ _ => trivial)))))

private theorem squaresNext_ct : RelCT isa (fun s t => s.sp=t.sp)
    (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresNext) (fun _ _ => True) := by
  have sub : RelCT isa (fun s t => s.sp=t.sp) (.block [.subs .r3 .r3 (.imm 1)])
      (fun s t => s.sp=t.sp) := by
    apply relCT_keep_sp _ (fun _ _ h => h)
    apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append ((loadStack_ct .r3 68).seq
    (RelCT.block_append (sub.seq (RelCT.block_append (stackAddr_ct.seq
      ((storeLocal_ct .r3 68).mono (fun _ _ h => h) (fun _ _ _ => trivial)))))))

private theorem squareBody_post (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {n : Nat}
    (positive : 0<n) (fits : n<2^32) (h : SquareInput p sp n s) :
    WP isa (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 5 5 5)
      (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresNext)) s
      (fun t => SquareInput p sp (n-1) t ∧ t.z=decide (n-1=0)) := by
  rw [WP.seq_iff]
  refine WP.mono (square_post backend s h) ?_
  intro u hu
  obtain ⟨E,power⟩ := hu.power
  refine WP.mono (squaresNext_state u hu.core power positive fits hu.counter) ?_
  rintro t ⟨core,power,count,zero,_,_⟩
  exact ⟨⟨core,⟨E,power⟩,count⟩,zero⟩

theorem squares_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32}
    (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p))
    (fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32) :
    RelCT isa (fun s t => (Core p sp s ∧ ∃E,Power5 p E s) ∧
      (Core p sp t ∧ ∃E,Power5 p E t) ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CombPrecompute.squares (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun _ _ => True) := by
  let I := fun n s t => 0<n ∧ n<2^32 ∧ SquareInput p sp n s ∧ SquareInput p sp n t ∧ s.sp=t.sp
  have step : ∀n, RelCT isa (I n)
      (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 5 5 5)
        (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresNext))
      (fun u v => isa.eval .ne u=isa.eval .ne v ∧ (isa.eval .ne u=some false → True) ∧
        (isa.eval .ne u=some true → ∃m<n,I m u v)) := by
    intro n s t tr1 tr2 u v h e1 e2
    have body := relCT_chain (square_ct backend (p:=p) (sp:=sp) (n:=n))
      (fun s h => square_post backend s h) (fun s h => square_post backend s h)
      (squaresNext_ct.mono (fun _ _ h => h.2.2) (fun _ _ h => h))
    obtain ⟨trace,sp'⟩ := relCT_keep_sp body (fun _ _ h => h.2.2) s t tr1 tr2 u v ⟨h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩ e1 e2
    obtain ⟨_,_,run1,left,z1⟩ := squareBody_post backend s h.1 h.2.1 h.2.2.1
    obtain ⟨_,_,run2,right,z2⟩ := squareBody_post backend t h.1 h.2.1 h.2.2.2.1
    obtain ⟨_,rfl⟩ := Exec.det e1 run1
    obtain ⟨_,rfl⟩ := Exec.det e2 run2
    refine ⟨trace,?_,fun _ => trivial,?_⟩
    · change some (!u.z)=some (!v.z)
      rw [z1,z2]
    · intro again
      have nz : n-1≠0 := by
        intro zero
        change some (!u.z)=some true at again
        simp only [z1,zero,decide_true,Bool.not_true,Option.some.injEq,Bool.false_eq_true] at again
      exact ⟨n-1,by omega,by omega,by omega,left,right,sp'⟩
  have init (s : State) (h : Core p sp s ∧ ∃E,Power5 p E s) :
      WP isa (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresInit) s
        (SquareInput p sp (Spec.Rsa.FixedBaseComb.rows (bits p))) := by
    obtain ⟨E,power⟩ := h.2
    refine WP.mono (squaresInit_state s h.1 power) ?_
    rintro t ⟨core,power,count,_,_⟩
    exact ⟨core,⟨E,power⟩,count⟩
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.squares
  exact relCT_chain (squaresInit_ct.mono (fun _ _ h => h.2.2) (fun _ _ h => h)) init init
    ((RelCT.loop I step (Spec.Rsa.FixedBaseComb.rows (bits p))).mono
      (fun _ _ h => ⟨positive,fits,h.1,h.2.1,h.2.2⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.CombBuilder
