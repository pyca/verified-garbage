module

public import VerifiedGarbage.Impl.Bignum.Arm.CombScan
import VerifiedGarbage.Proof.Bignum.Arm.CombScan
import VerifiedGarbage.Proof.Bignum.Arm.CombScanHead
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.SelectCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Bignum.Arm.CombScan
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Bignum.Arm.CombScanState
meta import VerifiedGarbage.Proof.Bignum.Arm.CombScanState
import VerifiedGarbage.Proof.Bignum.Arm.CombScanBody
meta import VerifiedGarbage.Proof.Bignum.Arm.CombScanBody
meta import VerifiedGarbage.Proof.Bignum.Arm.CombTableState

/-! A full 32-entry scan has no digit-dependent addresses or branches. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombScan
open VG VG.Arm VG.Impl.Bignum.Arm

private theorem next_ct : RelCT isa (fun s t => s.gpr .r0=t.gpr .r0)
    (.block VG.Impl.Bignum.Arm.CombScan.next) (fun _ _ => True) := by
  apply RelCT.taint (A:=taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h)

private theorem init_ct : RelCT isa (fun s t => s.gpr .r0=t.gpr .r0)
    (.block VG.Impl.Bignum.Arm.CombScan.init) (fun _ _ => True) := by
  apply RelCT.taint (A:=taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h)

private theorem selection_ct {base table : BitVec 32} {len w M g N d1 d2 j : Nat} :
    RelCT isa (fun s t => SelectInput base table len w M g N d1 j s ∧
      SelectInput base table len w M g N d2 j t ∧ s.sp=t.sp)
      (.seq selectRow (.block [.ldrSp .r0 0])) (fun _ _ => True) := by
  have row : RelCT isa (fun s t => SelectInput base table len w M g N d1 j s ∧
      SelectInput base table len w M g N d2 j t ∧ s.sp=t.sp) selectRow (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨selectRow_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.p0.trans h.2.1.p0.symm,h.1.p10.trans h.2.1.p10.symm,
        h.1.p12.trans h.2.1.p12.symm,h.1.count.trans h.2.1.count.symm⟩ e1 e2,trivial⟩
  exact ((relCT_keep_sp row (fun _ _ h => h.2.2)).seq (loadStack_ct .r0 0)).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem body_ct {base table : BitVec 32} {len w M g N d1 d2 j : Nat} (hj : j<32) :
    RelCT isa (fun s t => Inv base table len w M g N d1 j s ∧
      Inv base table len w M g N d2 j t ∧ s.sp=t.sp)
      VG.Impl.Bignum.Arm.CombScan.body (fun _ _ => True) := by
  unfold VG.Impl.Bignum.Arm.CombScan.body
  refine relCT_chain
    (scanHead_ct.mono (fun _ _ h => h.1.ready.ptr.trans h.2.1.ready.ptr.symm) (fun _ _ h => h))
    (fun s h => head_ok s h hj) (fun s h => head_ok s h hj) ?_
  apply RelCT.assoc
  exact relCT_chain selection_ct
    (fun s h => selection_ready s h hj) (fun s h => selection_ready s h hj)
    (next_ct.mono (fun _ _ h => h.1.trans h.2.1.symm) (fun _ _ h => h))

theorem loop_ct {base table : BitVec 32} {len w M g N d1 d2 : Nat} :
    RelCT isa (fun s t => Inv base table len w M g N d1 0 s ∧
      Inv base table len w M g N d2 0 t ∧ s.sp=t.sp)
      (.loop VG.Impl.Bignum.Arm.CombScan.body .ne) (fun _ _ => True) := by
  let I := fun k s t => ∃ j, j+k=32 ∧ 0<k ∧ Inv base table len w M g N d1 j s ∧
    Inv base table len w M g N d2 j t ∧ s.sp=t.sp
  have step : ∀ k, RelCT isa (I k) VG.Impl.Bignum.Arm.CombScan.body fun u v =>
      isa.eval .ne u=isa.eval .ne v ∧ (isa.eval .ne u=some false → True) ∧
      (isa.eval .ne u=some true → ∃ m<k, I m u v) := by
    intro k s t tr1 tr2 u v h e1 e2
    obtain ⟨j,total,positive,left,right,sp⟩ := h
    obtain ⟨trace,sp'⟩ := relCT_keep_sp (body_ct (by omega : j<32)) (fun _ _ h => h.2.2)
      s t tr1 tr2 u v ⟨left,right,sp⟩ e1 e2
    obtain ⟨_,_,run1,next1,zero1,_,_,_,_⟩ := body_ok s left (by omega)
    obtain ⟨_,_,run2,next2,zero2,_,_,_,_⟩ := body_ok t right (by omega)
    obtain ⟨_,rfl⟩ := Exec.det e1 run1
    obtain ⟨_,rfl⟩ := Exec.det e2 run2
    refine ⟨trace,?_,fun _ => trivial,?_⟩
    · change some (!u.z)=some (!v.z)
      rw [zero1,zero2]
    · intro again
      have notLast : j+1≠32 := by
        intro last
        change some (!u.z)=some true at again
        simp only [zero1,last,decide_true,Bool.not_true,Option.some.injEq,Bool.false_eq_true] at again
      exact ⟨k-1,by omega,j+1,by omega,by omega,next1,next2,sp'⟩
  exact (RelCT.loop I step 32).mono (fun _ _ h => ⟨0,rfl,by decide,h.1,h.2.1,h.2.2⟩) (fun _ _ h => h)

structure Input (base table : BitVec 32) (len w M g N digit : Nat) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  tableReady : CombTable table w M g N s
  separate : Region.Disjoint ⟨State.addr table,32*(8*w)⟩ ⟨State.addr base,8*len⟩
  digitLt : digit<32
  digitValue : s.mem.readW (VG.Proof.Mont.off (State.addr base) 196) 32=BitVec.ofNat 32 digit
  saved : s.mem.readW (VG.Proof.Mont.off (State.addr base) 232) 32=table

theorem code_ct {base table : BitVec 32} {len w M g N d1 d2 : Nat} :
    RelCT isa (fun s t => Input base table len w M g N d1 s ∧
      Input base table len w M g N d2 t ∧ s.sp=t.sp)
      VG.Impl.Bignum.Arm.CombScan.code (fun _ _ => True) := by
  unfold VG.Impl.Bignum.Arm.CombScan.code
  exact relCT_chain
    (init_ct.mono (fun _ _ h => h.1.ready.ptr.trans h.2.1.ready.ptr.symm) (fun _ _ h => h))
    (fun s h => WP.mono (init_state_ok s h.ready h.tableReady h.separate h.digitLt h.digitValue h.saved) fun _ k => k.1)
    (fun s h => WP.mono (init_state_ok s h.ready h.tableReady h.separate h.digitLt h.digitValue h.saved) fun _ k => k.1)
    loop_ct

end VG.Proof.Bignum.Arm.CombScan
