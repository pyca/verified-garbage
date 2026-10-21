module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquareState
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquare

/-! The public descending counter performs exactly d shared basis squares. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem square_round_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {E n : Nat}
    (h : Core p sp s) (power : Power5 p E s) (positive : 0<n) (fits : n<2^32)
    (counter : SquareCount sp n s) :
    WP isa (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 5 5 5)
      (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresNext)) s fun t =>
      Core p sp t ∧ Power5 p (2*E) t ∧ SquareCount sp (n-1) t ∧ t.z=decide (n-1=0) ∧
      Frame (squareNarrowWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (square5_ok backend s h power) ?_
  rintro u ⟨core,pow,_keeps,frame,rest⟩
  have preserved : SquareCount sp n u := by
    change u.mem.readW (off (State.addr sp) 68) 32=BitVec.ofNat 32 n
    have sub : (⟨off (State.addr sp) 68,4⟩ : Region).Sub ⟨State.addr sp,72⟩ := Offset.sub_base _ (by decide)
    rw [frame.readW (r:=⟨off (State.addr sp) 68,4⟩) (Region.contains_self _ _) (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact h.memory.context.locals.separate.sub_left (by rw [h.memory.fixed]; exact sub)
      · have fit : 48≤sp.toNat := by rw [←h.memory.fixed]; exact h.memory.calls.stack.fit
        rw [h.memory.fixed,FrameStack.belowA,FrameStack.addr_sub' fit]
        exact ((Offset.below_disjoint _ (by decide : 48+72≤2^64)).symm).sub_left sub) (by decide)]
    exact counter
  refine WP.mono (squaresNext_state u core pow positive fits preserved) ?_
  rintro t ⟨coreT,powT,countT,zero,frameT,restT⟩
  have frameS : Frame (squareNarrowWrites p sp) s.mem u.mem := frame.sub (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact ⟨_,by simp [squareNarrowWrites],fun _ hx => hx⟩
    · rw [h.memory.fixed]
      exact ⟨_,by simp [squareNarrowWrites],fun _ hx => hx⟩)
  exact ⟨coreT,powT,countT,zero,frameS.trans frameT,rest.trans restT⟩

theorem squares_loop_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {E D : Nat}
    (h : Core p sp s) (power : Power5 p E s) (positive : 0<D) (fits : D<2^32)
    (counter : SquareCount sp D s) :
    WP isa (.loop (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 5 5 5)
      (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresNext)) .ne) s fun t =>
      Core p sp t ∧ Power5 p (2^D*E) t ∧ SquareCount sp 0 t ∧
      Frame (squareNarrowWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => 0<k ∧ k≤D ∧ Core p sp t ∧ Power5 p (2^(D-k)*E) t ∧ SquareCount sp k t ∧
    Frame (squareNarrowWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t
  refine WP.loop (M:=isa) I ?_ D s ?_
  · intro k u hu
    obtain ⟨hk,bound,core,pow,count,frame,rest⟩ := hu
    refine WP.mono (square_round_ok backend u core pow hk (by omega) count) ?_
    rintro t ⟨coreT,powT,countT,zero,frameT,restT⟩
    have exponent : 2*(2^(D-k)*E)=2^(D-(k-1))*E := by
      rw [show D-(k-1)=(D-k)+1 by omega,Nat.pow_succ]
      ac_rfl
    rw [exponent] at powT
    by_cases last : k-1=0
    · left
      refine ⟨?_,coreT,?_,?_,frame.trans frameT,rest.trans restT⟩
      · change some (!t.z)=some false
        simp only [zero,last,decide_true,Bool.not_true]
      · simpa only [last,Nat.sub_zero] using powT
      · simpa only [last] using countT
    · right
      refine ⟨?_,k-1,by omega,by omega,by omega,coreT,powT,countT,frame.trans frameT,rest.trans restT⟩
      change some (!t.z)=some true
      simp only [zero,last,decide_false,Bool.not_false]
  · refine ⟨positive,by omega,h,?_,counter,Frame.refl _ _,Rest.refl _ _⟩
    simpa only [Nat.sub_self,Nat.pow_zero,Nat.one_mul] using power

theorem squares_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {E : Nat}
    (h : Core p sp s) (power : Power5 p E s)
    (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p))
    (fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32) :
    WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.squares
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      Core p sp t ∧ Power5 p (2^Spec.Rsa.FixedBaseComb.rows (bits p)*E) t ∧
      WorkspaceEq (State.addr p.output) (bytes p) s.mem t.mem ∧
      Frame (squareNarrowWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.CombPrecompute.squares,WP.seq_iff]
  refine WP.mono (squaresInit_state s h power) ?_
  rintro u ⟨core,pow,count,frame,rest⟩
  refine WP.mono (squares_loop_ok backend u core pow positive fits count) ?_
  rintro t ⟨coreT,powT,_countT,frameT,restT⟩
  have all := frame.trans frameT
  exact ⟨coreT,powT,h.memory.squareNarrowContextEq all,all,rest.trans restT⟩

end VG.Proof.Ffdh.Arm.CombBuilder
