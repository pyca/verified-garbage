module

public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeBasis
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInitialStore
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableInit
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductState
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeBasisStore

/-! Four runtime basis rounds produce all thirty-two canonical table entries. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem table_loop_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32}
    (h : Core p sp s)
    (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p))
    (fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32)
    (power : Power5 p 1 s) (table : TablePrefix p 2 s.mem)
    (saved : s.mem.readW (off (State.addr sp) 36) 32=2) :
    WP isa (.loop (VG.Impl.Ffdh.Arm.CombPrecompute.basis
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) .ne) s fun t =>
      Core p sp t ∧ TablePrefix p 32 t.mem ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => 0<k ∧ k≤4 ∧ Core p sp t ∧
    Power5 p (2^((4-k)*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
    TablePrefix p (2^(5-k)) t.mem ∧
    t.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^(5-k)) ∧
    WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
    Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t
  refine WP.loop (M:=isa) I ?_ 4 s ?_
  · intro k u hu
    obtain ⟨hk,bound,core,pow,tab,counter,header,frame,rest⟩ := hu
    have prev : 5-k-1=4-k := by omega
    have pow' : Power5 p (2^((5-k-1)*Spec.Rsa.FixedBaseComb.rows (bits p))) u := by rw [prev];exact pow
    refine WP.mono (basis_ok backend u core (by omega) (by omega) positive fits pow' tab counter) ?_
    rintro t ⟨coreT,powT,tableT,countT,zero,headerT,frameT,restT⟩
    have headerAll : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
      refine ⟨?_⟩
      intro d n hd
      exact (headerT.read d n hd).trans (header.read d n hd)
    by_cases last : k=1
    · left
      refine ⟨?_,coreT,?_,headerAll,frame.trans frameT,rest.trans restT⟩
      · change some (!t.z)=some false
        simp only [zero,last,decide_true,Bool.not_true]
      · simpa only [last] using tableT
    · right
      have ne : 5-k≠4 := by omega
      refine ⟨?_,k-1,by omega,by omega,by omega,coreT,?_,?_,?_,headerAll,frame.trans frameT,rest.trans restT⟩
      · change some (!t.z)=some true
        simp only [zero,ne,decide_false,Bool.not_false]
      · simpa only [show 4-(k-1)=5-k by omega] using powT
      · simpa only [show 5-(k-1)=5-k+1 by omega] using tableT
      · simpa only [show 5-(k-1)=5-k+1 by omega] using countT
  · refine ⟨by decide,by decide,h,?_,?_,?_,⟨fun _ _ _ => rfl⟩,Frame.refl _ _,Rest.refl _ _⟩
    · simpa only [Nat.sub_self,Nat.zero_mul,Nat.pow_zero] using power
    · exact table
    · exact saved


theorem table_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32}
    (h : Memory p sp s)
    (modulus : Proof.Rsa.Mont.numAt s.mem (State.addr p.base) p.w 0=p.P)
    (r2 : Proof.Rsa.Mont.numAt s.mem (State.addr p.base) p.w 4=2^(128*p.w)%p.P)
    (odd : p.P%2=1) (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p))
    (fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32) :
    WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.table
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      Core p sp t ∧ TablePrefix p 32 t.mem ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.CombPrecompute.table,WP.seq_iff]
  refine WP.mono (initial_ok backend s h modulus r2 odd) ?_
  rintro u ⟨memory,tab,value,one,modulusU,r2U,headerU,frameU,restU⟩
  have coreU : Core p sp u := ⟨memory,modulusU,odd,r2U,one⟩
  have power : Power5 p 1 u := by
    change _ = _
    rw [value,entryValue]
    have e := VG.Proof.Rsa.FixedBaseComb.exponent_tooth (bits p) 0 (by decide)
    simpa only [Nat.pow_zero,Nat.zero_mul] using congrArg
      (fun E => Spec.Rsa.powMod p.G E p.P * 2^(64*p.w)%p.P) e
  rw [WP.seq_iff]
  refine WP.mono (tableInit_state u coreU power) ?_
  rintro v ⟨coreV,powerV,savedV,frameV,restV⟩
  have ctxV := coreU.memory.controlContextEq (by decide) frameV
  have tableV : TablePrefix p 2 v.mem := by
    intro digit hd
    rw [ctxV.read (entryOffset p digit) (8*p.w) (entry_bound p (by omega))]
    exact tab digit hd
  refine WP.mono (table_loop_ok backend v coreV positive fits powerV tableV savedV) ?_
  rintro t ⟨coreT,tableT,headerT,frameT,restT⟩
  have header : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
    refine ⟨?_⟩
    intro d n hd
    exact (headerT.read d n hd).trans ((ctxV.read d n (by have := bytes_eq p;omega)).trans (headerU.read d n hd))
  have wholeU : Frame (productWrites p sp) s.mem u.mem := frameU.mono (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl <;> simp [productWrites])
  have wholeV : Frame (productWrites p sp) u.mem v.mem := frameV.sub (by
    intro r hr
    have eq := List.mem_singleton.mp hr
    subst r
    exact ⟨⟨State.addr sp,72⟩,by simp [productWrites],Offset.sub_base _ (by decide)⟩)
  exact ⟨coreT,tableT,header,wholeU.trans (wholeV.trans frameT),restU.trans (restV.trans restT)⟩

end VG.Proof.Ffdh.Arm.CombBuilder
