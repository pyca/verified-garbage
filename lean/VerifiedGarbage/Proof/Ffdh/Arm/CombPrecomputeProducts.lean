module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductRound
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductInit
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquareState
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductState

/-! The subset-product runtime loop fills one contiguous half of the table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem products_loop_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {j low : Nat}
    (h : Core p sp s) (hj : j<5) (hlow : low<2^j)
    (power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s)
    (table : TablePrefix p (2^j+low) s.mem)
    (count : ProductCount sp (2^j) low s) :
    WP isa (.loop (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
      (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5)
        (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productStore
          (.block VG.Impl.Ffdh.Arm.CombPrecompute.productNext)))) .ne) s fun t =>
      Core p sp t ∧ Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
      TablePrefix p (2*2^j) t.mem ∧ ProductCount sp (2^j) (2^j) t ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have highBound : 2^j≤16 := by
    have := Nat.pow_le_pow_right (by decide : 0<2) (by omega : j≤4)
    exact this
  let I := fun k t => 0<k ∧ k≤2^j ∧ Core p sp t ∧
    Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
    TablePrefix p (2^j+(2^j-k)) t.mem ∧ ProductCount sp (2^j) (2^j-k) t ∧
    WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
    Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t
  refine WP.loop (M:=isa) I ?_ (2^j-low) s ?_
  · intro k u hu
    obtain ⟨positive,bounded,core,pow,tab,counter,header,frame,rest⟩ := hu
    refine WP.mono (product_round_ok backend u core hj (by omega) pow tab (by omega) counter) ?_
    rintro t ⟨coreT,powT,tableT,countT,zero,headerT,frameT,restT⟩
    have next : 2^j-k+1=2^j-(k-1) := by omega
    rw [next] at tableT countT zero
    have headerAll : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
      refine ⟨?_⟩
      intro d n hd
      exact (headerT.read d n hd).trans (header.read d n hd)
    by_cases last : k-1=0
    · left
      refine ⟨?_,coreT,powT,?_,?_,headerAll,frame.trans frameT,rest.trans restT⟩
      · change some (!t.z)=some false
        simp only [zero,last,Nat.sub_zero,decide_true,Bool.not_true]
      · simpa only [last,Nat.sub_zero,←Nat.two_mul] using tableT
      · simpa only [last,Nat.sub_zero] using countT
    · right
      refine ⟨?_,k-1,by omega,by omega,by omega,coreT,powT,tableT,countT,headerAll,frame.trans frameT,rest.trans restT⟩
      change some (!t.z)=some true
      have neq : 2^j-(k-1)≠2^j := by omega
      simp only [zero,neq,decide_false,Bool.not_false]
  · refine ⟨by omega,by omega,h,power,?_,?_,⟨fun _ _ _ => rfl⟩,Frame.refl _ _,Rest.refl _ _⟩
    · simpa only [Nat.sub_sub_self (by omega : low≤2^j)] using table
    · simpa only [Nat.sub_sub_self (by omega : low≤2^j)] using count


theorem products_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {j : Nat}
    (h : Core p sp s) (hj : j<5) (positive : 0<j)
    (power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s)
    (table : TablePrefix p (2^j+1) s.mem)
    (saved : s.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^j)) :
    WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.products
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      Core p sp t ∧ Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
      TablePrefix p (2*2^j) t.mem ∧
      t.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^j) ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.CombPrecompute.products,WP.seq_iff]
  refine WP.mono (productsInit_state s h power saved) ?_
  rintro u ⟨core,pow,highU,lowU,frameU,restU⟩
  have ctxU := h.memory.controlContextEq (by decide) frameU
  have tableU : TablePrefix p (2^j+1) u.mem := by
    intro digit hd
    rw [ctxU.read (entryOffset p digit) (8*p.w) (entry_bound p (by
      have := Nat.pow_le_pow_right (by decide : 0<2) (by omega : j≤4)
      omega))]
    exact table digit hd
  have oneLow : 1<2^j := by have := Nat.pow_lt_pow_right (by decide : 1<2) positive; exact this
  refine WP.mono (products_loop_ok backend u core hj oneLow pow tableU ⟨highU,lowU⟩) ?_
  rintro t ⟨coreT,powT,tableT,countT,headerT,frameT,restT⟩
  have header : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
    refine ⟨?_⟩
    intro d n hd
    exact (headerT.read d n hd).trans (ctxU.read d n (by have := bytes_eq p; omega))
  have wholeU : Frame (productWrites p sp) s.mem u.mem := frameU.sub (by
    intro r hr
    have eq := List.mem_singleton.mp hr
    subst r
    exact ⟨⟨State.addr sp,72⟩,by simp [productWrites],Offset.sub_base _ (by decide)⟩)
  exact ⟨coreT,powT,tableT,countT.1,header,wholeU.trans frameT,restU.trans restT⟩

end VG.Proof.Ffdh.Arm.CombBuilder
