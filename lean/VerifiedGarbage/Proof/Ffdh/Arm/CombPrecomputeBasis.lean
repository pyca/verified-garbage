module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeBasisStore
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProducts
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquares
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductInit
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeControl
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductState
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore

/-! One public basis round fills the next dense half of the comb table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem basis_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {j : Nat}
    (h : Core p sp s) (hj : j<5) (jpositive : 0<j)
    (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p))
    (fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32)
    (power : Power5 p (2^((j-1)*Spec.Rsa.FixedBaseComb.rows (bits p))) s)
    (table : TablePrefix p (2^j) s.mem)
    (saved : s.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^j)) :
    WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.basis
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      Core p sp t ∧ Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
      TablePrefix p (2^(j+1)) t.mem ∧
      t.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^(j+1)) ∧
      t.z=decide (j=4) ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have highBound : 2^j≤16 := Nat.pow_le_pow_right (by decide : 0<2) (by omega : j≤4)
  have nextHigh : 2*2^j=2^(j+1) := by rw [Nat.pow_succ]; ac_rfl
  have stop : (2*2^j=32) ↔ j=4 := by
    have cases : j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
    rcases cases with rfl|rfl|rfl|rfl <;> decide
  have exponent : 2^Spec.Rsa.FixedBaseComb.rows (bits p)*
      2^((j-1)*Spec.Rsa.FixedBaseComb.rows (bits p))=
      2^(j*Spec.Rsa.FixedBaseComb.rows (bits p)) := by
    rw [←Nat.pow_add]
    congr 1
    calc
      _ = 1*Spec.Rsa.FixedBaseComb.rows (bits p)+(j-1)*Spec.Rsa.FixedBaseComb.rows (bits p) := by rw [Nat.one_mul]
      _ = (1+(j-1))*Spec.Rsa.FixedBaseComb.rows (bits p) := (Nat.add_mul _ _ _).symm
      _ = _ := by rw [show 1+(j-1)=j by omega]
  rw [VG.Impl.Ffdh.Arm.CombPrecompute.basis,WP.seq_iff]
  refine WP.mono (squares_ok backend s h power positive fits) ?_
  rintro u ⟨coreU,powerU,ctxU,frameU,restU⟩
  rw [exponent] at powerU
  have tableU : TablePrefix p (2^j) u.mem := by
    intro digit hd
    rw [ctxU.read (entryOffset p digit) (8*p.w) (entry_bound p (by omega))]
    exact table digit hd
  have savedU := (h.memory.squareNarrowRead36 frameU).trans saved
  have squareFrame : Frame (productWrites p sp) s.mem u.mem := frameU.sub (by
    intro r hr
    simp only [squareNarrowWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact ⟨_,by simp [productWrites],fun _ hx => hx⟩
    · exact ⟨⟨State.addr sp,72⟩,by simp [productWrites],Offset.sub_base _ (by decide)⟩
    · exact ⟨_,by simp [productWrites],fun _ hx => hx⟩)
  have grouped : WP isa (.seq
      (.seq (.block [.ldrSp .r3 36]) (VG.Impl.Ffdh.Arm.CombPrecompute.store 5))
      (.seq (VG.Impl.Ffdh.Arm.CombPrecompute.products (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
        (.block VG.Impl.Ffdh.Arm.CombPrecompute.basisNext))) u (fun t =>
      Core p sp t ∧ Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
      TablePrefix p (2^(j+1)) t.mem ∧
      t.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^(j+1)) ∧
      t.z=decide (j=4) ∧ WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t) := by
    rw [WP.seq_iff]
    refine WP.mono (basisStore_ok u coreU hj powerU tableU savedU) ?_
    rintro v ⟨coreV,powerV,tableV,savedV,headV,frameV,restV⟩
    rw [WP.seq_iff]
    refine WP.mono (products_ok backend v coreV hj jpositive powerV tableV savedV) ?_
    rintro w ⟨coreW,powerW,tableW,savedW,headW,frameW,restW⟩
    refine WP.mono (basisNext_state w coreW powerW (by omega) savedW) ?_
    rintro t ⟨coreT,powerT,savedT,zeroT,frameT,restT⟩
    simp only [stop] at zeroT
    rw [nextHigh] at tableW savedT
    have ctxT := coreW.memory.controlContextEq (d:=36) (by decide) (by simpa only [coreW.memory.fixed] using frameT)
    have tableT : TablePrefix p (2^(j+1)) t.mem := by
      intro digit hd
      rw [ctxT.read (entryOffset p digit) (8*p.w) (entry_bound p (by
        rw [←nextHigh] at hd
        omega))]
      exact tableW digit hd
    have header : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
      refine ⟨?_⟩
      intro d n hd
      exact (ctxT.read d n (by rw [bytes_eq]; omega)).trans
        ((headW.read d n hd).trans ((headV.read d n hd).trans (ctxU.read d n (by rw [bytes_eq]; omega))))
    have storeFrame : Frame (productWrites p sp) u.mem v.mem := frameV.mono (by
      intro r hr
      simp only [productBodyWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl <;> simp [productWrites])
    have nextFrame : Frame (productWrites p sp) w.mem t.mem := frameT.sub (by
      intro r hr
      have eq := List.mem_singleton.mp hr
      subst r
      exact ⟨⟨State.addr sp,72⟩,by simp [productWrites],Offset.sub_base _ (by decide)⟩)
    exact ⟨coreT,powerT,tableT,savedT,zeroT,header,
      squareFrame.trans (storeFrame.trans (frameW.trans nextFrame)),
      restU.trans (restV.trans (restW.trans restT))⟩
  obtain ⟨trace,t,run,post⟩ := grouped
  cases run with
  | seq ab c =>
    cases ab with
    | seq a b => exact ⟨_,t,.seq a (.seq b c),post⟩

end VG.Proof.Ffdh.Arm.CombBuilder
