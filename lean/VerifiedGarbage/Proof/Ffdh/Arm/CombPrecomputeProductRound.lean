module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductBody
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductCounterState
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquareState
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductState

/-! A public subset extension followed by its descending loop measure. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem product_round_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {j low : Nat}
    (h : Core p sp s) (hj : j<5) (hlow : low<2^j)
    (power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s)
    (table : TablePrefix p (2^j+low) s.mem) (bound : 2^j+low<32)
    (count : ProductCount sp (2^j) low s) :
    WP isa (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
      (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5)
        (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productStore
          (.block VG.Impl.Ffdh.Arm.CombPrecompute.productNext)))) s fun t =>
      Core p sp t ∧ Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
      TablePrefix p (2^j+(low+1)) t.mem ∧ ProductCount sp (2^j) (low+1) t ∧
      t.z=decide (low+1=2^j) ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  suffices grouped : WP isa (.seq
      (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
        (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5)
          VG.Impl.Ffdh.Arm.CombPrecompute.productStore))
      (.block VG.Impl.Ffdh.Arm.CombPrecompute.productNext)) s fun t =>
      Core p sp t ∧ Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
      TablePrefix p (2^j+(low+1)) t.mem ∧ ProductCount sp (2^j) (low+1) t ∧
      t.z=decide (low+1=2^j) ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t by
    obtain ⟨trace,t,exec,post⟩ := grouped
    cases exec with
    | seq hab hd =>
      cases hab with
      | seq ha hbc =>
        cases hbc with
        | seq hb hc => exact ⟨_,_,.seq ha (.seq hb (.seq hc hd)),post⟩
  rw [WP.seq_iff]
  refine WP.mono (productBody_ok backend s h hj hlow power table bound count) ?_
  rintro u ⟨core,pow,tableU,countU,headerU,frameU,restU⟩
  have highFit : 2^j<2^32 := Nat.pow_lt_pow_right (by decide) (by omega)
  have lowFit : low+1<2^32 := by omega
  refine WP.mono (productNext_state u core pow lowFit highFit countU.2 countU.1) ?_
  rintro t ⟨coreT,powT,highT,lowT,zero,frameT,restT⟩
  have ctxT := core.memory.controlContextEq (by decide) frameT
  have tableT : TablePrefix p (2^j+(low+1)) t.mem := by
    intro digit hd
    rw [ctxT.read (entryOffset p digit) (8*p.w) (entry_bound p (by omega))]
    apply tableU digit
    omega
  have header : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
    refine ⟨?_⟩
    intro d n hd
    exact (ctxT.read d n (by have := bytes_eq p; omega)).trans (headerU.read d n hd)
  have wholeU : Frame (productWrites p sp) s.mem u.mem := frameU.mono (by intro r hr; simp only [productBodyWrites,List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl|rfl <;> simp [productWrites])
  have wholeT : Frame (productWrites p sp) u.mem t.mem := frameT.sub (by
    intro r hr
    have eq := List.mem_singleton.mp hr
    subst r
    exact ⟨⟨State.addr sp,72⟩,by simp [productWrites],Offset.sub_base _ (by decide)⟩)
  exact ⟨coreT,powT,tableT,⟨highT,lowT⟩,zero,header,wholeU.trans wholeT,restU.trans restT⟩

end VG.Proof.Ffdh.Arm.CombBuilder
