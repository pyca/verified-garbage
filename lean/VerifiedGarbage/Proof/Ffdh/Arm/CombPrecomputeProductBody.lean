module

public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductState
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProduct
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductLoad
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductStore

/-! One public subset extension reuses the shared Montgomery helper. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem productBody_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {j low : Nat}
    (h : Core p sp s) (hj : j<5) (hlow : low<2^j)
    (power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s)
    (table : TablePrefix p (2^j+low) s.mem) (bound : 2^j+low<32)
    (count : ProductCount sp (2^j) low s) :
    WP isa (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
      (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5)
        VG.Impl.Ffdh.Arm.CombPrecompute.productStore)) s fun t =>
      Core p sp t ∧ Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
      TablePrefix p (2^j+low+1) t.mem ∧ ProductCount sp (2^j) low t ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productBodyWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  have countBound : 2^j+low≤32 := by omega
  have lowBound : low<2^j+low := by have := Nat.two_pow_pos j; omega
  refine WP.mono (productLoad_ok s h power table countBound lowBound (by rw [h.memory.fixed]; exact count.2)) ?_
  rintro u ⟨coreU,powerU,selected,tableU,ctxU,frameU,restU⟩
  have wideU : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem u.mem :=
    frameU.mono (by intro r hr; have eq := List.mem_singleton.mp hr; subst r; simp)
  have bodyU := product_body_arithmetic h.memory wideU
  have countU := count.after_frame h.memory bodyU
  rw [WP.seq_iff]
  refine WP.mono (product6_ok backend u coreU powerU selected) ?_
  rintro v ⟨coreV,powerV,value,keeps,frameV,restV⟩
  have bodyV := product_body_arithmetic coreU.memory frameV
  have countV := countU.after_frame coreU.memory bodyV
  have tableV := tableU.after_arithmetic coreU.memory countBound frameV
  rw [product_entry_value p hj hlow] at value
  refine WP.mono (productStore_ok v coreV powerV tableV bound value
    (by rw [coreV.memory.fixed]; exact countV.1) (by rw [coreV.memory.fixed]; exact countV.2)) ?_
  rintro t ⟨coreT,powerT,tableT,headerT,frameT,restT⟩
  have bodyT := product_body_store (sp:=sp) bound frameT
  have countT := countV.after_frame coreV.memory bodyT
  have headerV := headEq_arithmetic coreU.memory frameV
  have headerU : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem u.mem := by
    refine ⟨?_⟩
    intro d n hd
    exact ctxU.read d n (by have := bytes_eq p; omega)
  have header : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
    refine ⟨?_⟩
    intro d n hd
    exact (headerT.read d n hd).trans ((headerV.read d n hd).trans (headerU.read d n hd))
  exact ⟨coreT,powerT,tableT,countT,header,bodyU.trans (bodyV.trans bodyT),restU.trans (restV.trans restT)⟩

end VG.Proof.Ffdh.Arm.CombBuilder
