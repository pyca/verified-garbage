module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductBody
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductLoadCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeControlCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquaresCT
import VerifiedGarbage.Proof.Bignum.Arm.MontCallOpCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductState
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProduct
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductLoad

/-! Each public subset extension loads, multiplies, and exports at fixed public indices. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)

structure ProductBodyInput (p : Inputs) (sp : BitVec 32) (j low : Nat) (s : State) : Prop where
  core : Core p sp s
  power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s
  table : TablePrefix p (2^j+low) s.mem
  count : ProductCount sp (2^j) low s

private structure Loaded (p : Inputs) (sp : BitVec 32) (j low : Nat) (s : State) : Prop where
  core : Core p sp s
  power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s
  count : ProductCount sp (2^j) low s
  selected : numAt s.mem (State.addr p.base) p.w 1=entryValue p low

theorem productBody_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} {j low : Nat}
    (bound : 2^j+low<32) :
    RelCT isa (fun s t => ProductBodyInput p sp j low s ∧ ProductBodyInput p sp j low t ∧ s.sp=t.sp)
      (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
        (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5)
          VG.Impl.Ffdh.Arm.CombPrecompute.productStore)) (fun _ _ => True) := by
  have loaded (s : State) (h : ProductBodyInput p sp j low s) :
      WP isa VG.Impl.Ffdh.Arm.CombPrecompute.productLoad s (Loaded p sp j low) := by
    refine WP.mono (productLoad_ok (low:=low) (count:=2^j+low) s h.core h.power h.table (by omega)
      (by have := Nat.two_pow_pos j; omega) (by rw [h.core.memory.fixed]; exact h.count.2)) ?_
    rintro t ⟨core,power,selected,_,_,frame,_⟩
    have wide : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem := frame.mono (by simp)
    exact ⟨core,power,h.count.after_frame h.core.memory (product_body_arithmetic h.core.memory wide),selected⟩
  let Stored := fun s : State => Memory p sp s ∧
    s.mem.readW (off (State.addr s.sp) 36) 32=BitVec.ofNat 32 (2^j) ∧
    s.mem.readW (off (State.addr s.sp) 40) 32=BitVec.ofNat 32 low
  have multiplied (s : State) (h : Loaded p sp j low s) :
      WP isa (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5) s Stored := by
    refine WP.mono (product6_ok backend s h.core h.power h.selected) ?_
    rintro t ⟨core,_,_,_,frame,_⟩
    have count := h.count.after_frame h.core.memory (product_body_arithmetic h.core.memory frame)
    exact ⟨core.memory,by rw [core.memory.fixed]; exact count.1,by rw [core.memory.fixed]; exact count.2⟩
  have operand (a : Nat) (ha : a=1 ∨ a=5 ∨ a=6) : Spec.Rsa.Mont.Operand a := by
    rcases ha with rfl|rfl|rfl <;> simp [Spec.Rsa.Mont.Operand,Spec.Rsa.Mont.aAcc,Spec.Rsa.Mont.aTmp]
  have op := montCallOp_ct backend.name backend.mul (base:=p.base) (len:=p.len) (w:=p.w)
    (backend.rawCT (operand 6 (by simp)) (operand 1 (by simp)) (operand 5 (by simp)))
    (operand 6 (by simp)) (operand 1 (by simp)) (operand 5 (by simp))
  refine relCT_chain (productLoad_ct.mono
    (fun _ _ h => ⟨⟨h.1.core.memory,by rw [h.1.core.memory.fixed]; exact h.1.count.2⟩,
      ⟨h.2.1.core.memory,by rw [h.2.1.core.memory.fixed]; exact h.2.1.count.2⟩,h.2.2⟩)
    (fun _ _ h => h)) loaded loaded ?_
  exact relCT_chain (op.mono
    (fun _ _ h => ⟨h.1.core.memory.ready,h.2.1.core.memory.ready,h.1.core.memory.calls.stack,
      h.2.1.core.memory.calls.stack,power5_bound h.1.core ⟨_,h.1.power⟩,
      power5_bound h.2.1.core ⟨_,h.2.1.power⟩,h.2.2⟩) (fun _ _ _ => trivial))
    multiplied multiplied productStore_ct

end VG.Proof.Ffdh.Arm.CombBuilder
