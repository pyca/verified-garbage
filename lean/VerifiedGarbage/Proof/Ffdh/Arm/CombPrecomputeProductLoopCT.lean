module

public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductState

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductRound
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeControlCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductLoadCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquaresCT
import VerifiedGarbage.Proof.Bignum.Arm.MontCallOpCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProduct
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductLoad
/-! Subset multiplication visits each public index once before the next basis. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CombPrecomputeProductBodyCT.lean`, which only this module imported.
section

/-! Each public subset extension loads, multiplies, and exports at fixed public indices. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)

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
  have operand (a : Nat) (ha : a=1 ∨ a=5 ∨ a=6) : Proof.Rsa.Mont.Operand a := by
    rcases ha with rfl|rfl|rfl <;> simp [Proof.Rsa.Mont.Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]
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
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm

private theorem productRound_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} {j low : Nat}
    (bound : 2^j+low<32) :
    RelCT isa (fun s t => ProductBodyInput p sp j low s ∧ ProductBodyInput p sp j low t ∧ s.sp=t.sp)
      (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
        (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5)
          (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productStore
            (.block VG.Impl.Ffdh.Arm.CombPrecompute.productNext)))) (fun _ _ => True) := by
  have grouped := (relCT_keep_sp (productBody_ct backend (p:=p) (sp:=sp) bound) (fun _ _ h => h.2.2)).seq productNext_ct
  intro s t tr1 tr2 u v h e1 e2
  cases e1 with
  | seq load1 tail1 =>
    cases tail1 with
    | seq op1 tail1 =>
      cases tail1 with
      | seq store1 next1 =>
        cases e2 with
        | seq load2 tail2 =>
          cases tail2 with
          | seq op2 tail2 =>
            cases tail2 with
            | seq store2 next2 =>
              simpa only [List.append_assoc] using grouped _ _ _ _ _ _ h
                (.seq (.seq load1 (.seq op1 store1)) next1)
                (.seq (.seq load2 (.seq op2 store2)) next2)

theorem productsLoop_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} {j start : Nat}
    (hj : j<5) (hstart : start<2^j) :
    RelCT isa (fun s t => ProductBodyInput p sp j start s ∧ ProductBodyInput p sp j start t ∧ s.sp=t.sp)
      (.loop (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
        (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5)
          (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productStore
            (.block VG.Impl.Ffdh.Arm.CombPrecompute.productNext)))) .ne) (fun _ _ => True) := by
  have high : 2^j≤16 := Nat.pow_le_pow_right (n:=2) (i:=j) (j:=4) (by decide) (by omega)
  let I := fun k s t => ∃low, low+k=2^j ∧ 0<k ∧
    ProductBodyInput p sp j low s ∧ ProductBodyInput p sp j low t ∧ s.sp=t.sp
  have step : ∀k, RelCT isa (I k)
      (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
        (.seq (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5)
          (.seq VG.Impl.Ffdh.Arm.CombPrecompute.productStore
            (.block VG.Impl.Ffdh.Arm.CombPrecompute.productNext))))
      (fun u v => isa.eval .ne u=isa.eval .ne v ∧ (isa.eval .ne u=some false → True) ∧
        (isa.eval .ne u=some true → ∃m<k,I m u v)) := by
    intro k s t tr1 tr2 u v h e1 e2
    obtain ⟨low,parts,positive,left,right,spEq⟩ := h
    have bound : 2^j+low<32 := by omega
    obtain ⟨trace,sp'⟩ := relCT_keep_sp (productRound_ct backend (p:=p) (sp:=sp) bound) (fun _ _ h => h.2.2)
      s t tr1 tr2 u v ⟨left,right,spEq⟩ e1 e2
    obtain ⟨_,_,run1,core1,power1,table1,count1,z1,_,_,_⟩ := product_round_ok backend s
      left.core hj (by omega) left.power left.table bound left.count
    obtain ⟨_,_,run2,core2,power2,table2,count2,z2,_,_,_⟩ := product_round_ok backend t
      right.core hj (by omega) right.power right.table bound right.count
    obtain ⟨_,rfl⟩ := Exec.det e1 run1
    obtain ⟨_,rfl⟩ := Exec.det e2 run2
    refine ⟨trace,?_,fun _ => trivial,?_⟩
    · change some (!u.z)=some (!v.z)
      rw [z1,z2]
    · intro again
      have nz : low+1≠2^j := by
        intro eq
        change some (!u.z)=some true at again
        simp only [z1,eq,decide_true,Bool.not_true,Option.some.injEq,Bool.false_eq_true] at again
      exact ⟨k-1,by omega,low+1,by omega,by omega,
        ⟨core1,power1,table1,count1⟩,⟨core2,power2,table2,count2⟩,sp'⟩
  exact (RelCT.loop I step (2^j-start)).mono
    (fun _ _ h => ⟨start,by omega,by omega,h.1,h.2.1,h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm.CombBuilder
