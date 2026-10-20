module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductLoopCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProducts
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductInit
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeControlCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquareState
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState

/-! A public basis number fixes the entire subset-product schedule. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

structure ProductsInput (p : Inputs) (sp : BitVec 32) (j : Nat) (s : State) : Prop where
  core : Core p sp s
  power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s
  table : TablePrefix p (2^j+1) s.mem
  high : s.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^j)

theorem products_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} {j : Nat}
    (hj : j<5) (positive : 0<j) :
    RelCT isa (fun s t => ProductsInput p sp j s ∧ ProductsInput p sp j t ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CombPrecompute.products (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun _ _ => True) := by
  have initialized (s : State) (h : ProductsInput p sp j s) :
      WP isa (.block [.mov .r3 (.imm 1),.addSp .r12 0,VG.Impl.Ffdh.Arm.Domain.st .r3 40]) s
        (ProductBodyInput p sp j 1) := by
    refine WP.mono (productsInit_state s h.core h.power h.high) ?_
    rintro t ⟨core,power,high,low,frame,_⟩
    have ctx : WorkspaceEq (State.addr p.output) (bytes p) s.mem t.mem := by
      apply WorkspaceEq.of_frame (by have := h.core.memory.output.fits; omega) frame
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.core.memory.localSeparate.symm.sub_right (Offset.sub_base _ (by decide))
    have table : TablePrefix p (2^j+1) t.mem := by
      intro digit hd
      have highBound : 2^j≤16 := Nat.pow_le_pow_right (n:=2) (i:=j) (j:=4) (by decide) (by omega)
      rw [ctx.read (entryOffset p digit) (8*p.w) (entry_bound p (by omega))]
      exact h.table digit hd
    exact ⟨core,power,table,high,low⟩
  have one : 1<2^j := by
    have lt := Nat.pow_lt_pow_right (by decide : 1<2) positive
    exact lt
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.products
  exact relCT_chain ((controlInit_ct 1 40).mono (fun _ _ h => h.2.2) (fun _ _ h => h))
    initialized initialized (productsLoop_ct backend hj one)

end VG.Proof.Ffdh.Arm.CombBuilder
