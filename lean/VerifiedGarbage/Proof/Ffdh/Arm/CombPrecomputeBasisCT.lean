module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeBasis
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductsCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquaresCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeControlCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeBasisStore
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSquares

/-! A public tooth number determines the squares and dense subset extensions. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

structure BasisInput (p : Inputs) (sp : BitVec 32) (j : Nat) (s : State) : Prop where
  core : Core p sp s
  power : Power5 p (2^((j-1)*Spec.Rsa.FixedBaseComb.rows (bits p))) s
  table : TablePrefix p (2^j) s.mem
  high : s.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^j)

private structure Squared (p : Inputs) (sp : BitVec 32) (j : Nat) (s : State) : Prop where
  core : Core p sp s
  power : Power5 p (2^(j*Spec.Rsa.FixedBaseComb.rows (bits p))) s
  table : TablePrefix p (2^j) s.mem
  high : s.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^j)

theorem basis_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} {j : Nat}
    (hj : j<5) (jpositive : 0<j) (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p))
    (fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32) :
    RelCT isa (fun s t => BasisInput p sp j s ∧ BasisInput p sp j t ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CombPrecompute.basis (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun _ _ => True) := by
  have high : 2^j≤16 := Nat.pow_le_pow_right (n:=2) (i:=j) (j:=4) (by decide) (by omega)
  have exponent : 2^Spec.Rsa.FixedBaseComb.rows (bits p)*2^((j-1)*Spec.Rsa.FixedBaseComb.rows (bits p))=
      2^(j*Spec.Rsa.FixedBaseComb.rows (bits p)) := by
    rw [←Nat.pow_add]
    congr 1
    calc
      _ = 1*Spec.Rsa.FixedBaseComb.rows (bits p)+(j-1)*Spec.Rsa.FixedBaseComb.rows (bits p) := by rw [Nat.one_mul]
      _ = (1+(j-1))*Spec.Rsa.FixedBaseComb.rows (bits p) := (Nat.add_mul _ _ _).symm
      _ = _ := by rw [show 1+(j-1)=j by omega]
  have squared (s : State) (h : BasisInput p sp j s) :
      WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.squares (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s
        (Squared p sp j) := by
    refine WP.mono (squares_ok backend s h.core h.power positive fits) ?_
    rintro t ⟨core,power,ctx,frame,_⟩
    rw [exponent] at power
    have table : TablePrefix p (2^j) t.mem := by
      intro digit hd
      rw [ctx.read (entryOffset p digit) (8*p.w) (entry_bound p (by omega))]
      exact h.table digit hd
    exact ⟨core,power,table,(h.core.memory.squareNarrowRead36 frame).trans h.high⟩
  have stored (s : State) (h : Squared p sp j s) :
      WP isa (.seq (.block [.ldrSp .r3 36]) (VG.Impl.Ffdh.Arm.CombPrecompute.store 5)) s (ProductsInput p sp j) := by
    refine WP.mono (basisStore_ok s h.core hj h.power h.table h.high) ?_
    rintro t ⟨core,power,table,saved,_,_,_⟩
    exact ⟨core,power,table,saved⟩
  have products := (relCT_keep_sp (products_ct backend (p:=p) (sp:=sp) hj jpositive) (fun _ _ h => h.2.2)).seq basisNext_ct
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.basis
  refine relCT_chain ((squares_ct backend positive fits).mono
    (fun _ _ h => ⟨⟨h.1.core,⟨_,h.1.power⟩⟩,⟨h.2.1.core,⟨_,h.2.1.power⟩⟩,h.2.2⟩) (fun _ _ h => h))
    squared squared ?_
  apply RelCT.assoc
  exact relCT_chain (basisStore_ct.mono
    (fun _ _ h => ⟨⟨h.1.core.memory,by rw [h.1.core.memory.fixed]; exact h.1.high⟩,
      ⟨h.2.1.core.memory,by rw [h.2.1.core.memory.fixed]; exact h.2.1.high⟩,h.2.2⟩) (fun _ _ h => h))
    stored stored products

end VG.Proof.Ffdh.Arm.CombBuilder
