module

import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Divstep.Bound
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Divstep.Bound
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Divstep.WordBasic
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyFinish
meta import VerifiedGarbage.Proof.Divstep.Iter
meta import VerifiedGarbage.Proof.Divstep.WordBasic
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
meta import VerifiedGarbage.Proof.Mont.AArch64.RowInit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.OptimizeK
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine
meta import VerifiedGarbage.Proof.Weierstrass.Pow
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyCheck
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
import VerifiedGarbage.Proof.Weierstrass.MulContract
meta import VerifiedGarbage.Impl.Ecdh.P256.AArch64
meta import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
meta import VerifiedGarbage.Proof.Divstep.Batch
meta import VerifiedGarbage.Proof.Divstep.Incl
meta import VerifiedGarbage.Proof.Divstep.Tc
meta import VerifiedGarbage.Proof.Divstep.Word
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.AArch64.Blocks
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
meta import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
meta import VerifiedGarbage.Proof.Mont.AArch64.Rounds
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Kernel
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyCheck
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.InvRed
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.InvWords
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
meta import VerifiedGarbage.Proof.Weierstrass.JacMul
meta import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.Proof.Divstep.Alg
meta import VerifiedGarbage.Proof.Divstep.Alg
import Mathlib.Algebra.GroupWithZero.Nat
meta import Mathlib.Algebra.GroupWithZero.Nat
public import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.AArch64.Words
meta import VerifiedGarbage.Proof.Mont.AArch64.Words
public import Init.Data.BitVec.BasicAux
meta import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
meta import Init.Data.Int.Basic
public import VerifiedGarbage.TCB.Mem
meta import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Impl.Mont.Mod
meta import VerifiedGarbage.Impl.Mont.Mod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.InvAllocated
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvBatchStart
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvBatch
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyFinish
import VerifiedGarbage.Proof.Divstep.Iter
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.InvAllocated
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.InvBatchStart
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.InvBatch
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import Mathlib.Algebra.Ring.Int.Defs
meta import Mathlib.Data.Nat.Cast.Order.Basic
meta import Mathlib.Tactic.Linarith
meta import Mathlib.Tactic.Positivity
meta import Mathlib.Tactic.Ring
meta import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
meta import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
meta import VerifiedGarbage.Proof.Weierstrass.InverseContract
meta import VerifiedGarbage.Proof.Weierstrass.InvToM
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.LinearCombination

/-! ### `Weierstrass.AArch64.InvEarlyAllocatedMain`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.AArch64.InvEarlyAllocated`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdsa.Verify.AArch64.P256Allocated (inverseBatch)

abbrev invAllocatedCfg := p256.invN

def invAllocatedRegs : List Reg := .x19::allocatedRegs

def invAllocatedBatchW : List (Nat × Nat) := batchW invAllocatedCfg ++ [(7104,576)]

def invAllocatedW : List (Nat × Nat) := invW invAllocatedCfg ++ [(7104,576)]

private theorem wp_both {c : Prog isa} {s : State} {P Q : State → Prop}
    (hp : WP isa c s P) (hq : WP isa c s Q) : WP isa c s fun t => P t ∧ Q t := by
  obtain ⟨tr,t,ht,hp⟩ := hp
  obtain ⟨tr',t',ht',hq⟩ := hq
  obtain ⟨rfl,rfl⟩ := ht.det ht'
  exact ⟨_,_,ht,hp,hq⟩

private theorem word_values {m m' : Mem} {base : Addr} {a n : Nat}
    (h : ∀ i<n,word m base (a+8*i)=word m' base (a+8*i)) :
    wordsVal m base a n=wordsVal m' base a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [wordsVal]
    rw [show word m base a=word m' base a by simpa only [Nat.mul_zero,Nat.add_zero] using h 0 (by omega_arith)]
    rw [ih (a:=a+8) (fun i hi => by rw [show a+8+8*i=a+8*(i+1) by omega_arith]; exact h (i+1) (by omega_arith))]

 theorem invAllocated_update_clob : ∀ r∈Forward.InvAllocated.optimized.flatMap Forward.instrClob,
    r∈allocatedRegs := by
  rw [Forward.InvAllocated.rightCode.lit_eq]
  decide +kernel

 theorem invAllocated_update_writes : ∀ w∈Forward.InvAllocated.optimized.flatMap Forward.instrWrites,
    ∃ w'∈invAllocatedBatchW,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2 := by
  rw [Forward.InvAllocated.rightCode.lit_eq]
  decide +kernel

/-- Allocating the update preserves the divstep invariant, delta and loop counter;
only the explicit allocator spill area and register set widen the internal frame. -/
theorem invAllocated_batch_ok {base : Addr} {size m : Nat} (hsize : 8192≤size)
    (hL : InvLay invAllocatedCfg size) {s : State} (hs : Scr s base size)
    (hM : ModOkA invAllocatedCfg.M size m s.mem base) {I : Divstep.IState}
    (hI : IInv invAllocatedCfg base I s)
    (hd : |I.d|≤2^30) (hf1 : I.f%2=1) (hf : |I.f|≤m) (hg : |I.g|≤m)
    (ha : |I.a|≤m) (hb : |I.b|≤m) {j : Nat} (hj : 1≤j) (hj' : j<2^64)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa inverseBatch s fun t =>
      IInv invAllocatedCfg base (Divstep.batch 59 m invAllocatedCfg.M.minv.toNat I) t ∧
      t.gpr .x19=BitVec.ofNat 64 (j-1) ∧
      KeepRegs invAllocatedRegs s t ∧ Unch base invAllocatedBatchW s.mem t.mem := by
  have hb0 := batch_ok hL hs hM hI hd hf1 hf hg ha hb hj hj' h19
  have hw := words_ok hL hs hI hd hf1 hj hj' h19
  rw [InvCfg.batch] at hb0
  rw [VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.inverseBatch]
  refine WP.seq (WP.mono (wp_both (WP.seq_iff.mp hb0) hw) fun a ⟨qa,wa⟩ => ?_)
  refine WP.seq (WP.mono (wp_both (WP.seq_iff.mp qa) wa) fun b ⟨qb,wb⟩ => ?_)
  obtain ⟨bd,bu,bv,bq,br,b19,bmem,bkeep⟩ := wb
  have hsb := hs.of_keepRegs bkeep (by decide)
  refine WP.mono (Forward.InvAllocated.refine hsb hsize qb) fun t ⟨u,qu,hu,kt,ut⟩ => ?_
  obtain ⟨iu,u19,ku,uu⟩ := qu
  have heq : ∀ a∈[invAllocatedCfg.sF,invAllocatedCfg.sG,invAllocatedCfg.sA,invAllocatedCfg.sB],
      ∀ n≤5,wordsVal t.mem base a n=wordsVal u.mem base a n := by
    intro a ha n hn
    change a∈[2272,2312,2352,2384] at ha
    apply word_values
    intro i hi
    apply hu
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> change _<7104 ∨ 7680≤_ <;> left <;> omega_arith
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> omega_arith
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> omega_arith
  have hnot1 : Reg.x1∉Forward.InvAllocated.optimized.flatMap Forward.instrClob :=
    fun hr => (Forward.InvAllocated.keepsDeltaCounter _ hr).1 rfl
  have hnot19 : Reg.x19∉Forward.InvAllocated.optimized.flatMap Forward.instrClob :=
    fun hr => (Forward.InvAllocated.keepsDeltaCounter _ hr).2 rfl
  refine ⟨⟨?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  · rw [kt.gpr _ hnot1]
    simpa only [Divstep.batch] using bd
  · rw [heq _ (by simp) _ (by decide)]; exact iu.f
  · rw [heq _ (by simp) _ (by decide)]; exact iu.g
  · rw [heq _ (by simp) _ (by decide)]; exact iu.a
  · rw [heq _ (by simp) _ (by decide)]; exact iu.b
  · rw [kt.gpr _ hnot19]; exact b19
  · exact (bkeep.mono (by decide)).trans (kt.mono fun r hr => List.mem_cons_of_mem _ (invAllocated_update_clob r hr))
  · have h := ut.cover invAllocated_update_writes
    rw [bmem] at h
    exact h

/-- The inversion modulus lies outside both the arithmetic workspace and allocator spills. -/
theorem invAllocated_mod {base : Addr} {size m : Nat} {s t : State}
    (hs : Scr s base size) (hM : ModOkA invAllocatedCfg.M size m s.mem base)
    (hU : Unch base invAllocatedBatchW s.mem t.mem) : ModOkA invAllocatedCfg.M size m t.mem base := by
  refine ⟨hM.n0,hM.n10,hM.mo,hM.tmp,hM.sep,?_,hM.inv,hM.red, hM.call⟩
  rw [hU.wordsVal (by decide) (by omega_using [hM.mo,hs.nowrap])]
  exact hM.val

 theorem invAllocated_batch_frame {base : Addr} {s t : State}
    (hU : Unch base invAllocatedBatchW s.mem t.mem) : Unch base invAllocatedW s.mem t.mem := by
  apply hU.cover
  decide

 theorem invAllocated_loop_ok {base : Addr} {size m B : Nat} (hsize : 8192≤size)
    (hL : InvLay invAllocatedCfg size) {s : State} (hs : Scr s base size)
    (hM : ModOkA invAllocatedCfg.M size m s.mem base) {X : Nat} (hX : X<m)
    (hm2 : m%2=1) (hm1 : 1<m) (hB1 : 1≤B) (hB : B<2^16)
    (hI : IInv invAllocatedCfg base (Divstep.invRun 59 m invAllocatedCfg.M.minv.toNat X 0) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 B) :
    WP isa (.loop inverseBatch (.nonzero .x .x19)) s fun t =>
      IInv invAllocatedCfg base (Divstep.invRun 59 m invAllocatedCfg.M.minv.toNat X B) t ∧
      KeepRegs invAllocatedRegs s t ∧ Unch base invAllocatedBatchW s.mem t.mem := by
  have hmi : ((m : Int)*(invAllocatedCfg.M.minv.toNat : Int)+1)%2^64=0 := by exact_mod_cast hM.inv
  refine countLoop_ok (n:=B) (by omega_arith)
    (Inv:=fun j t => IInv invAllocatedCfg base (Divstep.invRun 59 m invAllocatedCfg.M.minv.toNat X (B-j)) t ∧
      t.gpr .x19=BitVec.ofNat 64 j ∧ Scr t base size ∧ ModOkA invAllocatedCfg.M size m t.mem base ∧
      KeepRegs invAllocatedRegs s t ∧ Unch base invAllocatedBatchW s.mem t.mem)
    (fun j t hj1 hjB ⟨it,xt,st,mt,kt,ut⟩ => ?_)
    (fun t ⟨it,_,_,_,kt,ut⟩ => ⟨by simpa only [Nat.sub_zero] using it,kt,ut⟩)
    hB1 ⟨by rw [Nat.sub_self]; exact hI,h19,hs,hM,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Unch.refl _ _ _⟩
  obtain ⟨bd,bf1,bf,bg,ba0,ba1,bb0,bb1⟩ := Divstep.invRun_bounds (N:=59) (by decide)
    (p:=m) (m:=invAllocatedCfg.M.minv.toNat) (x:=X) (by exact_mod_cast hm2)
    (by exact_mod_cast hm1) hmi (by omega_arith) (by exact_mod_cast hX) (B-j)
  refine WP.mono (invAllocated_batch_ok hsize hL st mt it (by
    have hh : ((59*(B-j) : Nat) : Int)≤59*2^16 := by exact_mod_cast (Nat.mul_le_mul_left 59 (by omega_arith : B-j≤2^16))
    omega_arith) bf1 bf bg (by rw [abs_of_nonneg ba0]; exact ba1.le)
    (by rw [abs_of_nonneg bb0]; exact bb1.le) hj1 (by omega_arith) xt)
    fun u ⟨iu,xu,ku,uu⟩ => ⟨⟨?_,xu,st.of_keepRegs ku (by decide),invAllocated_mod st mt uu,
      kt.trans ku,fun x hx => (uu x hx).trans (ut x hx)⟩,xu⟩
  rw [show B-(j-1)=B-j+1 by omega_arith]
  exact iu

end VG.Proof.Weierstrass.AArch64

end

end

/-! ### `Weierstrass.AArch64.InvEarly`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- The early finish differs only in its actual batch count and scaling constants. -/
def earlyCfg (P : InvCfg) (B m : Nat) : InvCfg :=
  let c := 2^(5*B)*(2^(64*P.M.n))^3 % m
  {P with B:=B,C:=c,Cn:=m-c}

theorem IInv.of_keeps {P : InvCfg} {base : Addr} {I : Divstep.IState} {s t : State}
    (hI : IInv P base I s) {rs : List Reg} (h : Keeps rs s t) (h1 : .x1∉rs) : IInv P base I t :=
  ⟨by rw [h.gpr _ h1]; exact hI.d, by rw [h.mem]; exact hI.f,
    by rw [h.mem]; exact hI.g, by rw [h.mem]; exact hI.a, by rw [h.mem]; exact hI.b⟩

theorem IInv.of_earlyCfg {P : InvCfg} {B m : Nat} {base : Addr} {I : Divstep.IState} {s : State}
    (h : IInv (earlyCfg P B m) base I s) : IInv P base I s := ⟨h.d,h.f,h.g,h.a,h.b⟩

theorem IInv.earlyCfg {P : InvCfg} {base : Addr} {I : Divstep.IState} {s : State}
    (h : IInv P base I s) (B m : Nat) : IInv (earlyCfg P B m) base I s := ⟨h.d,h.f,h.g,h.a,h.b⟩

theorem InvLay.earlyCfg {P : InvCfg} {size : Nat} (hL : InvLay P size) (B m : Nat) :
    InvLay (earlyCfg P B m) size := by
  exact ⟨hL.n4,hL.n10,hL.acc,hL.base,hL.tbl,hL.acc8,hL.base8,hL.tbl8,hL.mod,
    hL.acc_base,hL.acc_tbl,hL.base_tbl,hL.acc_tmp,hL.tbl_tmp,hL.mo_acc,hL.mo_tbl,hL.mo_tmp,hL.base_mo⟩

end VG.Proof.Weierstrass.AArch64

end

end


@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdsa.Verify.AArch64.P256Allocated (inverseBatch inverseNine inverseCheck)

abbrev invAllocatedModulus := p256.C.n

def invAllocatedTail : Prog isa :=
  .seq (.block inverseCheck) <|
    .ite (.nonzero .x .x2)
      (.seq (.block [.movz .x .x19 1 0]) (.seq inverseBatch (.block invAllocatedCfg.finish)))
      (.block inverseNine.finish)

def invAllocatedBody : Prog isa :=
  .seq (.block inverseNine.init)
    (.seq (.loop inverseBatch (.nonzero .x .x19)) invAllocatedTail)

 theorem invAllocated_powClob : ∀ r∈powClob invAllocatedCfg.M.n,r∈invAllocatedRegs := by decide

 theorem invAllocated_original_frame {base : Addr} {s t : State}
    (hU : Unch base (invW invAllocatedCfg) s.mem t.mem) : Unch base invAllocatedW s.mem t.mem := by
  apply hU.cover
  decide

 theorem invAllocated_odd (_hp : invAllocatedModulus.Prime) : invAllocatedModulus%2=1 := by decide

 theorem invAllocated_nine_pos : 0<inverseNine.C := by decide +kernel

 theorem invAllocated_nine_eq : inverseNine=earlyCfg invAllocatedCfg 9 invAllocatedModulus := rfl

/-- Correctness of the public early-exit tail after register allocation. -/
theorem invAllocated_tail_ok {base : Addr} {size X : Nat} [NeZero invAllocatedModulus]
    (hsize : 8192≤size) (hpr : invAllocatedModulus.Prime) (hT : InvToM invAllocatedModulus)
    (hL : InvLay invAllocatedCfg size) (hR : UnitMod invAllocatedModulus (2^256))
    {s : State} (hs : Scr s base size)
    (hM : ModOkA invAllocatedCfg.M size invAllocatedModulus s.mem base)
    (hX : X<invAllocatedModulus) (hC : InvOk invAllocatedCfg invAllocatedModulus)
    (hI : IInv invAllocatedCfg base (Divstep.invRun 59 invAllocatedModulus invAllocatedCfg.M.minv.toNat X 9) s) :
    WP isa invAllocatedTail s fun t =>
      KeepRegs invAllocatedRegs s t ∧ Unch base invAllocatedW s.mem t.mem ∧
      wordsVal t.mem base invAllocatedCfg.acc 4<invAllocatedModulus ∧
      toM invAllocatedModulus (2^256) (wordsVal t.mem base invAllocatedCfg.acc 4)=
        toM invAllocatedModulus (2^256) X ^ (invAllocatedModulus-2) := by
  have hm2 : 2<invAllocatedModulus := by decide
  have hm2' := invAllocated_odd hpr
  have hmi : ((invAllocatedModulus : Int)*(invAllocatedCfg.M.minv.toNat : Int)+1)%2^64=0 := by exact_mod_cast hM.inv
  obtain ⟨bd,bf1,bf,bg,ba0,ba1,bb0,bb1⟩ := Divstep.invRun_bounds (N:=59) (by decide)
    (p:=invAllocatedModulus) (m:=invAllocatedCfg.M.minv.toNat) (x:=X)
    (by exact_mod_cast hm2') (by exact_mod_cast hpr.one_lt) hmi (by omega_using []) (by exact_mod_cast hX) 9
  rw [invAllocatedTail]
  refine WP.seq (WP.mono (earlyCheck_ok hs (n:=5) (a:=2312) (by decide) (by omega_using [hsize]) (by decide))
    fun a ⟨az,ka⟩ => ?_)
  have ha := hs.of_keeps ka (by decide)
  have ia := hI.of_keeps ka (by decide)
  have ma : ModOkA invAllocatedCfg.M size invAllocatedModulus a.mem base := by rw [ka.mem]; exact hM
  have kap : KeepRegs invAllocatedRegs s a := (Keeps.regs ka).mono (by decide)
  have eval : isa.eval (.nonzero .x .x2) a=some (decide (wordsVal s.mem base 2312 5≠0)) := by
    change some (a.read .x .x2 != 0)=_
    rw [read_x]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne,decide_eq_true_eq,ne_eq,az]
  apply WP.ite _ eval
  · intro _
    refine WP.seq (WP.mono (movzI_ok a .x19 1) fun b ⟨b19,kb⟩ => ?_)
    have hb := ha.of_keeps kb (by decide)
    have ib := ia.of_keeps kb (by decide)
    have mb : ModOkA invAllocatedCfg.M size invAllocatedModulus b.mem base := by rw [kb.mem]; exact ma
    refine WP.seq (WP.mono (invAllocated_batch_ok hsize hL hb mb ib (by norm_num at bd ⊢; omega_using [bd])
      bf1 bf bg (by rw [abs_of_nonneg ba0]; exact ba1.le) (by rw [abs_of_nonneg bb0]; exact bb1.le)
      (j:=1) (by decide) (by decide) b19) fun c ⟨ic,_,kc,uc⟩ => ?_)
    have ic' : IInv invAllocatedCfg base
        (Divstep.invRun 59 invAllocatedModulus invAllocatedCfg.M.minv.toNat X 10) c := ic
    have done : (Divstep.invRun 59 invAllocatedModulus invAllocatedCfg.M.minv.toNat X 10).g=0 := by
      have hd := (Divstep.invRun_dfg (N:=59) (p:=(invAllocatedModulus:Int))
        (m:=invAllocatedCfg.M.minv.toNat) (x:=X) (by exact_mod_cast hm2') 10).1
      have hz := (Divstep.divsteps_590 (by exact_mod_cast hm2') (by omega_using [] : (0:Int)≤X)
        (by exact_mod_cast hX.le) (by decide : (invAllocatedModulus:Int)≤2^256) (by decide : 590≤59*10)).1
      rw [←hd] at hz
      exact hz
    refine WP.mono (finish_early_ok hpr hT hL hm2 hR (hb.of_keepRegs kc (by decide))
      (invAllocated_mod hb mb uc) hX ic' done hC.C hC.Cpos hC.Cn) fun t ⟨kt,ut,lt,et⟩ =>
      ⟨(kap.trans ((Keeps.regs kb).mono (by decide))).trans (kc.trans (kt.mono invAllocated_powClob)),?_,lt,et⟩
    intro x hx
    rw [(invAllocated_original_frame ut) x hx,(invAllocated_batch_frame uc) x hx,kb.mem,ka.mem]
  · intro hz
    have hw : wordsVal s.mem base 2312 5=0 := by simpa only [ne_eq,decide_eq_false_iff_not,not_not] using hz
    have hg := hI.g_zero_of_words (lt_of_le_of_lt bg (by decide +kernel : (invAllocatedModulus:Int)<(2^(64*invAllocatedCfg.L):Nat))) hw
    have hl9 : InvLay inverseNine size := by rw [invAllocated_nine_eq]; exact hL.earlyCfg _ _
    refine WP.mono (finish_early_ok hpr hT hl9 hm2 hR ha ma hX (ia.earlyCfg 9 invAllocatedModulus) hg
      rfl invAllocated_nine_pos rfl) fun t ⟨kt,ut,lt,et⟩ =>
      ⟨kap.trans (kt.mono invAllocated_powClob),?_,lt,et⟩
    intro x hx
    rw [(invAllocated_original_frame ut) x hx,ka.mem]

/-- Full value and explicit spill/register frames for the allocated inverse body. -/
theorem invAllocated_body_ok {base : Addr} {size : Nat} [NeZero invAllocatedModulus]
    (hsize : 8192≤size) (hpr : invAllocatedModulus.Prime) (hT : InvToM invAllocatedModulus)
    (hL : InvLay invAllocatedCfg size) (hR : UnitMod invAllocatedModulus (2^256))
    {s : State} (hs : Scr s base size)
    (hM : ModOkA invAllocatedCfg.M size invAllocatedModulus s.mem base)
    (hX : wordsVal s.mem base invAllocatedCfg.base 4<invAllocatedModulus)
    (hC : InvOk invAllocatedCfg invAllocatedModulus) :
    WP isa invAllocatedBody s fun t =>
      KeepRegs invAllocatedRegs s t ∧ Unch base invAllocatedW s.mem t.mem ∧
      wordsVal t.mem base invAllocatedCfg.acc 4<invAllocatedModulus ∧
      toM invAllocatedModulus (2^256) (wordsVal t.mem base invAllocatedCfg.acc 4)=
        toM invAllocatedModulus (2^256) (wordsVal s.mem base invAllocatedCfg.base 4) ^ (invAllocatedModulus-2) := by
  have hl9 : InvLay inverseNine size := by rw [invAllocated_nine_eq]; exact hL.earlyCfg _ _
  rw [invAllocatedBody]
  refine WP.seq (WP.mono (init_ok hl9 hs hM (by decide)) fun a ⟨ia,a19,ka,ua⟩ => ?_)
  have ua' : Unch base invAllocatedBatchW s.mem a.mem := ua.cover (by decide)
  have ha := hs.of_keepRegs ka (by decide)
  have ma := invAllocated_mod hs hM ua'
  have ia' := IInv.of_earlyCfg (P:=invAllocatedCfg) (B:=9) (m:=invAllocatedModulus) ia
  refine WP.seq (WP.mono (invAllocated_loop_ok hsize hL ha ma hX (invAllocated_odd hpr)
    hpr.one_lt (B:=9) (by decide) (by decide) ia' a19)
    fun b ⟨ib,kb,ub⟩ => ?_)
  refine WP.mono (invAllocated_tail_ok hsize hpr hT hL hR (ha.of_keepRegs kb (by decide))
    (invAllocated_mod ha ma ub) hX hC ib) fun t ⟨kt,ut,lt,et⟩ =>
      ⟨(ka.mono (by decide)).trans (kb.trans kt),?_,lt,et⟩
  intro x hx
  rw [ut x hx,(invAllocated_batch_frame ub) x hx,(invAllocated_batch_frame ua') x hx]

end VG.Proof.Weierstrass.AArch64

end

end

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdsa.Verify.AArch64.P256Allocated (inverseBatch inverseNine inverseCheck)

def invAllocatedPrefix : Prog isa :=
  .seq (.block inverseNine.init) (.loop inverseBatch (.nonzero .x .x19))

def invAllocatedCheckedPrefix : Prog isa := .seq invAllocatedPrefix (.block inverseCheck)

def invAllocatedLast : Prog isa :=
  .seq (.block [.movz .x .x19 1 0]) (.seq inverseBatch (.block invAllocatedCfg.finish))

macro "inv_fixed_ct" : tactic => `(tactic|
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide))

 theorem invAllocated_prefix_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) invAllocatedCheckedPrefix := by inv_fixed_ct

 theorem invAllocated_last_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) invAllocatedLast := by inv_fixed_ct

 theorem invAllocated_finish_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (.block inverseNine.finish) := by inv_fixed_ct

/-- Exact word equality follows from the invariant's signed residue representation. -/
theorem IInv.g_words_eq {P : InvCfg} {base : Addr} {I : Divstep.IState} {s t : State}
    (hs : IInv P base I s) (ht : IInv P base I t) :
    wordsVal s.mem base P.sG P.L=wordsVal t.mem base P.sG P.L := by
  have es := hs.g
  have et := ht.g
  rw [Int.emod_eq_of_lt (by omega_using []) (by exact_mod_cast wordsVal_lt s.mem base P.sG P.L)] at es
  rw [Int.emod_eq_of_lt (by omega_using []) (by exact_mod_cast wordsVal_lt t.mem base P.sG P.L)] at et
  exact_mod_cast es.trans et.symm

 theorem invAllocated_prefix_ok {base : Addr} {size X : Nat}
    (hsize : 8192≤size) (hpr : invAllocatedModulus.Prime) (hL : InvLay invAllocatedCfg size)
    {s : State} (hs : Scr s base size)
    (hM : ModOkA invAllocatedCfg.M size invAllocatedModulus s.mem base)
    (hX : X<invAllocatedModulus) (hval : wordsVal s.mem base invAllocatedCfg.base 4=X) :
    WP isa invAllocatedPrefix s fun t =>
      Scr t base size ∧ IInv invAllocatedCfg base
        (Divstep.invRun 59 invAllocatedModulus invAllocatedCfg.M.minv.toNat X 9) t ∧
      KeepRegs invAllocatedRegs s t := by
  have hl9 : InvLay inverseNine size := by rw [invAllocated_nine_eq]; exact hL.earlyCfg _ _
  rw [invAllocatedPrefix]
  refine WP.seq (WP.mono (init_ok hl9 hs hM (by decide)) fun a ⟨ia,a19,ka,ua⟩ => ?_)
  have ua' : Unch base invAllocatedBatchW s.mem a.mem := ua.cover (by decide)
  have ha := hs.of_keepRegs ka (by decide)
  have ma := invAllocated_mod hs hM ua'
  have ia' := IInv.of_earlyCfg (P:=invAllocatedCfg) (B:=9) (m:=invAllocatedModulus) ia
  change IInv invAllocatedCfg base ⟨1,invAllocatedModulus,wordsVal s.mem base invAllocatedCfg.base 4,0,1⟩ a at ia'
  rw [hval] at ia'
  refine WP.mono (invAllocated_loop_ok hsize hL ha ma hX (invAllocated_odd hpr)
      hpr.one_lt (B:=9) (by decide) (by decide) ia' a19) fun t ⟨it,kt,_⟩ =>
      ⟨ha.of_keepRegs kt (by decide),it,(ka.mono (by decide)).trans kt⟩

 theorem invAllocated_checked_prefix_ok {base : Addr} {size X : Nat}
    (hsize : 8192≤size) (hpr : invAllocatedModulus.Prime) (hL : InvLay invAllocatedCfg size)
    {s : State} (hs : Scr s base size)
    (hM : ModOkA invAllocatedCfg.M size invAllocatedModulus s.mem base)
    (hX : X<invAllocatedModulus) (hval : wordsVal s.mem base invAllocatedCfg.base 4=X) :
    WP isa invAllocatedCheckedPrefix s fun t => ∃ u,
      IInv invAllocatedCfg base (Divstep.invRun 59 invAllocatedModulus invAllocatedCfg.M.minv.toNat X 9) u ∧
      (t.gpr .x2=0 ↔ wordsVal u.mem base invAllocatedCfg.sG invAllocatedCfg.L=0) ∧
      KeepRegs invAllocatedRegs s t := by
  rw [invAllocatedCheckedPrefix]
  refine WP.seq (WP.mono (invAllocated_prefix_ok hsize hpr hL hs hM hX hval) fun u ⟨hu,iu,ku⟩ => ?_)
  exact WP.mono (earlyCheck_ok hu (n:=5) (a:=2312) (by decide) (by omega_using [hsize]) (by decide))
    fun t ⟨eq,kt⟩ => ⟨u,iu,eq,ku.trans ((Keeps.regs kt).mono (by decide))⟩

/-- The canonical public signature scalar determines whether the tenth batch runs. -/
theorem invAllocated_body_relCT {base : Addr} {size X : Nat} [NeZero invAllocatedModulus]
    (hsize : 8192≤size) (hpr : invAllocatedModulus.Prime) (hT : InvToM invAllocatedModulus)
    (hL : InvLay invAllocatedCfg size) (hR : UnitMod invAllocatedModulus (2^256))
    (hX : X<invAllocatedModulus) (hC : InvOk invAllocatedCfg invAllocatedModulus) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ s.sp=t.sp ∧
      ModOkA invAllocatedCfg.M size invAllocatedModulus s.mem base ∧
      ModOkA invAllocatedCfg.M size invAllocatedModulus t.mem base ∧
      wordsVal s.mem base invAllocatedCfg.base 4=X ∧ wordsVal t.mem base invAllocatedCfg.base 4=X)
      invAllocatedBody (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  let Pre := fun s t : State => Scr s base size ∧ Scr t base size ∧ s.sp=t.sp ∧
      ModOkA invAllocatedCfg.M size invAllocatedModulus s.mem base ∧
      ModOkA invAllocatedCfg.M size invAllocatedModulus t.mem base ∧
      wordsVal s.mem base invAllocatedCfg.base 4=X ∧ wordsVal t.mem base invAllocatedCfg.base 4=X
  have hpub : ∀ s t,Pre s t → AArch64.Taint.Agree (Taint.ofRegs [.x0]) s t := by
    intro s t hp
    refine ⟨hp.2.2.1,?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
    subst r
    exact hp.1.x0.trans hp.2.1.x0.symm
  let Post := fun s t : State => AArch64.Taint.Agree (Taint.ofRegs [.x0]) s t ∧ (s.gpr .x2=0 ↔ t.gpr .x2=0)
  have hc : RelCT isa Pre invAllocatedCheckedPrefix Post := by
    intro s t ts tt s' t' hp es et
    obtain ⟨_,_,xs,u,iu,zu,ku⟩ := invAllocated_checked_prefix_ok hsize hpr hL hp.1 hp.2.2.2.1 hX hp.2.2.2.2.2.1
    obtain ⟨_,_,xt,v,iv,zv,kv⟩ := invAllocated_checked_prefix_ok hsize hpr hL hp.2.1 hp.2.2.2.2.1 hX hp.2.2.2.2.2.2
    obtain ⟨_,rfl⟩ := es.det xs
    obtain ⟨_,rfl⟩ := et.det xt
    refine ⟨invAllocated_prefix_ct _ _ _ _ _ _ trivial trivial (hpub s t hp) es et,?_,?_⟩
    · refine ⟨ku.sp.trans (hp.2.2.1.trans kv.sp.symm),?_⟩
      intro r hr
      simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
      subst r
      rw [ku.gpr _ (by decide),kv.gpr _ (by decide)]
      exact hp.1.x0.trans hp.2.1.x0.symm
    · rw [zu,zv,iu.g_words_eq iv]
  have hb : RelCT isa Post (.ite (.nonzero .x .x2) invAllocatedLast (.block inverseNine.finish)) (fun _ _ => True) := by
    apply RelCT.ite
    · intro s t hp
      change some (s.read .x .x2 != 0)=some (t.read .x .x2 != 0)
      rw [read_x,read_x]
      apply congrArg some
      apply Bool.eq_iff_iff.mpr
      simp only [bne_iff_ne,ne_eq,hp.2]
    · intro s t ts tt s' t' hp es et
      exact ⟨invAllocated_last_ct _ _ _ _ _ _ trivial trivial hp.1.1 es et,trivial⟩
    · intro s t ts tt s' t' hp es et
      exact ⟨invAllocated_finish_ct _ _ _ _ _ _ trivial trivial hp.1.1 es et,trivial⟩
  have hbody : RelCT isa Pre invAllocatedBody (fun _ _ => True) :=
    RelCT.assoc (RelCT.assoc (RelCT.seq hc hb))
  intro s t ts tt s' t' hp es et
  obtain ⟨trace,_⟩ := hbody _ _ _ _ _ _ hp es et
  obtain ⟨_,_,xs,ks,_,_,_⟩ := invAllocated_body_ok hsize hpr hT hL hR hp.1 hp.2.2.2.1
    (by rw [hp.2.2.2.2.2.1]; exact hX) hC
  obtain ⟨_,_,xt,kt,_,_,_⟩ := invAllocated_body_ok hsize hpr hT hL hR hp.2.1 hp.2.2.2.2.1
    (by rw [hp.2.2.2.2.2.2]; exact hX) hC
  obtain ⟨_,rfl⟩ := es.det xs
  obtain ⟨_,rfl⟩ := et.det xt
  refine ⟨trace,ks.sp.trans (hp.2.2.1.trans kt.sp.symm),?_⟩
  intro r hr
  simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
  subst r
  rw [ks.gpr _ (by decide),kt.gpr _ (by decide)]
  exact hp.1.x0.trans hp.2.1.x0.symm

end VG.Proof.Weierstrass.AArch64
