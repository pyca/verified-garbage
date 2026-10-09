import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourLoad
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourRead
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourAdvance

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def constantRegs : List Reg := [.x0,.x9,.x10,.x11,.x12,.x15,.x16]
def constantVecs : List VReg := [.v18,.v19,.v20,.v21,.v22,.v23,.v24,.v25]
def bodyRegs : List Reg := [.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x13]
def bodyVecs : List VReg := [.v0,.v1,.v2,.v6]

structure Consts (η : Nat) (table : Addr) (s : State) : Prop where
 zero : s.gpr .x0=0
 mask : s.gpr .x11=15
 table : s.gpr .x12=table
 four : s.gpr .x16=4
 thirteen : ∀e<4,vword (s.v .v18) e=13#32
 five : ∀e<4,vword (s.v .v19) e=5#32
 etaQ : ∀e<4,vword (s.v .v20) e=BitVec.ofNat 32 (Spec.MlDsa.q+η)
 q : ∀e<4,vword (s.v .v21) e=8380417#32
 bound : ∀e<4,vword (s.v .v22) e=BitVec.ofNat 32 (VG.Proof.MlDsa.Sample.rbB η)
 nibble : s.v .v23=ofVBytes (fun _=>15)
 weights : ∀e<4,vword (s.v .v24) e=BitVec.ofNat 32 (2^e)
 expand : s.v .v25=expandIndices
 scalarQ : s.gpr .x9=BitVec.ofNat 64 Spec.MlDsa.q
 scalarEta : s.gpr .x10=BitVec.ofNat 64 η
 scalarBound : s.gpr .x15=BitVec.ofNat 64 (VG.Proof.MlDsa.Sample.rbB η)

theorem Consts.keep {η : Nat} {table : Addr} {s t : State} (h : Consts η table s)
    {rs : List Reg} (hk : Keep rs s t)
    (hg : ∀r∈constantRegs,r∉rs)
    (hv : ∀r∈constantVecs,t.v r=s.v r) : Consts η table t := by
  constructor
  · rw [hk.gpr _ (hg _ (by decide))]; exact h.zero
  · rw [hk.gpr _ (hg _ (by decide))]; exact h.mask
  · rw [hk.gpr _ (hg _ (by decide))]; exact h.table
  · rw [hk.gpr _ (hg _ (by decide))]; exact h.four
  · rw [hv _ (by decide)]; exact h.thirteen
  · rw [hv _ (by decide)]; exact h.five
  · rw [hv _ (by decide)]; exact h.etaQ
  · rw [hv _ (by decide)]; exact h.q
  · rw [hv _ (by decide)]; exact h.bound
  · rw [hv _ (by decide)]; exact h.nibble
  · rw [hv _ (by decide)]; exact h.weights
  · rw [hv _ (by decide)]; exact h.expand
  · rw [hk.gpr _ (hg _ (by decide))]; exact h.scalarQ
  · rw [hk.gpr _ (hg _ (by decide))]; exact h.scalarEta
  · rw [hk.gpr _ (hg _ (by decide))]; exact h.scalarBound

theorem Consts.body {η : Nat} {table : Addr} {s t : State} (h : Consts η table s)
    (hk : Keep bodyRegs s t) (hv : ∀r,r∉bodyVecs→t.v r=s.v r) : Consts η table t :=
  h.keep hk (by decide) (fun r hr=>hv r (by
    simp only [constantVecs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide))

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
