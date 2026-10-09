import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourScalarBody
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourTraversal

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

def parserRegs : List Reg := [.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17]

structure ScalarLayout (σ : State) (p q : Addr) (X : List Byte) : Prop where
 short : X.length≤272
 stream : ∀i<X.length,σ.mem (q+BitVec.ofNat 64 i)=X[i]!
 apart : (⟨q,X.length⟩ : Region).Disjoint (polyR p)
 read : ∀i<X.length,InRegions (σ.rd++σ.wr) (q+BitVec.ofNat 64 i) 1
 write : ∀j<256,InRegions σ.wr (coeffAddr p j) 4

structure ScalarInv (σ : State) (η : Nat) (p q : Addr) (L : List Zq) (X : List Byte)
    (done : Nat) (s : State) : Prop where
 bound : done≤X.length
 consts : ScalarConsts η s
 keep : Keep parserRegs σ s
 frame : Frame [polyR p] σ.mem s.mem
 stored : Stored s.mem p (parsed η L X done)
 input : s.gpr .x2=q+BitVec.ofNat 64 done
 output : s.gpr .x3=coeffAddr p (parsed η L X done).length
 remaining : (s.gpr .x4).toNat=256-(parsed η L X done).length
 bytes : s.gpr .x5=BitVec.ofNat 64 (X.length-done)
 guard : s.gpr .x8=BitVec.ofNat 64 ((256-(parsed η L X done).length)*(X.length-done))

theorem ScalarInv.stream {σ s : State} {η done : Nat} {p q : Addr} {L : List Zq} {X : List Byte}
    (h : ScalarInv σ η p q L X done s) (hy : ScalarLayout σ p q X) {i : Nat} (hi : i<X.length) :
    s.mem (q+BitVec.ofNat 64 i)=X[i]! := by
  rw [h.frame.bytes (R := ⟨q,X.length⟩) (fun r hr=>by
    rw [List.mem_singleton.mp hr]; exact hy.apart) (by change X.length≤2^64; have:=hy.short; omega) hi]
  exact hy.stream i hi

theorem scalarGuard_ok {s : State} {r n : Nat}
    (h4 : (s.gpr .x4).toNat=r) (h5 : s.gpr .x5=BitVec.ofNat 64 n) :
    WP isa (.block [.mul .x .x8 .x4 .x5]) s fun t=>
      Only [.x8] s t ∧ t.gpr .x8=BitVec.ofNat 64 (r*n) := by
  have hh : s.gpr .x4=BitVec.ofNat 64 r := by rw [←h4]; simp
  refine wp_mul fun t ht he=>wp_nil ⟨ht,?_⟩
  rw [he,hh,h5,BitVec.ofNat_mul]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
