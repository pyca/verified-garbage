import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBody
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourTraversal

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64 (Keep)

structure Layout (σ : State) (table p q : Addr) (X : List Byte) : Prop where
 short : X.length≤272
 even : X.length%2=0
 stream : ∀i<X.length,σ.mem (q+BitVec.ofNat 64 i)=X[i]!
 streamApart : (⟨q,X.length+2⟩ : Region).Disjoint (polyR p)
 tableApart : (⟨table,1024⟩ : Region).Disjoint (polyR p)
 read : ∀d,d+2≤X.length→InRegions (σ.rd++σ.wr) (q+BitVec.ofNat 64 d) 4
 tableRead : ∀m<16,InRegions (σ.rd++σ.wr) (table+BitVec.ofNat 64 (64*m)) 16 ∧
      InRegions (σ.rd++σ.wr) (table+BitVec.ofNat 64 (64*m)+32) 8
 write : ∀j,j≤252→InRegions σ.wr (coeffAddr p j) 16

structure LoopInv (σ : State) (η : Nat) (table p q : Addr) (L : List Zq) (X : List Byte)
    (done : Nat) (s : State) : Prop where
 bound : done≤X.length
 even : done%2=0
 consts : Consts η table s
 table : TableAt s.mem table
 keep : Keep bodyRegs σ s
 frame : Frame [polyR p] σ.mem s.mem
 stored : Stored s.mem p (parsed η L X done)
 input : s.gpr .x2=q+BitVec.ofNat 64 done
 output : s.gpr .x3=coeffAddr p (parsed η L X done).length
 remaining : s.gpr .x4=BitVec.ofNat 64 (256-(parsed η L X done).length)
 bytes : s.gpr .x5=BitVec.ofNat 64 (X.length-done)
 guard : s.gpr .x8=if (parsed η L X done).length≤252 then BitVec.ofNat 64 (X.length-done) else 0

theorem LoopInv.stream {σ s : State} {η done : Nat} {table p q : Addr} {L : List Zq} {X : List Byte}
    (h : LoopInv σ η table p q L X done s) (hY : Layout σ table p q X) {i : Nat} (hi : i<X.length) :
    s.mem (q+BitVec.ofNat 64 i)=X[i]! := by
  rw [h.frame.bytes (R := ⟨q,X.length+2⟩) (fun r hr=>by
    rw [List.mem_singleton.mp hr]; exact hY.streamApart) (by change X.length+2≤2^64; have:=hY.short; omega) (by change i<X.length+2; omega)]
  exact hY.stream i hi

theorem LoopInv.values {σ s : State} {η done : Nat} {table p q : Addr} {L : List Zq} {X : List Byte}
    (h : LoopInv σ η table p q L X done s) (hY : Layout σ table p q X) (hd : done+2≤X.length) :
    bodyValues η s=accepted η (nibbles X[done]! X[done+1]!) := by
  unfold bodyValues
  rw [h.input,h.stream hY (by omega)]
  have ha : q+BitVec.ofNat 64 done+1=q+BitVec.ofNat 64 (done+1) := by
    rw [BitVec.add_assoc,BitVec.ofNat_add]; rfl
  rw [ha,h.stream hY (by omega)]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
