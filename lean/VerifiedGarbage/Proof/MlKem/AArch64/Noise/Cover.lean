module
public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate

/-! # Coverage of the existing scratch allocation -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon

def scratchOff (kg : Bool) : Nat := if kg then KG.SS else KEM.SS
def seedOff (kg : Bool) : Nat := if kg then KG.SG else KEM.RB
def nttOff (kg : Bool) : Nat := if kg then KG.NS else KEM.NS

theorem inScratch {s : State} {B : Addr} {size off len : Nat}
    (hc : Covers [⟨B,size⟩] s.wr) (hfit : off+len≤size) (hsize : size<2^64) :
    InRegions s.wr (B+BitVec.ofNat 64 off) len :=
  hc _ _ ⟨⟨B,size⟩,by simp,Offset.contains_base B hfit (by omega)⟩

theorem coversScratch {s : State} {B : Addr} {size off len : Nat}
    (hc : Covers [⟨B,size⟩] s.wr) (hfit : off+len≤size) :
    Covers [⟨B+BitVec.ofNat 64 off,len⟩] s.wr :=
  (Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨⟨B,size⟩,by simp,off,rfl,hfit⟩).trans hc

theorem coversTwo {xs : List Region} {a b : Region} (ha : Covers [a] xs) (hb : Covers [b] xs) :
    Covers [a,b] xs := by
  intro p n ⟨r,hr,h⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact ha p n ⟨r,by simp,h⟩
  · exact hb p n ⟨r,by simp,h⟩

theorem layout_limits {L : KemLay} (wf : L.Wf) (kg : Bool) :
    scratchOff kg+2048=nttOff kg ∧ seedOff kg+32≤scratchOff kg ∧
    nttOff kg+1024≤L.scl ∧ L.scl<65536 := by
  cases kg <;> unfold scratchOff seedOff nttOff <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  all_goals constructor
  all_goals first | rfl | (constructor <;> first | decide | lom)

end VG.Proof.MlKem.AArch64.Noise
