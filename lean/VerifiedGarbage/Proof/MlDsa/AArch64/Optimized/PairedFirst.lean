import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedProductFive
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFiveSlice

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (PackedRoots packedRoot localRoot localOffset fiveValues)

def firstCode : List Instr := productFiveCode++(pairStores 16).map (fun p => Instr.strq p.1 .x0 p.2)
def firstAdvance : List Instr :=
  [.addImm .x .x13 .x13 128,.addImm .x .x14 .x14 128,.addImm .x .x0 .x0 128,
   .addImm .x .x1 .x1 480,.subImm .x .x11 .x11 1]

theorem firstBlock_eq : firstBlock=firstCode++firstAdvance := by
  unfold firstBlock firstCode productFiveCode
  rw [fiveCode_eq]
  rfl

theorem first_ok (u : Nat) {s : State} {rest : List Instr} {Q : State → Prop}
    (hc : ProductConstants s) (hp : PackedRoots s (packedRoot u))
    (hl : ∀i:Fin 7,RootReady s (localOffset i.val) (localRoot u i.val))
    (hr : ∀j<8,InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (16*j)) 16 ∧
      ∀p<2,InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j)) 16)
    (hw : ∀p:Fin 2,∀j:Fin 8,InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (1024*p.val+16*j.val)) 16)
    (k : ∀t,(∃a,VChg workRegs s a ∧ VMem a t
      (writePair (fun p => fiveValues u (inputValues s p)) (s.gpr .x0) 16 s.mem)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (firstCode++rest)) s Q := by
  simp only [firstCode,List.append_assoc]
  refine productFive_ok hc hp hl hr fun a ha va => ?_
  refine storePair_ok 16 .x0 (by intro p j; constructor <;> omega) va ?_ fun t ht => ?_
  · intro p j
    simpa only [ha.wr,ha.gpr] using hw p j
  · refine k t ⟨a,ha,?_⟩
    simpa only [ha.gpr,ha.mem,Inverse.fiveValues] using ht

end VG.Proof.MlDsa.AArch64.Optimized.Paired
