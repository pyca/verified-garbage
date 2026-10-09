import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedState

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

def inputValues (s : State) : Values := fun p => Vector.ofFn fun j =>
  ofVWords (productInput s j.val p.val 0) (productInput s j.val p.val 1)
    (productInput s j.val p.val 2) (productInput s j.val p.val 3)

theorem inputValues_word (s : State) (p : Fin 2) (j : Fin 8) {e : Nat} (he : e<4) :
    vword ((inputValues s p)[j.val]) e=productInput s j.val p.val e := by
  simp only [inputValues,Vector.getElem_ofFn]
  rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [vword_ofVWords_0,vword_ofVWords_1,vword_ofVWords_2,vword_ofVWords_3]

/-- Exact sixteen-vector initial state of the selected paired transform. -/
theorem inputs_ok {s : State} (hc : ProductConstants s)
    (hr : ∀j<8,InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (16*j)) 16 ∧
      ∀p<2,InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg (productClobs (List.finRange 8)) s t → ProductConstants t →
      Banks t (inputValues s) → WP isa (.block rest) t Q) :
    WP isa (.block ((List.range 8).flatMap product++rest)) s Q := by
  have heq : (List.finRange 8).flatMap (fun j => product j.val)=(List.range 8).flatMap product := rfl
  rw [← heq]
  refine productBank_ok _ (List.nodup_finRange 8) hc (fun j _ => hr j.val j.isLt) fun t ht ct vt =>
    k t ht ct ?_
  intro p j
  apply vec_ext
  intro e he
  rw [inputValues_word s p j he]
  simpa only [bankRegs,Vector.getElem_ofFn] using vt j (List.mem_finRange j) p.val p.isLt e he

end VG.Proof.MlDsa.AArch64.Optimized.Paired
