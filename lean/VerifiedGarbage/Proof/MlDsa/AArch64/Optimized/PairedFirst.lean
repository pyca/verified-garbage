import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLoad
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedState
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFive
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFiveSlice

/-! ## From `PairedBank.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

def productTemps : List VReg := [.v24,.v25,.v26,.v27,.v28]
def productClobs (js : List (Fin 8)) : List VReg :=
  productTemps++js.flatMap (fun j => [vr j.val,vr (8+j.val)])
def productInput (s : State) (j p e : Nat) : BitVec 32 :=
  centeredProduct (vword (s.mem.read (s.gpr .x13+BitVec.ofNat 64 (16*j)) 16) e)
    (vword (s.mem.read (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j)) 16) e)

theorem bank_not_clob {j : Fin 8} {js : List (Fin 8)} (hj : j∉js) {p : Nat} (hp : p<2) :
    vr (8*p+j.val)∉productClobs js := by
  intro h
  rcases List.mem_append.mp h with h | h
  · have hb := bank_safe (j := 8*p+j.val) (by omega)
    apply hb
    simp only [productTemps,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · obtain ⟨i,hi,h⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    have he : j=i := by
      apply Fin.ext
      rcases h with h | h
      · have hx := bank_injective (by omega) (by omega) h
        omega
      · have hx := bank_injective (by omega) (by omega) h
        omega
    exact hj (he ▸ hi)

theorem productBank_ok (js : List (Fin 8)) (hn : js.Nodup)
    {s : State} (hc : ProductConstants s)
    (hr : ∀j∈js,InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (16*j.val)) 16 ∧
      ∀p<2,InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j.val)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg (productClobs js) s t → ProductConstants t →
      (∀j∈js,∀p<2,∀e<4,vword (t.v (vr (8*p+j.val))) e=productInput s j.val p e) →
      WP isa (.block rest) t Q) :
    WP isa (.block (js.flatMap (fun j => product j.val)++rest)) s Q := by
  induction js generalizing s with
  | nil => exact k s (VChg.refl _ _) hc (by simp)
  | cons j js ih =>
    have nn := List.nodup_cons.mp hn
    have rr := hr j (by simp)
    simp only [List.flatMap_cons,List.append_assoc]
    refine product_ok j hc rr.1 rr.2 fun a ha ca va => ?_
    refine ih nn.2 ca ?_ fun t ht ct vt => ?_
    · intro i hi
      rw [ha.rd,ha.wr,ha.gpr]
      exact hr i (List.mem_cons_of_mem _ hi)
    · refine k t ((ha.trans ht).mono ?_) ct ?_
      · intro r hm
        simp only [productClobs,productTemps,List.flatMap_cons,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false] at *
        grind only
      · intro i hi p hp e he
        rcases List.mem_cons.mp hi with rfl | hi
        · rw [ht.get _ (bank_not_clob nn.1 hp),va p hp e he]
          rfl
        · rw [vt i hi p hp e he]
          unfold productInput
          rw [ha.mem,ha.gpr]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedInputs.lean` -/

section

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

end

/-! ## From `PairedProductFive.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (PackedRoots packedSteps packedRunValues localOffset)

def productFiveCode : List Instr := (List.range 8).flatMap product++fiveCode

theorem productFive_ok {s : State} {rest : List Instr} {Q : State → Prop}
    {zp : Nat → Nat → Nat → Int} {zl : Nat → Nat → Int}
    (hc : ProductConstants s) (hp : PackedRoots s zp)
    (hl : ∀i:Fin 7,RootReady s (localOffset i.val) (zl i.val))
    (hr : ∀j<8,InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (16*j)) 16 ∧
      ∀p<2,InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j)) 16)
    (k : ∀t,VChg workRegs s t → Banks t (fun p =>
      Inverse.runValues zl 0 7 (packedRunValues (inputValues s p) zp packedSteps)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (productFiveCode++rest)) s Q := by
  simp only [productFiveCode,List.append_assoc]
  refine inputs_ok hc hr fun a ha _ va => ?_
  have ha' : VChg workRegs s a := ha.mono (by decide)
  refine five_ok va (packedRoots_frame hp ha') (fun i => (hl i).chg ha) fun t ht vt => ?_
  exact k t ((ha'.trans ht).mono (by simp)) vt

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedFirst.lean` -/

section

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

end
