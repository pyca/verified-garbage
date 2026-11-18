module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerBank
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PackedBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Traversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
import VerifiedGarbage.Proof.Framework.AArch64.Simd

/-! ### `MlDsa.AArch64.Optimized.PackedLanes`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def pairWord (a b : BitVec 128) (i : Nat) : BitVec 32 :=
  if i<4 then vword a i else vword b (i-4)

def packedLane (len i : Nat) : Nat := len*(i/(2*len))+i%len

def packedLow (len i : Nat) : Nat := 2*len*(i/(2*len))+i%len

/-- The gather/scatter pair implements four scalar butterflies in coefficient order. -/
theorem packedResult_word (a b : BitVec 128) {len : Nat} (hl : len=1 ∨ len=2)
    (second : Bool) (z : Nat → Int) {e : Nat} (he : e<4) :
    vword (packedResult len second a b z) e =
      let i := (if second then 4 else 0)+e
      let x := pairWord a b (packedLow len i)
      let y := fastMulWord (pairWord a b (packedLow len i+len)) (z (packedLane len i))
      if i%(2*len)<len then x+y else x-y := by
  have he' : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega_using [he]
  rcases hl with rfl | rfl <;> cases second <;>
    rcases he' with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) [packedResult,gatherWord,scatterWord,show ¬ (1:Nat)=2 by decide,
      vword_trn1_d2,vword_trn2_d2,
      vword_zip1_s4',vword_zip2_s4,
      VG.AArch64.vword_map2,fastVector_word,
      vword_uzp1_s4,vword_uzp2_s4,
      pairWord,packedLow,packedLane]

theorem packed_indices {len i : Nat} (hl : len=1 ∨ len=2) (hi : i<8) :
    packedLow len i<8 ∧ packedLow len i+len<8 ∧ packedLane len i<4 := by
  rcases hl with rfl | rfl <;> unfold packedLow packedLane <;> omega_using [hi]

theorem packedResult_int (a b : BitVec 128) {len : Nat} (hl : len=1 ∨ len=2)
    (second : Bool) (z : Nat → Int) {e : Nat} (he : e<4) {bound : Int}
    (hb : 0≤bound) (hs : bound+16760834<2147483648)
    (hv : ∀ i<8,-bound≤(pairWord a b i).toInt ∧ (pairWord a b i).toInt≤bound) :
    (vword (packedResult len second a b z) e).toInt =
      let i := (if second then 4 else 0)+e
      let x := (pairWord a b (packedLow len i)).toInt
      let y := fastMul (pairWord a b (packedLow len i+len)).toInt (z (packedLane len i))
      if i%(2*len)<len then x+y else x-y := by
  rw [packedResult_word a b hl second z he]
  have hi : (if second then 4 else 0)+e<8 := by cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add] <;> omega
  have hd := packed_indices hl hi
  have hx := hv _ hd.1
  have hy := fastMul_bounds (z := z (packedLane len ((if second then 4 else 0)+e)))
    (BitVec.le_toInt (pairWord a b (packedLow len ((if second then 4 else 0)+e)+len)))
    (BitVec.toInt_lt (x := pairWord a b (packedLow len ((if second then 4 else 0)+e)+len)))
  dsimp only
  by_cases hc : ((if second then 4 else 0)+e)%(2*len)<len
  · rw [ite_eq_left hc,ite_eq_left hc,addWord_int _ _ (by rw [fastMulWord_int]; omega) (by rw [fastMulWord_int]; omega),fastMulWord_int]
  · rw [ite_eq_right hc,ite_eq_right hc,subWord_int _ _ (by rw [fastMulWord_int]; omega) (by rw [fastMulWord_int]; omega),fastMulWord_int]

theorem packedResult_bound (a b : BitVec 128) {len : Nat} (hl : len=1 ∨ len=2)
    (second : Bool) (z : Nat → Int) {e : Nat} (he : e<4) {bound : Int}
    (hb : 0≤bound) (hs : bound+16760834<2147483648)
    (hv : ∀ i<8,-bound≤(pairWord a b i).toInt ∧ (pairWord a b i).toInt≤bound) :
    -(bound+16760834)≤(vword (packedResult len second a b z) e).toInt ∧
      (vword (packedResult len second a b z) e).toInt≤bound+16760834 := by
  rw [packedResult_int a b hl second z he hb hs hv]
  have hi : (if second then 4 else 0)+e<8 := by
    cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add] <;> omega_using [he]
  have hd := packed_indices hl hi
  have hx := hv _ hd.1
  have hy := fastMul_bounds (z := z (packedLane len ((if second then 4 else 0)+e)))
    (BitVec.le_toInt (pairWord a b (packedLow len ((if second then 4 else 0)+e)+len)))
    (BitVec.toInt_lt (x := pairWord a b (packedLow len ((if second then 4 else 0)+e)+len)))
  dsimp only
  by_cases hc : ((if second then 4 else 0)+e)%(2*len)<len
  · rw [ite_eq_left hc]; omega_using [hx, hy]
  · rw [ite_eq_right hc]; omega_using [hx, hy]

end VG.Proof.MlDsa.AArch64.Optimized

end

end

/-! ### `MlDsa.AArch64.Optimized.TailTraversal`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Traversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def packedSchedule (start len : Nat) (root : Nat → Nat) : List Op :=
  (List.range (4/len)).flatMap fun g => (List.range len).map fun j =>
    ⟨start+2*len*g+j,len,root (len*g+j)⟩

theorem packedSchedule_get (w : Poly) {start len i : Nat} (hl : len=1 ∨ len=2)
    (hs : start+8≤256) (hi : i<8) (root : Nat → Nat) :
    (run (packedSchedule start len root) w)[start+i]! =
      let x := w[start+packedLow len i]!
      let y := zetas (root (packedLane len i))*w[start+packedLow len i+len]!
      if i%(2*len)<len then x+y else x-y := by
  have hi' : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega_using [hi]
  rcases hl with rfl | rfl <;>
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [-getElem!_pos,packedSchedule,run,List.range_succ,Op.apply,packedLow,packedLane,Nat.add_assoc] <;>
    repeat (rw [bfly_get _ (by omega_using []) (by unfold n; omega_using [hs]) _ (by unfold n; omega_using [hs])]
            simp (disch := omega) [-getElem!_pos,Nat.add_assoc])

theorem packedSchedule_outside (w : Poly) {start len i : Nat} (hl : len=1 ∨ len=2)
    (hs : start+8≤256) (hi : i<256) (hout : i<start ∨ start+8≤i) (root : Nat → Nat) :
    (run (packedSchedule start len root) w)[i]! = w[i]! := by
  have h0 : i≠start := by omega_using [hout]
  have hn : ∀ j<8,i≠start+j := by intro j hj; omega_using [hout, hj]
  rcases hl with rfl | rfl <;>
    simp [-getElem!_pos,packedSchedule,run,List.range_succ,Op.apply] <;>
    repeat (rw [bfly_get _ (by omega_using []) (by unfold n; omega_using [hs]) _ (by unfold n; omega_using [hi])]
            simp (disch := omega) [-getElem!_pos,Nat.add_assoc,h0,hn 1 (by decide),
              hn 2 (by decide),hn 3 (by decide),hn 4 (by decide),hn 5 (by decide),
              hn 6 (by decide),hn 7 (by decide)])

end VG.Proof.MlDsa.AArch64.Optimized.Traversal

end

end

/-! ## From `TailField.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem packedResult_field (a b : BitVec 128) (w : Poly) {len start : Nat}
    (hl : len=1 ∨ len=2) (hstart : start+8≤256) (second : Bool) (root : Nat → Nat)
    {e : Nat} (he : e<4) {bound : Int} (hb : 0≤bound) (hs : bound+16760834<2147483648)
    (hv : ∀ i<8,-bound≤(pairWord a b i).toInt ∧ (pairWord a b i).toInt≤bound)
    (hf : ∀ i<8,ofInt (pairWord a b i).toInt=w[start+i]!) :
    ofInt (vword (packedResult len second a b (fun e => (zetaNat (root e) : Int))) e).toInt=
      (Traversal.run (Traversal.packedSchedule start len root) w)[start+(if second then 4 else 0)+e]! := by
  have hi : (if second then 4 else 0)+e<8 := by
    cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add] <;> omega_using [he]
  have hd := packed_indices hl hi
  rw [packedResult_int a b hl second _ he hb hs hv,Nat.add_assoc,
    Traversal.packedSchedule_get w hl hstart hi]
  dsimp only
  by_cases hc : ((if second then 4 else 0)+e)%(2*len)<len
  · rw [ite_eq_left hc,ite_eq_left hc,ofInt_add,fastMul_field,
      Traversal.ofInt_zetaNat,hf _ hd.1,hf _ hd.2.1,Nat.add_assoc,Fin.mul_comm]
  · rw [ite_eq_right hc,ite_eq_right hc,ofInt_sub,fastMul_field,
      Traversal.ofInt_zetaNat,hf _ hd.1,hf _ hd.2.1,Nat.add_assoc,Fin.mul_comm]

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `TailBank.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem pairWord_bound (v : Vector (BitVec 128) 8) {g : Nat} (hg : g<4) {bound : Int}
    (hv : BankBound v bound) {i : Nat} (hi : i<8) :
    -bound≤(pairWord v[2*g] v[2*g+1] i).toInt ∧
      (pairWord v[2*g] v[2*g+1] i).toInt≤bound := by
  unfold pairWord
  split
  · exact hv ⟨2*g,by omega_using [hg]⟩ i ‹_›
  · exact hv ⟨2*g+1,by omega_using [hg]⟩ (i-4) (by omega_using [hi])

theorem pairWord_field (v : Vector (BitVec 128) 8) (w : Poly) {g u : Nat} (hg : g<4)
    (hf : InnerBankField u v w) {i : Nat} (hi : i<8) :
    ofInt (pairWord v[2*g] v[2*g+1] i).toInt = w[32*u+8*g+i]! := by
  unfold pairWord
  split
  · have h := hf ⟨2*g,by omega_using [hg]⟩ i ‹_›
    simpa only [Traversal.innerLoc,show 4*(2*g)=8*g by omega_using []] using h
  · have h := hf ⟨2*g+1,by omega_using [hg]⟩ (i-4) (by omega_using [hi])
    simpa only [Traversal.innerLoc,show 32*u+4*(2*g+1)+(i-4)=32*u+8*g+i by omega_arith] using h

theorem packedValues_bound (v : Vector (BitVec 128) 8) {g len : Nat} (hg : g<4)
    (hl : len=1 ∨ len=2) (z : Nat → Int) {bound : Int} (hb : 0≤bound)
    (hs : bound+16760834<2147483648) (hv : BankBound v bound) :
    BankBound (packedValues v ⟨2*g,by omega_using [hg]⟩ ⟨2*g+1,by omega_using [hg]⟩ len z) (bound+16760834) := by
  intro i e he
  simp only [packedValues,Vector.getElem_set]
  by_cases hj : 2*g+1=i.val
  · rw [ite_eq_left hj]
    exact packedResult_bound _ _ hl true z he hb hs (fun i hi => pairWord_bound v hg hv hi)
  · rw [ite_eq_right hj]
    by_cases hi : 2*g=i.val
    · rw [ite_eq_left hi]
      exact packedResult_bound _ _ hl false z he hb hs (fun i hi => pairWord_bound v hg hv hi)
    · rw [ite_eq_right hi]
      have h := hv i e he
      omega_using [h]

theorem packedValues_field (v : Vector (BitVec 128) 8) (w : Poly) {g len u : Nat}
    (hg : g<4) (hl : len=1 ∨ len=2) (hu : u<8) (root : Nat → Nat) {bound : Int}
    (hb : 0≤bound) (hs : bound+16760834<2147483648) (hv : BankBound v bound)
    (hf : InnerBankField u v w) :
    InnerBankField u (packedValues v ⟨2*g,by omega_using [hg]⟩ ⟨2*g+1,by omega_using [hg]⟩ len
      (fun e => (zetaNat (root e) : Int)))
      (Traversal.run (Traversal.packedSchedule (32*u+8*g) len root) w) := by
  intro i e he
  simp only [packedValues,Vector.getElem_set]
  by_cases hj : 2*g+1=i.val
  · rw [ite_eq_left hj]
    have h := packedResult_field v[2*g] v[2*g+1] w hl (show 32*u+8*g+8≤256 by omega_using [hg, hu])
      true root he hb hs (fun i hi => pairWord_bound v hg hv hi)
      (fun i hi => pairWord_field v w hg hf hi)
    simpa only [ite_true,Traversal.innerLoc,← hj,show 32*u+4*(2*g+1)+e=32*u+8*g+4+e by omega_using []] using h
  · rw [ite_eq_right hj]
    by_cases hi : 2*g=i.val
    · rw [ite_eq_left hi]
      have h := packedResult_field v[2*g] v[2*g+1] w hl (show 32*u+8*g+8≤256 by omega_using [hg, hu])
        false root he hb hs (fun i hi => pairWord_bound v hg hv hi)
        (fun i hi => pairWord_field v w hg hf hi)
      simpa only [Bool.false_eq_true,ite_false,Nat.add_zero,Traversal.innerLoc,← hi,
        show 4*(2*g)=8*g by omega_using []] using h
    · rw [ite_eq_right hi,Traversal.packedSchedule_outside w hl (by omega_using [hg, hu])
        (by unfold Traversal.innerLoc; omega_using [hu, he]) (by unfold Traversal.innerLoc; omega_using [he, hj, hi]),hf i e he]

end VG.Proof.MlDsa.AArch64.Optimized

end
