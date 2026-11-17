module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFive
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedBank
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PackedLanes
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalBank
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseArithmetic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TailBank
import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankFieldStage
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseLocalTable
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal

/-! ### `MlDsa.AArch64.Optimized.InverseBankFieldSchedule`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def packedSchedule (start len : Nat) (root : Nat → Nat) : List Op :=
  (List.range (4/len)).flatMap fun g => (List.range len).map fun j =>
    ⟨start+2*len*g+j,len,root (len*g+j)⟩

theorem packedSchedule_get (w : Poly) {start len i : Nat} (hl : len=1 ∨ len=2)
    (hs : start+8≤256) (hi : i<8) (root : Nat → Nat) :
    (run (packedSchedule start len root) w)[start+i]! =
      let x := w[start+packedLow len i]!
      let y := w[start+packedLow len i+len]!
      if i%(2*len)<len then x+y else -zetas (root (packedLane len i))*(x-y) := by
  have hi' : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega_using [hi]
  rcases hl with rfl | rfl <;>
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [-getElem!_pos,packedSchedule,run,List.range_succ,Op.apply,packedLow,packedLane,Nat.add_assoc] <;>
    repeat (rw [bflyInv_get _ (by omega_using []) (by unfold n; omega_using [hs]) _ (by unfold n; omega_using [hs])]
            simp (disch := omega) [-getElem!_pos,Nat.add_assoc])

theorem packedSchedule_outside (w : Poly) {start len i : Nat} (hl : len=1 ∨ len=2)
    (hs : start+8≤256) (hi : i<256) (hout : i<start ∨ start+8≤i) (root : Nat → Nat) :
    (run (packedSchedule start len root) w)[i]! = w[i]! := by
  have h0 : i≠start := by omega_using [hout]
  have hn : ∀ j<8,i≠start+j := by intro j hj; omega_using [hout, hj]
  rcases hl with rfl | rfl <;>
    simp [-getElem!_pos,packedSchedule,run,List.range_succ,Op.apply] <;>
    repeat (rw [bflyInv_get _ (by omega_using []) (by unfold n; omega_using [hs]) _ (by unfold n; omega_using [hi])]
            simp (disch := omega) [-getElem!_pos,Nat.add_assoc,h0,hn 1 (by decide),
              hn 2 (by decide),hn 3 (by decide),hn 4 (by decide),hn 5 (by decide),
              hn 6 (by decide),hn 7 (by decide)])

end VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseBankFieldRun`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def runOps (u : Nat) (root : Nat → Nat) (i : Nat) : Nat → List InverseTraversal.Op
  | 0 => []
  | n+1 => stageOps u (root i) i ++ runOps u root (i+1) n

theorem runValues_field (i n : Nat) (hin : i+n≤7) (v : Vector (BitVec 128) 8) (w : Poly)
    {u : Nat} (hu : u<8) (root : Nat → Nat) {b : Int}
    (hb : 8380417≤b) (hs : 8*b<2147483648) (hv : StageBound v i b)
    (hf : InnerBankField u v w) :
    StageBound (runValues (fun i _ => (negZetaNat (root i) : Int)) i n v) (i+n) b ∧
      InnerBankField u (runValues (fun i _ => (negZetaNat (root i) : Int)) i n v)
        (InverseTraversal.run (runOps u root i n) w) := by
  induction n generalizing i v w with
  | zero => exact ⟨hv,hf⟩
  | succ n ih =>
    have hi : i<7 := by omega_using [hin]
    have hp := stageValues_bound ⟨i,hi⟩ v (fun _ => (negZetaNat (root i) : Int)) hb hs hv
    have hfield := stageValues_field ⟨i,hi⟩ v w hu (root i) hb hs hv hf
    have h := ih (i := i+1) (by omega_using [hin]) _ _ hp hfield
    simpa only [runValues,runOps,InverseTraversal.run_append,Nat.add_assoc,Nat.add_comm 1 n] using h

theorem stageBound_zero (v : Vector (BitVec 128) 8) (b : Int) :
    StageBound v 0 b ↔ BankBound v b := by
  simp only [StageBound,BankBound,stageDepth,Nat.reduceLT,ite_true,Nat.mul_zero,
    Nat.not_lt_zero,ite_false,Int.pow_zero,Int.one_mul]

theorem stageBound_seven (v : Vector (BitVec 128) 8) (b : Int) :
    StageBound v 7 b ↔ BankBound v (8*b) := by
  simp only [StageBound,BankBound,stageDepth,Nat.reduceLT,ite_false,Nat.reduceEqDiff,Int.reducePow]

theorem localRoot_index (u : Nat) :
    localRoot u=(fun i _ => (negZetaNat (localIndex u i) : Int)) := rfl

theorem runValues_local (v : Vector (BitVec 128) 8) (w : Poly) {u : Nat} (hu : u<8)
    (hv : BankBound v 33521668) (hf : InnerBankField u v w) :
    BankBound (runValues (localRoot u) 0 7 v) 268173344 ∧
      InnerBankField u (runValues (localRoot u) 0 7 v)
        (InverseTraversal.run (runOps u (localIndex u) 0 7) w) := by
  rw [localRoot_index]
  have h := runValues_field 0 7 (by decide) v w hu (localIndex u) (by decide) (by decide)
    ((stageBound_zero v 33521668).mpr hv) hf
  exact ⟨(stageBound_seven _ _).mp h.1,h.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseBankFieldPackedBank`, which only this module used -/

section

/-! ## From `InverseBankFieldPacked.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

/-- The packed inverse gather/scatter computes four ordered scalar butterflies. -/
theorem packedResult_word (a b : BitVec 128) {len : Nat} (hl : len=1 ∨ len=2)
    (second : Bool) (z : Nat → Int) {e : Nat} (he : e<4) :
    vword (packedResult len second a b z) e =
      let i := (if second then 4 else 0)+e
      let x := pairWord a b (packedLow len i)
      let y := pairWord a b (packedLow len i+len)
      if i%(2*len)<len then x+y else fastMulWord (x-y) (z (packedLane len i)) := by
  have he' : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega_using [he]
  rcases hl with rfl | rfl <;> cases second <;>
    rcases he' with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) [packedResult,gather,scatter,
      vword_trn1_d2,vword_trn2_d2,vword_zip1_s4',vword_zip2_s4,
      VG.AArch64.vword_map2,fastVector_word,vword_uzp1_s4,vword_uzp2_s4,
      pairWord,packedLow,packedLane]

/-- Bounds are needed only for the two selected registers, not the other six
registers whose current layer may already have completed. -/
theorem packedResult_int (a b : BitVec 128) {len : Nat} (hl : len=1 ∨ len=2)
    (second : Bool) (z : Nat → Int) {e : Nat} (he : e<4) {bound : Int}
    (hq : 8380417≤bound) (hs : 2*bound<2147483648)
    (hv : ∀ i<8,-bound≤(pairWord a b i).toInt ∧ (pairWord a b i).toInt≤bound) :
    (vword (packedResult len second a b z) e).toInt =
      let i := (if second then 4 else 0)+e
      let x := (pairWord a b (packedLow len i)).toInt
      let y := (pairWord a b (packedLow len i+len)).toInt
      if i%(2*len)<len then x+y else fastMul (x-y) (z (packedLane len i)) := by
  rw [packedResult_word a b hl second z he]
  have hi : (if second then 4 else 0)+e<8 := by
    cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add] <;> omega_using [he]
  have hd := packed_indices hl hi
  have hp := pair_word (z := z (packedLane len ((if second then 4 else 0)+e)))
    _ _ hq hs (hv _ hd.1) (hv _ hd.2.1)
  dsimp only
  by_cases hc : ((if second then 4 else 0)+e)%(2*len)<len
  · rw [ite_eq_left hc,ite_eq_left hc]
    exact hp.1
  · rw [ite_eq_right hc,ite_eq_right hc]
    exact hp.2

theorem packedResult_bound (a b : BitVec 128) {len : Nat} (hl : len=1 ∨ len=2)
    (second : Bool) (z : Nat → Int) {e : Nat} (he : e<4) {bound : Int}
    (hq : 8380417≤bound) (hs : 2*bound<2147483648)
    (hv : ∀ i<8,-bound≤(pairWord a b i).toInt ∧ (pairWord a b i).toInt≤bound) :
    -(2*bound)≤(vword (packedResult len second a b z) e).toInt ∧
      (vword (packedResult len second a b z) e).toInt≤2*bound := by
  rw [packedResult_int a b hl second z he hq hs hv]
  have hi : (if second then 4 else 0)+e<8 := by
    cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add] <;> omega_using [he]
  have hd := packed_indices hl hi
  have hp := pair_bounds (z := z (packedLane len ((if second then 4 else 0)+e)))
    hq hs (hv _ hd.1) (hv _ hd.2.1)
  dsimp only
  by_cases hc : ((if second then 4 else 0)+e)%(2*len)<len
  · rw [ite_eq_left hc]
    simpa only [pair,Int.neg_mul] using hp.1
  · rw [ite_eq_right hc]
    simpa only [pair,Int.neg_mul] using hp.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseBankFieldPackedField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem packedResult_field (a b : BitVec 128) (w : Poly) {len start : Nat}
    (hl : len=1 ∨ len=2) (hstart : start+8≤256) (second : Bool) (root : Nat → Nat)
    {e : Nat} (he : e<4) {bound : Int} (hb : 8380417≤bound) (hs : 2*bound<2147483648)
    (hv : ∀ i<8,-bound≤(pairWord a b i).toInt ∧ (pairWord a b i).toInt≤bound)
    (hf : ∀ i<8,ofInt (pairWord a b i).toInt=w[start+i]!) :
    ofInt (vword (packedResult len second a b (fun e => (negZetaNat (root e) : Int))) e).toInt=
      (InverseTraversal.run (InverseTraversal.packedSchedule start len root) w)[start+(if second then 4 else 0)+e]! := by
  have hi : (if second then 4 else 0)+e<8 := by
    cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add] <;> omega_using [he]
  have hd := packed_indices hl hi
  rw [packedResult_int a b hl second _ he hb hs hv,Nat.add_assoc,
    InverseTraversal.packedSchedule_get w hl hstart hi]
  dsimp only
  by_cases hc : ((if second then 4 else 0)+e)%(2*len)<len
  · rw [ite_eq_left hc,ite_eq_left hc,ofInt_add,hf _ hd.1,hf _ hd.2.1,Nat.add_assoc]
  · rw [ite_eq_right hc,ite_eq_right hc,fastMul_field,ofInt_sub,
      InverseTraversal.ofInt_negZetaNat,hf _ hd.1,hf _ hd.2.1,Nat.add_assoc,Fin.mul_comm]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseBankFieldPackedBank.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem packedValues_field (v : Vector (BitVec 128) 8) (w : Poly) {g len u : Nat}
    (hg : g<4) (hl : len=1 ∨ len=2) (hu : u<8) (root : Nat → Nat) {bound : Int}
    (hb : 8380417≤bound) (hs : 2*bound<2147483648)
    (hv : ∀ j<8, -bound≤(pairWord v[2*g] v[2*g+1] j).toInt ∧
      (pairWord v[2*g] v[2*g+1] j).toInt≤bound)
    (hf : InnerBankField u v w) :
    InnerBankField u (packedValues v ⟨2*g,by omega_using [hg]⟩ ⟨2*g+1,by omega_using [hg]⟩ len
      (fun e => (negZetaNat (root e) : Int)))
      (InverseTraversal.run (InverseTraversal.packedSchedule (32*u+8*g) len root) w) := by
  intro i e he
  simp only [packedValues,Vector.getElem_set]
  by_cases hj : 2*g+1=i.val
  · rw [ite_eq_left hj]
    have h := packedResult_field v[2*g] v[2*g+1] w hl (show 32*u+8*g+8≤256 by omega_using [hg, hu])
      true root he hb hs hv
      (fun i hi => pairWord_field v w hg hf hi)
    simpa only [ite_true,Traversal.innerLoc,← hj,show 32*u+4*(2*g+1)+e=32*u+8*g+4+e by omega_using []] using h
  · rw [ite_eq_right hj]
    by_cases hi : 2*g=i.val
    · rw [ite_eq_left hi]
      have h := packedResult_field v[2*g] v[2*g+1] w hl (show 32*u+8*g+8≤256 by omega_using [hg, hu])
        false root he hb hs hv
        (fun i hi => pairWord_field v w hg hf hi)
      simpa only [Bool.false_eq_true,ite_false,Nat.add_zero,Traversal.innerLoc,← hi,
        show 4*(2*g)=8*g by omega_using []] using h
    · rw [ite_eq_right hi,InverseTraversal.packedSchedule_outside w hl (by omega_using [hg, hu])
        (by unfold Traversal.innerLoc; omega_using [hu, he]) (by unfold Traversal.innerLoc; omega_using [he, hj, hi]),hf i e he]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end

/-! ## From `InverseBankFieldPackedLayer.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/InverseBankFieldPackedBounds.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64

/-- A packed layer doubles the bound only for the register pairs it has
already processed; the following pair still has the old bound. -/
def PackedProgress (v : Vector (BitVec 128) 8) (g : Nat) (b : Int) : Prop :=
  ∀ i : Fin 8, ∀ e<4,
    -(if i.val<2*g then 2*b else b)≤(vword v[i.val] e).toInt ∧
      (vword v[i.val] e).toInt≤(if i.val<2*g then 2*b else b)

theorem PackedProgress.pair {v : Vector (BitVec 128) 8} {g : Nat} {b : Int}
    (h : PackedProgress v g b) (hg : g<4) {i : Nat} (hi : i<8) :
    -b≤(pairWord v[2*g] v[2*g+1] i).toInt ∧ (pairWord v[2*g] v[2*g+1] i).toInt≤b := by
  unfold pairWord
  split
  · have hv := h ⟨2*g,by omega_using [hg]⟩ i ‹_›
    simpa only [show ¬2*g<2*g by omega_using [],ite_false] using hv
  · have hv := h ⟨2*g+1,by omega_using [hg]⟩ (i-4) (by omega_using [hi])
    simpa only [show ¬2*g+1<2*g by omega_using [],ite_false] using hv

theorem packedValues_progress (v : Vector (BitVec 128) 8) {g len : Nat} (hg : g<4)
    (hl : len=1 ∨ len=2) (z : Nat → Int) {b : Int} (hb : 8380417≤b)
    (hs : 2*b<2147483648) (hv : PackedProgress v g b) :
    PackedProgress (packedValues v ⟨2*g,by omega_using [hg]⟩ ⟨2*g+1,by omega_using [hg]⟩ len z) (g+1) b := by
  intro i e he
  simp only [packedValues,Vector.getElem_set]
  by_cases hj : 2*g+1=i.val
  · rw [ite_eq_left hj,ite_eq_left (by omega_using [hj] : i.val<2*(g+1))]
    exact packedResult_bound _ _ hl true z he hb hs (fun j hj => hv.pair hg hj)
  · rw [ite_eq_right hj]
    by_cases hi : 2*g=i.val
    · rw [ite_eq_left hi,ite_eq_left (by omega_using [hi] : i.val<2*(g+1))]
      exact packedResult_bound _ _ hl false z he hb hs (fun j hj => hv.pair hg hj)
    · rw [ite_eq_right hi]
      have heq : (i.val<2*(g+1)) ↔ (i.val<2*g) := by omega_using [hj, hi]
      simpa only [heq] using hv i e he

theorem packedProgress_zero (v : Vector (BitVec 128) 8) (b : Int) :
    PackedProgress v 0 b ↔ BankBound v b := by
  simp only [PackedProgress,BankBound,Nat.mul_zero,Nat.not_lt_zero,ite_false]

theorem packedProgress_four (v : Vector (BitVec 128) 8) (b : Int) :
    PackedProgress v 4 b ↔ BankBound v (2*b) := by
  constructor <;> intro h i e he
  all_goals have hi : i.val<2*4 := i.isLt
  · simpa only [hi,ite_true] using h i e he
  · simpa only [hi,ite_true] using h i e he

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def packedLayerValues (len : Nat) (root : Nat → Nat → Nat) (g : Nat) :
    Nat → Vector (BitVec 128) 8 → Vector (BitVec 128) 8
  | 0,v => v
  | n+1,v => packedLayerValues len root (g+1) n
      (packedValues v ⟨(2*g)%8,Nat.mod_lt _ (by decide)⟩
        ⟨(2*g+1)%8,Nat.mod_lt _ (by decide)⟩ len (fun e => (negZetaNat (root g e) : Int)))

def packedLayerOps (u len : Nat) (root : Nat → Nat → Nat) (g : Nat) : Nat → List InverseTraversal.Op
  | 0 => []
  | n+1 => InverseTraversal.packedSchedule (32*u+8*g) len (root g) ++ packedLayerOps u len root (g+1) n

theorem packedLayer_values (v : Vector (BitVec 128) 8) (w : Poly) {u len g n : Nat}
    (hu : u<8) (hl : len=1 ∨ len=2) (hgn : g+n≤4) (root : Nat → Nat → Nat)
    {b : Int} (hb : 8380417≤b) (hs : 2*b<2147483648)
    (hv : PackedProgress v g b) (hf : InnerBankField u v w) :
    PackedProgress (packedLayerValues len root g n v) (g+n) b ∧
      InnerBankField u (packedLayerValues len root g n v)
        (InverseTraversal.run (packedLayerOps u len root g n) w) := by
  induction n generalizing g v w with
  | zero => exact ⟨hv,hf⟩
  | succ n ih =>
    have hg : g<4 := by omega_using [hgn]
    have hm0 : 2*g%8=2*g := Nat.mod_eq_of_lt (by omega_using [hgn])
    have hm1 : (2*g+1)%8=2*g+1 := Nat.mod_eq_of_lt (by omega_using [hgn])
    have hp := packedValues_progress v hg hl (fun e => (negZetaNat (root g e) : Int)) hb hs hv
    have hfield := packedValues_field v w hg hl hu (root g) hb hs
      (fun j hj => hv.pair hg hj) hf
    have hi := ih _ _ (g := g+1) (by omega_using [hgn]) hp hfield
    simpa only [packedLayerValues,packedLayerOps,hm0,hm1,InverseTraversal.run_append,
      Nat.add_assoc,Nat.add_comm 1 n] using hi

theorem packedLayer_full (v : Vector (BitVec 128) 8) (w : Poly) {u len : Nat}
    (hu : u<8) (hl : len=1 ∨ len=2) (root : Nat → Nat → Nat)
    {b : Int} (hb : 8380417≤b) (hs : 2*b<2147483648)
    (hv : BankBound v b) (hf : InnerBankField u v w) :
    BankBound (packedLayerValues len root 0 4 v) (2*b) ∧
      InnerBankField u (packedLayerValues len root 0 4 v)
        (InverseTraversal.run (packedLayerOps u len root 0 4) w) := by
  have h := packedLayer_values v w hu hl (g := 0) (n := 4) (by decide) root hb hs
    ((packedProgress_zero v b).mpr hv) hf
  exact ⟨(packedProgress_four _ b).mp h.1,h.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseBankFieldPackedPass.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def packedIndex (u len g e : Nat) : Nat :=
  256/len-1-(16*u/len+4*g/len+e/len)

def packedPassValues (u : Nat) (v : Vector (BitVec 128) 8) : Vector (BitVec 128) 8 :=
  packedLayerValues 2 (packedIndex u 2) 0 4 (packedLayerValues 1 (packedIndex u 1) 0 4 v)

def packedPassOps (u : Nat) : List InverseTraversal.Op :=
  packedLayerOps u 1 (packedIndex u 1) 0 4 ++ packedLayerOps u 2 (packedIndex u 2) 0 4

theorem packedPass_field (v : Vector (BitVec 128) 8) (w : Poly) {u : Nat} (hu : u<8)
    (hv : BankBound v 8380417) (hf : InnerBankField u v w) :
    BankBound (packedPassValues u v) 33521668 ∧
      InnerBankField u (packedPassValues u v) (InverseTraversal.run (packedPassOps u) w) := by
  have h1 := packedLayer_full v w hu (Or.inl rfl) (packedIndex u 1) (by decide) (by decide) hv hf
  have h2 := packedLayer_full _ _ hu (Or.inr rfl) (packedIndex u 2) (by decide) (by decide) h1.1 h1.2
  simpa only [packedPassValues,packedPassOps,InverseTraversal.run_append,Int.reduceMul] using h2

theorem packedRoot_index (u g len : Nat) (hl : len=1 ∨ len=2) :
    packedRoot u g len=(fun e => (negZetaNat (packedIndex u len g e) : Int)) := by
  funext e
  have hi : (if len=1 then 255-16*u-4*g-e else 127-8*u-2*g-e/2)=packedIndex u len g e := by
    rcases hl with rfl | rfl <;> simp [packedIndex] <;> omega_using []
  unfold packedRoot
  rw [hi]
  rfl

theorem packedPassValues_eq (u : Nat) (v : Vector (BitVec 128) 8) :
    packedRunValues v (packedRoot u) packedSteps=packedPassValues u v := by
  have h1 := fun g => packedRoot_index u g 1 (Or.inl rfl)
  have h2 := fun g => packedRoot_index u g 2 (Or.inr rfl)
  simp only [packedRunValues,packedSteps,h1,h2,packedPassValues,packedLayerValues]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseBankField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The physical packed groups and renamed groups visit exactly the logical
local slice, retaining each root index symbolically. -/
theorem fiveOps_eq {u : Nat} (hu : u<8) :
    packedPassOps u ++ runOps u (localIndex u) 0 7=InverseTraversal.localSlice u := by
  exact (show ∀ u : Fin 8,
    packedPassOps u.val ++ runOps u.val (localIndex u.val) 0 7=InverseTraversal.localSlice u.val
    by decide +kernel) ⟨u,hu⟩

/-- The selected five-layer machine bank has the exact inverse field result,
with every signed representative bounded by 32q. No normalization is added. -/
theorem fiveValues_field (v : Vector (BitVec 128) 8) (w : Poly) {u : Nat} (hu : u<8)
    (hv : BankBound v 8380417) (hf : InnerBankField u v w) :
    BankBound (fiveValues u v) 268173344 ∧
      InnerBankField u (fiveValues u v) (InverseTraversal.run (InverseTraversal.localSlice u) w) := by
  rw [fiveValues,packedPassValues_eq]
  have hp := packedPass_field v w hu hv hf
  have h := runValues_local _ _ hu hp.1 hp.2
  refine ⟨h.1,?_⟩
  simpa only [← InverseTraversal.run_append,fiveOps_eq hu] using h.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
