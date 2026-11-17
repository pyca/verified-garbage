module

import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRun
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Slice
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedRun
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

/-! ### `MlDsa.AArch64.Optimized.InverseScale`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

def scalePairs : List (VReg × VReg) := (List.finRange 4).map fun j => ((regs 7)[j.val],VG.Impl.MlDsa.AArch64.Optimized.Inverse.qt j.val)
def scaleLoad : List Instr := [.vop (.dupE .s4 .v20 .v30 0),.vop (.dupE .s4 .v21 .v30 1)]
def scaleCode : List Instr := scaleLoad ++ multiplyCode scalePairs

def scaleValues (v : Vector (BitVec 128) 8) : Vector (BitVec 128) 8 :=
  Vector.ofFn fun j => if j.val<4 then fastVector v[j.val] (fun _ => 16382) else v[j.val]

def ScaleRoots (s : State) : Prop :=
  vword (s.v .v30) 0=BitVec.ofInt 32 16382 ∧
  vword (s.v .v30) 1=BitVec.ofInt 32 (reciprocal 16382)

theorem scaleLoad_ok {s : State} {rest : List Instr} {Q : State → Prop} (h : ScaleRoots s)
    (k : ∀ t, VChg [.v20,.v21] s t →
      (∀ e<4, vword (t.v .v20) e=BitVec.ofInt 32 16382) →
      (∀ e<4, vword (t.v .v21) e=BitVec.ofInt 32 (reciprocal 16382)) → WP isa (.block rest) t Q) :
    WP isa (.block (scaleLoad ++ rest)) s Q := by
  refine wp_vop (d := .v20) rfl fun s₁ h₁ => wp_vop (d := .v21) rfl fun t h₂ => ?_
  refine k t (h₁.chg.trans h₂.chg) ?_ ?_
  · intro e he
    rw [h₂.get .v20,h₁.v,VG.AArch64.vword_map2 _ _ _ he]
    exact h.1
  · intro e he
    rw [h₂.v,VG.AArch64.vword_map2 _ _ _ he,h₁.get .v30]
    exact h.2

theorem scale_geometry :
    (scalePairs.map Prod.fst).Nodup ∧ (scalePairs.map Prod.snd).Nodup ∧
    (∀ p∈scalePairs, p.1∉scalePairs.map Prod.snd) ∧
    (∀ p∈scalePairs, p.2∉scalePairs.map Prod.fst) ∧
    .v20∉scalePairs.map Prod.fst ∧ .v20∉scalePairs.map Prod.snd ∧
    .v21∉scalePairs.map Prod.snd ∧ .v31∉scalePairs.map Prod.fst ∧ .v31∉scalePairs.map Prod.snd := by decide +kernel

theorem scale_index (j : Fin 8) :
    (j.val<4 → ∃ tmp, ((regs 7)[j.val],tmp)∈scalePairs) ∧
    (¬j.val<4 → (regs 7)[j.val]∉scalePairs.map Prod.snd++scalePairs.map Prod.fst) := by
  have h : ∀ j : Fin 8,
      (j.val<4 → ((regs 7)[j.val],VG.Impl.MlDsa.AArch64.Optimized.Inverse.qt j.val)∈scalePairs) ∧
      (¬j.val<4 → (regs 7)[j.val]∉scalePairs.map Prod.snd++scalePairs.map Prod.fst) := by decide +kernel
  exact ⟨fun hj => ⟨_,(h j).1 hj⟩,(h j).2⟩

theorem scale_ok {s : State} {rest : List Instr} {Q : State → Prop} {v : Vector (BitVec 128) 8}
    (hb : Bank s (regs 7) v) (hs : ScaleRoots s)
    (hq : ∀ e<4, vword (s.v .v31) e=8380417#32)
    (k : ∀ t, VChg runRegs s t → Bank t (regs 7) (scaleValues v) → WP isa (.block rest) t Q) :
    WP isa (.block (scaleCode ++ rest)) s Q := by
  unfold scaleCode
  rw [List.append_assoc]
  refine scaleLoad_ok hs fun s₁ hc₁ hz₁ hb₁ => ?_
  obtain ⟨hd,ht,hdt,htd,hzd,hzt,hbt,hqd,hqt⟩ := scale_geometry
  have bank₁ : Bank s₁ (regs 7) v := by
    intro j
    rw [hc₁.get _ ((show ∀ j : Fin 8, (regs 7)[j.val]∉[.v20,.v21] by decide +kernel) j)]
    exact hb j
  have hq₁ : ∀ e<4, vword (s₁.v .v31) e=8380417#32 := by
    intro e he
    rw [hc₁.get .v31 (by decide)]
    exact hq e he
  have heq : multiplyCode scalePairs=
      scalePairs.map (fun p => Instr.vop (.sqdmulh p.2 p.1 .v21)) ++
      (scalePairs.map Prod.fst).map (fun d => Instr.vop (.mul d d .v20)) ++
      scalePairs.map (fun p => Instr.vop (.mls p.1 p.2 .v31)) := by
    simp only [multiplyCode,List.map_map,Function.comp_def]
  rw [heq]
  refine multiply_batch_ok scalePairs .v20 .v21 .v31 hd ht hdt htd hzd hzt hbt hqd hqt
    (z := fun _ => 16382) (by intro e he; decide) hz₁ hb₁ hq₁ fun t hc₂ hv => ?_
  refine k t (VChg.mono (hc₁.trans hc₂) (by decide +kernel)) ?_
  intro j
  simp only [scaleValues,Vector.getElem_ofFn]
  by_cases hj : j.val<4
  · rw [ite_eq_left hj]
    obtain ⟨tmp,htmp⟩ := (scale_index j).1 hj
    apply VG.AArch64.vec_ext
    intro e he
    rw [hv _ htmp e he,bank₁ j,fastVector_word _ _ he]
  · rw [ite_eq_right hj,hc₂.get _ ((scale_index j).2 hj)]
    exact bank₁ j

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseFinalRoots`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def finalValue (i : Nat) : Nat :=
  if i<4 then VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (7-i)
  else if i<6 then VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (3-(i-4))
  else (VG.Impl.MlDsa.AArch64.Optimized.Inverse.z 1*16382)%8380417

def finalZ (i : Nat) (_e : Nat) : Int := finalValue i

def finalRootReg (i : Nat) : VReg := if i<4 then .v22 else if i<6 then .v23 else .v30
def finalRecipReg (i : Nat) : VReg := if i<4 then .v28 else if i<6 then .v29 else .v30
def finalRootLane (i : Nat) : Nat := if i<4 then i else if i<6 then i-4 else 2
def finalRecipLane (i : Nat) : Nat := if i<4 then i else if i<6 then i-4 else 3

def finalLoad (i : Nat) : List Instr :=
  [.vop (.dupE .s4 .v20 (finalRootReg i) (finalRootLane i)),
   .vop (.dupE .s4 .v21 (finalRecipReg i) (finalRecipLane i))]

structure FinalRoots (s : State) : Prop where
  root : ∀ i : Fin 7, vword (s.v (finalRootReg i.val)) (finalRootLane i.val)=BitVec.ofInt 32 (finalZ i.val 0)
  recip : ∀ i : Fin 7, vword (s.v (finalRecipReg i.val)) (finalRecipLane i.val)=BitVec.ofInt 32 (reciprocal (finalZ i.val 0))
  q : ∀ e<4, vword (s.v .v31) e=8380417#32

def finalConstants : List VReg := [.v22,.v23,.v28,.v29,.v30,.v31]

theorem FinalRoots.frame {s t : State} {vs : List VReg} (h : FinalRoots s)
    (hc : VChg vs s t) (hv : ∀ r∈finalConstants, r∉vs) : FinalRoots t := by
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [hc.get _ (hv _ ((show ∀ i : Fin 7, finalRootReg i.val∈finalConstants by decide +kernel) i))]
    exact h.root i
  · intro i
    rw [hc.get _ (hv _ ((show ∀ i : Fin 7, finalRecipReg i.val∈finalConstants by decide +kernel) i))]
    exact h.recip i
  · intro e he
    rw [hc.get _ (hv _ (by decide))]
    exact h.q e he

theorem finalZ_range (i e : Nat) : 0≤finalZ i e ∧ finalZ i e<8380417 := by
  have hz (j : Nat) : VG.Impl.MlDsa.AArch64.Optimized.Inverse.z j<8380417 := Nat.mod_lt _ (by decide)
  have hv : finalValue i<8380417 := by
    unfold finalValue
    repeat' split
    · exact hz _
    · exact hz _
    · exact Nat.mod_lt _ (by decide)
  exact ⟨Int.natCast_nonneg _,Int.ofNat_lt.mpr hv⟩

theorem finalLoad_ok (i : Fin 7) {s : State} {rest : List Instr} {Q : State → Prop}
    (h : FinalRoots s)
    (k : ∀ t, VChg [.v20,.v21] s t → FinalRoots t →
      (∀ e<4, vword (t.v .v20) e=BitVec.ofInt 32 (finalZ i.val e)) →
      (∀ e<4, vword (t.v .v21) e=BitVec.ofInt 32 (reciprocal (finalZ i.val e))) →
      WP isa (.block rest) t Q) :
    WP isa (.block (finalLoad i.val ++ rest)) s Q := by
  have hi : finalRootLane i.val<4 ∧ finalRecipLane i.val<4 ∧ finalRecipReg i.val≠.v20 :=
    (show ∀ i : Fin 7, finalRootLane i.val<4 ∧ finalRecipLane i.val<4 ∧ finalRecipReg i.val≠.v20 by decide +kernel) i
  unfold finalLoad
  simp only [List.cons_append,List.nil_append]
  have he (t : State) (d a : VReg) (j : Nat) (hj : j<4) :
      (VOp.dupE .s4 d a j).eval t=some (d,
        VArr.s4.map2 (fun w _ _ => (t.v a).extractLsb' (w*j) w) 0 0) := by
    simp only [reduceVOpEval,VArr.esize,show 128/32=4 by decide,hj,ite_true]
  refine VG.Proof.MlKem.AArch64.wp_vop (he s .v20 _ _ hi.1) fun s₁ h₁ =>
    VG.Proof.MlKem.AArch64.wp_vop (he s₁ .v21 _ _ hi.2.1) fun t h₂ => ?_
  have hc' : VChg [.v20,.v21] s t := h₁.chg.trans h₂.chg
  refine k t hc' (h.frame hc' (by decide)) ?_ ?_
  · intro e he
    rw [h₂.get .v20,h₁.v,VG.AArch64.vword_map2 _ _ _ he]
    exact h.root i
  · intro e he
    rw [h₂.v,VG.AArch64.vword_map2 _ _ _ he,h₁.get _ hi.2.2]
    exact h.recip i

def finalPlan : RootPlan where
  load := finalLoad
  value := finalZ
  invariant := FinalRoots
  range i e _ := finalZ_range i.val e
  stable i _ _ hc hs := hs.frame hc ((show ∀ i : Fin 7, ∀ r∈finalConstants, r∉stageClobs i.val by decide +kernel) i)
  load_ok i _ _ _ hs k := finalLoad_ok i hs fun t hc ht hz hb => k t hc ht hz hb ht.q

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseFinalStore`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.InverseCanonicalBank`, which only this module used -/

section

/-! ## From `InverseCanonicalBatch.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def signVector (v : BitVec 128) : BitVec 128 := VArr.s4.map2 (fun _ x _ => x.sshiftRight 31) v 0

def correctedVector (v q : BitVec 128) : BitVec 128 := VArr.s4.map2 (fun _ x y => x+y) v (signVector v &&& q)

def canonicalVector (v q : BitVec 128) : BitVec 128 :=
  let a := correctedVector v q
  VArr.s4.map2 (fun _ x y => if x.toNat≤y.toNat then x else y) a
    (VArr.s4.map2 (fun _ x y => x-y) a q)

def canonicalBatchCode (ps : List (VReg × VReg)) (qr : VReg) : List Instr :=
  (ps.map fun p => Instr.vop (.shift .sshr .s4 p.2 p.1 31)) ++
  (ps.map fun p => Instr.vop (.logic .and p.2 p.2 qr)) ++
  (ps.map fun p => Instr.vop (.add .s4 p.1 p.1 p.2)) ++
  (ps.map fun p => Instr.vop (.sub .s4 p.2 p.1 qr)) ++
  (ps.map fun p => Instr.vop (.umin p.1 p.1 p.2))

/-- The selected inverse normalizes four registers phase-by-phase. Every
cross-phase dependency and untouched source is retained explicitly. -/
theorem canonicalBatch_ok (ps : List (VReg × VReg)) (qr : VReg)
    (hd : (ps.map Prod.fst).Nodup) (ht : (ps.map Prod.snd).Nodup)
    (hdt : ∀ p∈ps, p.1∉ps.map Prod.snd) (htd : ∀ p∈ps, p.2∉ps.map Prod.fst)
    (hqd : qr∉ps.map Prod.fst) (hqt : qr∉ps.map Prod.snd)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg (ps.map Prod.snd++ps.map Prod.fst) s t →
      (∀ p∈ps, t.v p.1=canonicalVector (s.v p.1) (s.v qr)) → WP isa (.block rest) t Q) :
    WP isa (.block (canonicalBatchCode ps qr ++ rest)) s Q := by
  simp only [canonicalBatchCode,List.append_assoc]
  refine parallel_ok ps Prod.snd (fun p => .shift .sshr .s4 p.2 p.1 31)
    (fun p => signVector (s.v p.1)) ht ?_ fun s₁ hc₁ hv₁ => ?_
  · intro t hc p hp _
    change some (p.2,signVector (t.v p.1))=_
    rw [hc.get p.1 (hdt p hp)]
  · refine parallel_ok ps Prod.snd (fun p => .logic .and p.2 p.2 qr)
      (fun p => s₁.v p.2 &&& s₁.v qr) ht ?_ fun s₂ hc₂ hv₂ => ?_
    · intro t hc p _ hself
      change some (p.2,t.v p.2 &&& t.v qr)=_
      rw [hself,hc.get qr hqt]
    · refine parallel_ok ps Prod.fst (fun p => .add .s4 p.1 p.1 p.2)
        (fun p => VArr.s4.map2 (fun _ x y => x+y) (s₂.v p.1) (s₂.v p.2)) hd ?_
        fun s₃ hc₃ hv₃ => ?_
      · intro t hc p hp hself
        change some (p.1,VArr.s4.map2 (fun _ x y => x+y) (t.v p.1) (t.v p.2))=_
        rw [hself,hc.get p.2 (htd p hp)]
      · have hadd p (hp : p∈ps) : s₃.v p.1=correctedVector (s.v p.1) (s.v qr) := by
          rw [hv₃ p hp,hc₂.get p.1 (hdt p hp),hc₁.get p.1 (hdt p hp),hv₂ p hp,hv₁ p hp,hc₁.get qr hqt]
          rfl
        refine parallel_ok ps Prod.snd (fun p => .sub .s4 p.2 p.1 qr)
          (fun p => VArr.s4.map2 (fun _ x y => x-y) (s₃.v p.1) (s₃.v qr)) ht ?_
          fun s₄ hc₄ hv₄ => ?_
        · intro t hc p hp _
          change some (p.2,VArr.s4.map2 (fun _ x y => x-y) (t.v p.1) (t.v qr))=_
          rw [hc.get p.1 (hdt p hp),hc.get qr hqt]
        · refine parallel_ok ps Prod.fst (fun p => .umin p.1 p.1 p.2)
            (fun p => VArr.s4.map2 (fun _ x y => if x.toNat≤y.toNat then x else y) (s₄.v p.1) (s₄.v p.2)) hd ?_
            fun t hc₅ hv₅ => ?_
          · intro t hc p hp hself
            change some (p.1,VArr.s4.map2 (fun _ x y => if x.toNat≤y.toNat then x else y) (t.v p.1) (t.v p.2))=_
            rw [hself,hc.get p.2 (htd p hp)]
          · refine k t (VChg.mono ((((hc₁.trans hc₂).trans hc₃).trans hc₄).trans hc₅) ?_) ?_
            · intro r hr
              simp only [List.mem_append] at *
              grind only
            · intro p hp
              rw [hv₅ p hp,hc₄.get p.1 (hdt p hp),hv₄ p hp,hadd p hp,
                hc₃.get qr hqd,hc₂.get qr hqt,hc₁.get qr hqt]
              rfl


theorem canonicalVector_word (v q : BitVec 128) {e : Nat} (he : e<4)
    (hq : vword q e=8380417#32) :
    vword (canonicalVector v q) e=canonicalWord (vword v e) := by
  have ha : vword (correctedVector v q) e=
      vword v e+((vword v e).sshiftRight 31 &&& 8380417#32) := by
    rw [correctedVector,VG.AArch64.vword_map2 _ _ _ he,word_and,hq,
      signVector,VG.AArch64.vword_map2 _ _ _ he]
  rw [canonicalVector,VG.AArch64.vword_map2 _ _ _ he,umin_word,
    VG.AArch64.vword_map2 _ _ _ he,hq,ha]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseCanonicalBank.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def halfPairs (half : Fin 2) : List (VReg × VReg) :=
  (List.finRange 4).map fun j => ((regs 7)[4*half.val+j.val],VG.Impl.MlDsa.AArch64.Optimized.Inverse.qt j.val)

def halfValues (half : Fin 2) (v : Vector (BitVec 128) 8) (q : BitVec 128) : Vector (BitVec 128) 8 :=
  Vector.ofFn fun j => if 4*half.val≤j.val ∧ j.val<4*half.val+4 then canonicalVector v[j.val] q else v[j.val]

theorem half_geometry (half : Fin 2) :
    ((halfPairs half).map Prod.fst).Nodup ∧ ((halfPairs half).map Prod.snd).Nodup ∧
    (∀ p∈halfPairs half, p.1∉(halfPairs half).map Prod.snd) ∧
    (∀ p∈halfPairs half, p.2∉(halfPairs half).map Prod.fst) ∧
    .v31∉(halfPairs half).map Prod.fst ∧ .v31∉(halfPairs half).map Prod.snd := by
  revert half
  decide +kernel

theorem half_index (half : Fin 2) (j : Fin 8) :
    ((4*half.val≤j.val ∧ j.val<4*half.val+4) →
      ((regs 7)[j.val],VG.Impl.MlDsa.AArch64.Optimized.Inverse.qt (j.val-4*half.val))∈halfPairs half) ∧
    (¬(4*half.val≤j.val ∧ j.val<4*half.val+4) →
      (regs 7)[j.val]∉(halfPairs half).map Prod.snd++(halfPairs half).map Prod.fst) := by
  revert half j
  decide +kernel

theorem canonicalBank_ok (half : Fin 2)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Vector (BitVec 128) 8}
    (hb : Bank s (regs 7) v)
    (k : ∀ t, VChg runRegs s t → Bank t (regs 7) (halfValues half v (s.v .v31)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (canonicalBatchCode (halfPairs half) .v31 ++ rest)) s Q := by
  obtain ⟨hd,ht,hdt,htd,hqd,hqt⟩ := half_geometry half
  refine canonicalBatch_ok (halfPairs half) .v31 hd ht hdt htd hqd hqt fun t hc hv => ?_
  have hm : ∀ half : Fin 2, (halfPairs half).map Prod.snd++(halfPairs half).map Prod.fst⊆runRegs := by decide +kernel
  refine k t (hc.mono (hm half)) ?_
  intro j
  simp only [halfValues,Vector.getElem_ofFn]
  by_cases hj : 4*half.val≤j.val ∧ j.val<4*half.val+4
  · rw [ite_eq_left hj,hv _ ((half_index half j).1 hj),hb j]
  · rw [ite_eq_right hj,hc.get _ ((half_index half j).2 hj)]
    exact hb j

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end


/-! ## From `InverseHalfStore.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)

def halfStores (half : Fin 2) : List (VReg × Nat) :=
  (List.finRange 4).map fun j => ((regs 7)[4*half.val+j.val],128*(4*half.val+j.val))

def halfCode (half : Fin 2) : List Instr := canonicalBatchCode (halfPairs half) .v31 ++
  (halfStores half).map (fun p => Instr.strq p.1 .x2 p.2)

def halfWrite (half : Fin 2) (v : Vector (BitVec 128) 8) (base : Addr) (m : Mem) : Mem :=
  (List.finRange 4).foldl (fun m j => m.write (base+BitVec.ofNat 64 (128*(4*half.val+j.val))) 16 v[4*half.val+j.val]) m

theorem half_writeSlice {s : State} {v : Vector (BitVec 128) 8} (half : Fin 2)
    (hb : Bank s (regs 7) v) (base : Addr) :
    writeSlice (halfStores half) base s.v s.mem=halfWrite half v base s.mem := by
  simp only [writeSlice,halfStores,List.foldl_map,halfWrite]
  congr 1
  funext m j
  rw [hb ⟨4*half.val+j.val,by omega_using []⟩]

theorem halfStore_ok (half : Fin 2) {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Vector (BitVec 128) 8} (hb : Bank s (regs 7) v)
    (hw : ∀ i : Fin 8, InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (128*i.val)) 16)
    (k : ∀ t, (∃ mid, VChg runRegs s mid ∧
        VMem mid t (halfWrite half (halfValues half v (s.v .v31)) (s.gpr .x2) s.mem)) →
      Bank t (regs 7) (halfValues half v (s.v .v31)) → WP isa (.block rest) t Q) :
    WP isa (.block (halfCode half ++ rest)) s Q := by
  simp only [halfCode,List.append_assoc]
  refine canonicalBank_ok half hb fun mid hc hb' => ?_
  refine store_many_ok (halfStores half) .x2 ?_ ?_ fun t hm => ?_
  · intro p hp
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
    omega_using []
  · intro p hp
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
    simpa only [hc.wr,hc.gpr] using hw ⟨4*half.val+j.val,by omega_using []⟩
  · rw [half_writeSlice half hb',hc.gpr,hc.mem] at hm
    refine k t ⟨mid,hc,hm⟩ ?_
    intro j
    rw [hm.v]
    exact hb' j

/-- Arithmetic and stores may be interleaved without weakening the final
register frame: memory is restored only in the intermediate witness. -/
theorem frame_store_trans {s a b c t : State} {m₁ m₂ : Mem}
    (ha : VChg runRegs s a) (hb : VMem a b m₁)
    (hc : VChg runRegs b c) (ht : VMem c t m₂) :
    ∃ mid, VChg runRegs s mid ∧ VMem mid t m₂ := by
  refine ⟨{c with mem := s.mem},?_,?_⟩
  · refine ⟨?_,hc.gpr.trans (hb.gpr.trans ha.gpr),rfl,
      hc.rd.trans (hb.rd.trans ha.rd),hc.wr.trans (hb.wr.trans ha.wr),
      hc.sp.trans (hb.sp.trans ha.sp)⟩
    intro r hr
    change c.v r=s.v r
    rw [hc.get r hr,hb.v,ha.get r hr]
  · exact ⟨ht.gpr,ht.v,ht.mem,ht.rd,ht.wr,ht.sp⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseFinalStore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)

def canonicalValues (v : Vector (BitVec 128) 8) (q : BitVec 128) : Vector (BitVec 128) 8 :=
  Vector.ofFn fun j => canonicalVector v[j.val] q

def finalStoreCode : List Instr := halfCode 0 ++ halfCode 1

theorem halfValues_both (v : Vector (BitVec 128) 8) (q : BitVec 128) :
    halfValues 1 (halfValues 0 v q) q=canonicalValues v q := by
  refine Vector.ext fun j hj => ?_
  simp only [halfValues, canonicalValues, Vector.getElem_ofFn, Fin.isValue, Fin.val_zero, Fin.val_one,
    Nat.mul_zero, Nat.zero_add, Nat.zero_le, true_and, Nat.mul_one]
  by_cases h : j < 4
  · simp only [h, ite_true, show ¬(4 ≤ j ∧ j < 8) by omega_using [h], ite_false]
  · simp only [h, ite_false, show 4 ≤ j ∧ j < 8 by omega_using [hj, h], and_self, ite_true]

/-- The two halves of a bank write the whole bank. -/
theorem halfWrite_halves (c : Vector (BitVec 128) 8) (p : Addr) (m : Mem) :
    halfWrite 1 c p (halfWrite 0 c p m) = writeBank c p 128 m := rfl

theorem halfWrite_congr {half : Fin 2} {v w : Vector (BitVec 128) 8}
    (h : ∀ j : Fin 4, v[4*half.val+j.val] = w[4*half.val+j.val]) (p : Addr) (m : Mem) :
    halfWrite half v p m = halfWrite half w p m := by
  unfold halfWrite
  congr 1
  funext m j
  rw [h j]

theorem halfWrite_both (v : Vector (BitVec 128) 8) (q : BitVec 128) (p : Addr) (m : Mem) :
    halfWrite 1 (halfValues 1 (halfValues 0 v q) q) p (halfWrite 0 (halfValues 0 v q) p m)=
      writeBank (canonicalValues v q) p 128 m := by
  have h0 : halfWrite 0 (halfValues 0 v q) p m = halfWrite 0 (canonicalValues v q) p m :=
    halfWrite_congr (fun j => by
      simp only [halfValues, canonicalValues, Vector.getElem_ofFn, Fin.isValue, Fin.val_zero,
        Nat.mul_zero, Nat.zero_add, Nat.zero_le, true_and, j.isLt, ite_true]) p m
  rw [halfValues_both, h0, halfWrite_halves]

theorem finalStore_ok {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Vector (BitVec 128) 8} (hb : Bank s (regs 7) v)
    (hw : ∀ i : Fin 8, InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (128*i.val)) 16)
    (k : ∀ t, (∃ mid, VChg runRegs s mid ∧
        VMem mid t (writeBank (canonicalValues v (s.v .v31)) (s.gpr .x2) 128 s.mem)) →
      Bank t (regs 7) (canonicalValues v (s.v .v31)) → WP isa (.block rest) t Q) :
    WP isa (.block (finalStoreCode ++ rest)) s Q := by
  simp only [finalStoreCode,List.append_assoc]
  refine halfStore_ok 0 hb hw fun s₁ ⟨a,ha,hm₁⟩ hb₁ => ?_
  have hq : s₁.v .v31=s.v .v31 := by rw [hm₁.v,ha.get .v31 (by decide)]
  refine halfStore_ok 1 hb₁ ?_ fun t ⟨b,hb',hm₂⟩ hbt => ?_
  · intro i
    simpa only [hm₁.wr,hm₁.gpr,ha.wr,ha.gpr] using hw i
  · have hm₂' : VMem b t (writeBank (canonicalValues v (s.v .v31)) (s.gpr .x2) 128 s.mem) := by
      simpa only [hq,hm₁.gpr,ha.gpr,hm₁.mem,halfWrite_both] using hm₂
    refine k t (frame_store_trans ha hm₁ hb' hm₂') ?_
    simpa only [hq,halfValues_both] using hbt

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)

def finalLoads : List Instr := (bankLoads (regs 0) 128).map (fun p => Instr.ldrq p.1 .x2 p.2)
def finalSliceCode : List Instr := finalLoads ++ runCode finalLoad 0 7 ++ scaleCode ++ finalStoreCode
def finalAdvance : List Instr := [.addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1]

def finalValues (v : Vector (BitVec 128) 8) (q : BitVec 128) : Vector (BitVec 128) 8 :=
  canonicalValues (scaleValues (runValues finalZ 0 7 v)) q

def finalSliceMem (s : State) : Mem :=
  writeBank (finalValues (readBank s.mem (s.gpr .x2) 128) (s.v .v31)) (s.gpr .x2) 128 s.mem

theorem finalBody_eq : VG.Impl.MlDsa.AArch64.Optimized.Inverse.finalBody=
    finalSliceCode ++ finalAdvance := by kernel_rfl

theorem finalSlice_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hf : FinalRoots s) (hs : ScaleRoots s)
    (hr : ∀ i : Fin 8, InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (128*i.val)) 16)
    (hw : ∀ i : Fin 8, InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (128*i.val)) 16)
    (k : ∀ t, (∃ mid, VChg runRegs s mid ∧ VMem mid t (finalSliceMem s)) → WP isa (.block rest) t Q) :
    WP isa (.block (finalSliceCode ++ rest)) s Q := by
  have ho : ∀ i : Fin 8, (128*i.val)%16=0 ∧ 128*i.val<65536 := by intro i; omega_using []
  have hsub : ((bankLoads (regs 0) 128).map Prod.fst)⊆runRegs := by decide +kernel
  have hconst : ∀ r∈finalConstants, r∉runRegs := by decide
  simp only [finalSliceCode,finalLoads,List.append_assoc]
  refine loadBank_ok (regs 0) 128 .x2 initial_inj ho hr fun a hload hbank => ?_
  have hload' := hload.mono hsub
  have hf₁ := hf.frame hload' hconst
  refine run_ok finalPlan 0 7 (by decide) hbank hf₁ fun b hrun hf₂ hb => ?_
  have hsf : ScaleRoots b := by
    simpa only [ScaleRoots,hrun.get .v30 (by decide),hload'.get .v30 (by decide)] using hs
  refine scale_ok hb hsf hf₂.q fun c hscale hc => ?_
  refine finalStore_ok hc ?_ fun t ⟨d,hcanon,hm⟩ _ => ?_
  · intro i
    simpa only [hscale.wr,hscale.gpr,hrun.wr,hrun.gpr,hload.wr,hload.gpr] using hw i
  · have hframe : VChg runRegs s d := VChg.mono (((hload'.trans hrun).trans hscale).trans hcanon) (by
      intro r h
      simpa only [List.mem_append,or_self] using h)
    have hm' : VMem d t (finalSliceMem s) := by
      simpa only [show finalPlan.value=finalZ from rfl,finalSliceMem,finalValues,hscale.mem,hscale.gpr,
        hscale.get .v31 (by decide),hrun.mem,hrun.gpr,hrun.get .v31 (by decide),
        hload.mem,hload.gpr,hload'.get .v31 (by decide)] using hm
    exact k t ⟨d,hframe,hm'⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
