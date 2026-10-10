import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstMemory
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalLoad
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory

/-! ## From `PairedFirstSource.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- The paired scratch writes cannot alter later challenge/source slices. -/
theorem valuesAt_frame_slice {m m' : Mem} {p a b : Addr} {u : Nat} (hu : u<8)
    (hf : Frame [⟨p,2048⟩] m m')
    (ha : (⟨a,1024⟩ : Region).Disjoint ⟨p,2048⟩)
    (hb : (⟨b,2048⟩ : Region).Disjoint ⟨p,2048⟩) :
    valuesAt m' (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u))=
      valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) := by
  funext poly
  apply Vector.ext
  intro j hj
  have ra : m'.read (a+BitVec.ofNat 64 (128*u+16*j)) 16=
      m.read (a+BitVec.ofNat 64 (128*u+16*j)) 16 :=
    hf.read (Offset.contains_base a (by omega : 128*u+16*j+16≤1024) (by omega))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact ha) (by decide)
  have rb : m'.read (b+BitVec.ofNat 64 (128*u+(1024*poly.val+16*j))) 16=
      m.read (b+BitVec.ofNat 64 (128*u+(1024*poly.val+16*j))) 16 :=
    hf.read (Offset.contains_base b (by omega : 128*u+(1024*poly.val+16*j)+16≤2048) (by omega))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hb) (by decide)
  simp only [valuesAt,Vector.getElem_ofFn,BitVec.add_assoc,←BitVec.ofNat_add,ra,rb]

/-- The machine memory recursion reads the same products as the original inputs. -/
theorem firstPass_valuesAt {m : Mem} {p a b : Addr} {u : Nat} (hu : u<8)
    (ha : (⟨a,1024⟩ : Region).Disjoint ⟨p,2048⟩)
    (hb : (⟨b,2048⟩ : Region).Disjoint ⟨p,2048⟩) :
    valuesAt (firstPassMem m p a b u) (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u))=
      valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) :=
  valuesAt_frame_slice hu (firstPass_frame (by omega)) ha hb
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedStoreRead.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def storeValues {α : Type} (xs : List α) (addr : α → Addr) (values : α → BitVec 128) (m : Mem) : Mem :=
 xs.foldl (fun m i => m.write (addr i) 16 (values i)) m

theorem storeValues_read_other {α : Type} (xs : List α) (addr : α → Addr)
    (values : α → BitVec 128) (m : Mem) (a : Addr)
    (hs : ∀i∈xs,Mem.Sep a 16 (addr i) 16) :
    (storeValues xs addr values m).read a 16=m.read a 16 := by
  induction xs generalizing m with
  | nil => rfl
  | cons i xs ih =>
    change (storeValues xs addr values (m.write (addr i) 16 (values i))).read a 16=_
    rw [ih _ (fun j hj => hs j (List.mem_cons_of_mem _ hj)),Mem.read_write_sep (hs i (by simp)) (by decide)]

theorem storeValues_read_slot {α : Type} [DecidableEq α] (xs : List α) (addr : α → Addr)
    (values : α → BitVec 128) (m : Mem) (i : α) (hi : i∈xs)
    (hs : ∀j∈xs,j≠i → Mem.Sep (addr i) 16 (addr j) 16) :
    (storeValues xs addr values m).read (addr i) 16=values i := by
  induction xs generalizing m with
  | nil => simp at hi
  | cons j xs ih =>
    change (storeValues xs addr values (m.write (addr j) 16 (values j))).read _ 16=_
    by_cases ht : i∈xs
    · exact ih _ ht (fun k hk => hs k (List.mem_cons_of_mem _ hk))
    · have he : i=j := (List.mem_cons.mp hi).resolve_right ht
      subst j
      rw [storeValues_read_other _ _ _ _ _ (fun k hk => hs k (List.mem_cons_of_mem _ hk)
        (by intro he; subst k; exact ht hk))]
      simpa only [Mem.writeW,Mem.readW,BitVec.setWidth_eq] using
        Mem.readW_writeW_self m (addr i) 16 (values i) (by decide)

def pairIndices : List (Fin 2 × Fin 8) :=
 (List.finRange 2).flatMap fun p => (List.finRange 8).map fun j => (p,j)

theorem pairIndices_mem (i : Fin 2 × Fin 8) : i∈pairIndices := by
  simp only [pairIndices,List.mem_flatMap,List.mem_map,List.mem_finRange,true_and]
  exact ⟨i.1,i.2,rfl⟩

theorem writePair_values (v : Values) (base : Addr) (stride : Nat) (m : Mem) :
    writePair v base stride m=storeValues pairIndices
      (fun i => base+BitVec.ofNat 64 (1024*i.1.val+stride*i.2.val))
      (fun i => (v i.1)[i.2.val]) m := by
  simp only [writePair,storeValues,pairIndices,List.foldl_flatMap,List.foldl_map]

theorem pair16_sep (base : Addr) {i j : Fin 2 × Fin 8} (hne : j≠i) :
    Mem.Sep (base+BitVec.ofNat 64 (1024*i.1.val+16*i.2.val)) 16
      (base+BitVec.ofNat 64 (1024*j.1.val+16*j.2.val)) 16 := by
  have hd : j.1.val≠i.1.val ∨ j.2.val≠i.2.val := by
    by_contra h
    simp only [not_or,not_not] at h
    exact hne (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
  exact Offset.sep base (by omega) (by omega) (by omega)

/-- Each stored 16-byte first-pass vector is recovered exactly from its own bank. -/
theorem writePair_read16 (v : Values) (base : Addr) (m : Mem) (p : Fin 2) (j : Fin 8) :
    (writePair v base 16 m).read (base+BitVec.ofNat 64 (1024*p.val+16*j.val)) 16=(v p)[j.val] := by
  rw [writePair_values]
  exact storeValues_read_slot _ _ _ _ (p,j) (pairIndices_mem _) (fun _ _ hn => pair16_sep base hn)
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedFirstRead.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem writePair_slice_other (v : Values) (base : Addr) (m : Mem)
    {u k : Nat} (hu : u<8) (hk : k<8) (hne : k≠u) (poly : Fin 2) (j : Fin 8) :
    (writePair v (base+BitVec.ofNat 64 (128*u)) 16 m).read
      ((base+BitVec.ofNat 64 (128*k))+BitVec.ofNat 64 (1024*poly.val+16*j.val)) 16=
    m.read ((base+BitVec.ofNat 64 (128*k))+BitVec.ofNat 64 (1024*poly.val+16*j.val)) 16 := by
  rw [writePair_values]
  apply storeValues_read_other
  intro i _
  simp only [BitVec.add_assoc,←BitVec.ofNat_add]
  exact Offset.sep base (by omega) (by omega) (by omega)

/-- Every completed local slice contains the original-input product followed by
exactly the first five inverse layers, independent of later scratch writes. -/
theorem firstPass_read_written {m : Mem} {p a b : Addr} {n u : Nat}
    (hn : n≤8) (hu : u<n)
    (ha : (⟨a,1024⟩ : Region).Disjoint ⟨p,2048⟩)
    (hb : (⟨b,2048⟩ : Region).Disjoint ⟨p,2048⟩) (poly : Fin 2) (j : Fin 8) :
    (firstPassMem m p a b n).read
      ((p+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (1024*poly.val+16*j.val)) 16=
    (Inverse.fiveValues u (valuesAt m (a+BitVec.ofNat 64 (128*u))
      (b+BitVec.ofNat 64 (128*u)) poly))[j.val] := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : u=n
    · subst u
      rw [firstPassMem,writePair_read16,firstPass_valuesAt (by omega) ha hb]
    · rw [firstPassMem,writePair_slice_other _ _ _ (by omega) (by omega) he]
      exact ih (by omega) (by omega)
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedFinalSource.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- The final strided bank is the transpose of the eight completed local slices. -/
theorem firstPass_finalBank {m : Mem} {p a b : Addr} {u : Nat} (hu : u<8)
    (ha : (⟨a,1024⟩ : Region).Disjoint ⟨p,2048⟩)
    (hb : (⟨b,2048⟩ : Region).Disjoint ⟨p,2048⟩) (poly : Fin 2) :
    readPair (firstPassMem m p a b 8) (p+BitVec.ofNat 64 (16*u)) 128 poly=
      Vector.ofFn (fun j : Fin 8 =>
        (Inverse.fiveValues j.val (valuesAt m (a+BitVec.ofNat 64 (128*j.val))
          (b+BitVec.ofNat 64 (128*j.val)) poly))[u]) := by
  apply Vector.ext
  intro j hj
  simp only [readPair,Vector.getElem_ofFn]
  have had : (p+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*poly.val+128*j)=
      (p+BitVec.ofNat 64 (128*j))+BitVec.ofNat 64 (1024*poly.val+16*u) := by
    simp only [BitVec.add_assoc,←BitVec.ofNat_add]
    rw [show 16*u+(1024*poly.val+128*j)=128*j+(1024*poly.val+16*u) by omega]
  rw [had]
  exact firstPass_read_written (by decide) hj ha hb poly ⟨u,hu⟩

/-- Final-pass output stores outside work preserve every strided inverse bank. -/
theorem readPair_workFrame {m m' : Mem} {p : Addr} {u : Nat} {W : List Region}
    (hu : u<8) (hf : Frame W m m')
    (hd : ∀r∈W,(⟨p,2048⟩ : Region).Disjoint r) :
    readPair m' (p+BitVec.ofNat 64 (16*u)) 128=readPair m (p+BitVec.ofNat 64 (16*u)) 128 := by
  funext poly
  apply Vector.ext
  intro j hj
  simp only [readPair,Vector.getElem_ofFn,BitVec.add_assoc,←BitVec.ofNat_add]
  exact hf.read (Offset.contains_base p (by omega : 16*u+(1024*poly.val+128*j)+16≤2048) (by omega)) hd (by decide)
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedProductField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

theorem valuesAt_word (m : Mem) (a b : Addr) (poly : Fin 2) (j : Fin 8) {e : Nat} (he : e<4) :
    vword ((valuesAt m a b poly)[j.val]) e=centeredProduct
      (vword (m.read (a+BitVec.ofNat 64 (16*j.val)) 16) e)
      (vword (m.read (b+BitVec.ofNat 64 (1024*poly.val+16*j.val)) 16) e) := by
  simp only [valuesAt,Vector.getElem_ofFn]
  rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl <;> simp only [vword_ofVWords_0,vword_ofVWords_1,vword_ofVWords_2,vword_ofVWords_3]

/-- The paired SIMD layout contains the same pointwise products as the scalar polynomial view. -/
theorem valuesAt_coeff (m : Mem) (a b : Addr) (u : Nat) (poly : Fin 2) (j : Fin 8)
    {e : Nat} (he : e<4) :
    vword ((valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly)[j.val]) e=
      centeredProduct (coeffAt m a (32*u+4*j.val+e))
        (coeffAt m (b+BitVec.ofNat 64 (1024*poly.val)) (32*u+4*j.val+e)) := by
  rw [valuesAt_word _ _ _ _ _ he,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he]
  simp only [coeffAt,BitVec.add_assoc,←BitVec.ofNat_add]
  rw [show 128*u+16*j.val+4*e=4*(32*u+4*j.val+e) by omega,
    show 128*u+(1024*poly.val+16*j.val)+4*e=1024*poly.val+4*(32*u+4*j.val+e) by omega]

theorem valuesAt_bounds {m : Mem} {a b : Addr} {u : Nat} {poly : Fin 2} {f g : Poly}
    (hu : u<8) (hf : PosPolyIs m a f) (hg : PosPolyIs m (b+BitVec.ofNat 64 (1024*poly.val)) g)
    (j : Fin 8) {e : Nat} (he : e<4) :
    -(q : Int)≤(vword ((valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly)[j.val]) e).toInt ∧
    (vword ((valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly)[j.val]) e).toInt≤147168 := by
  rw [valuesAt_coeff _ _ _ _ _ _ he]
  exact centeredProduct_bounds _ _ (hf.bound _ (by change 32*u+4*j.val+e<256; omega))
    (hg.bound _ (by change 32*u+4*j.val+e<256; omega))

theorem valuesAt_scaled {m : Mem} {a b : Addr} {u : Nat} {poly : Fin 2} {f g : Poly}
    (hu : u<8) (hf : PosPolyIs m a f) (hg : PosPolyIs m (b+BitVec.ofNat 64 (1024*poly.val)) g)
    (j : Fin 8) {e : Nat} (he : e<4) :
    ofInt (vword ((valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly)[j.val]) e).toInt * ofInt 4294967296=
      f[32*u+4*j.val+e]! * g[32*u+4*j.val+e]! := by
  have hi : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega
  rw [valuesAt_coeff _ _ _ _ _ _ he,
    centeredProduct_scaled _ _ (hf.bound _ hi) (hg.bound _ hi),
    ofInt_nat_eq,ofInt_nat_eq,←polyAt_get _ _ hi,←polyAt_get _ _ hi,hf.value,hg.value]
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
