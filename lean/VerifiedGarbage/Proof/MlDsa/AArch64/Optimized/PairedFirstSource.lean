import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstMemory

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
