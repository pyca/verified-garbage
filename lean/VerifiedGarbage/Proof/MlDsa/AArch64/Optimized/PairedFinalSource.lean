import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstRead
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalLoad

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
