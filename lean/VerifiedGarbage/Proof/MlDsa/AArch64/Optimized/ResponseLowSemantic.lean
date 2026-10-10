import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

/-! ## From `ResponseLowStore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Spec.MlDsa (coeffAt)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

theorem lowStep_frame (g B : Nat) (p a l : Addr) {j : Nat} (hj : j<64) (d : LowData) :
    Frame [polyRegion p,polyRegion l] d.mem (lowStep g B p a l j d).mem := by
  have hp : (polyRegion p).Contains (p+BitVec.ofNat 64 (16*j)) 16 :=
    Offset.contains_base p (by omega) (by omega)
  have hl : (polyRegion l).Contains (l+BitVec.ofNat 64 (16*j)) 16 :=
    Offset.contains_base l (by omega) (by omega)
  exact ((Frame.refl _ _).write (by simp) _ hp).write (by simp) _ hl

theorem coeffAt_write16_other {m : Mem} {p l : Addr} {j i : Nat} (hj : j<64) (hi : i<256)
    (hd : (polyRegion p).Disjoint (polyRegion l)) (v : BitVec 128) :
    coeffAt (m.write (l+BitVec.ofNat 64 (16*j)) 16 v) p i=coeffAt m p i := by
  have hl : (polyRegion l).Contains (l+BitVec.ofNat 64 (16*j)) 16 :=
    Offset.contains_base l (by omega) (by omega)
  have hf : Frame [polyRegion l] m (m.write (l+BitVec.ofNat 64 (16*j)) 16 v) :=
    (Frame.refl _ _).write (by simp) _ hl
  exact coeffAt_frame hf (by intro r hr; simpa using (List.mem_singleton.mp hr ▸ hd)) hi

theorem lowStep_high {g B : Nat} {p a l : Addr} {j i : Nat} (hj : j<64) (hi : i<256)
    (hd : (polyRegion p).Disjoint (polyRegion l)) (d : LowData) :
    coeffAt (lowStep g B p a l j d).mem p i=
      if 4*j≤i ∧ i<4*j+4 then HighPack.highWord g (lowInput d.mem p a j (i-4*j))
      else coeffAt d.mem p i := by
  dsimp only [lowStep]
  rw [coeffAt_write16_other hj hi hd]
  have ha : p+BitVec.ofNat 64 (16*j)=coeffAddr p (4*j) := by congr 2; omega
  rw [ha,coeffAt_write16 _ _ (by omega) _ hi]
  split
  · rename_i h; rw [laneVector_word _ (by omega)]
  · rfl

theorem lowStep_low {g B : Nat} {p a l : Addr} {j i : Nat} (hj : j<64) (hi : i<256)
    (hd : (polyRegion p).Disjoint (polyRegion l)) (d : LowData) :
    coeffAt (lowStep g B p a l j d).mem l i=
      if 4*j≤i ∧ i<4*j+4 then lowOutput g d.mem p a j (i-4*j)
      else coeffAt d.mem l i := by
  dsimp only [lowStep]
  have ha : l+BitVec.ofNat 64 (16*j)=coeffAddr l (4*j) := by congr 2; omega
  rw [ha,coeffAt_write16 _ _ (by omega) _ hi]
  split
  · rename_i h; rw [laneVector_word _ (by omega)]
  · exact coeffAt_write16_other hj hi hd.symm _

theorem lowRun_frame (m : Mem) (g B : Nat) (p a l : Addr) {j : Nat} (hj : j≤64) :
    Frame [polyRegion p,polyRegion l] m (lowRun m g B p a l j).mem := by
  induction j with
  | zero => exact Frame.refl _ _
  | succ j ih => exact (ih (by omega)).trans (lowStep_frame g B p a l (by omega) _)

theorem lowRun_input {m : Mem} {g B : Nat} {p a l : Addr} {j i : Nat} (hj : j≤64) (hi : i<256)
    (hap : (polyRegion a).Disjoint (polyRegion p)) (hal : (polyRegion a).Disjoint (polyRegion l)) :
    coeffAt (lowRun m g B p a l j).mem a i=coeffAt m a i := by
  apply coeffAt_frame (lowRun_frame m g B p a l hj) _ hi
  intro r hr
  rcases (show r=polyRegion p ∨ r=polyRegion l by simpa using hr) with rfl|rfl
  · exact hap
  · exact hal

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseLowSemantic.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Spec.MlDsa (coeffAt)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

def lowCanonical (m : Mem) (p a : Addr) (i : Nat) : BitVec 32 :=
  Inverse.signCorrected (reduceWord (coeffAt m p i-coeffAt m a i))
def lowHigh (m : Mem) (g : Nat) (p a : Addr) (i : Nat) : BitVec 32 :=
  HighPack.highWord g (lowCanonical m p a i)
def lowSigned (m : Mem) (g : Nat) (p a : Addr) (i : Nat) : BitVec 32 :=
  lowWord (lowCanonical m p a i) (lowHigh m g p a i) (BitVec.ofNat 32 (2*g))

theorem lowInput_coeff (m : Mem) (p a : Addr) (j : Nat) {e : Nat} (he : e<4) :
    lowInput m p a j e=lowCanonical m p a (4*j+e) := by
  unfold lowInput lowCanonical
  rw [show 16*j=4*(4*j) by omega]
  change Inverse.signCorrected (reduceWord (vword (m.read (coeffAddr p (4*j)) 16) e-
    vword (m.read (coeffAddr a (4*j)) 16) e))=_
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,coeffAddr_add,coeffAddr_add]
  rfl

theorem lowOutput_coeff (m : Mem) (g : Nat) (p a : Addr) (j : Nat) {e : Nat} (he : e<4) :
    lowOutput g m p a j e=lowSigned m g p a (4*j+e) := by
  simp only [lowOutput,lowInput_coeff _ _ _ _ he,lowSigned,lowHigh]

def LowPrefix (initial current : Mem) (g : Nat) (p a l : Addr) (done : Nat) : Prop :=
  (∀i<256,coeffAt current p i=if i<done then lowHigh initial g p a i else coeffAt initial p i) ∧
  (∀i<256,coeffAt current l i=if i<done then lowSigned initial g p a i else coeffAt initial l i)

theorem lowRun_prefix (m : Mem) (g B : Nat) (p a l : Addr)
    (hpl : (polyRegion p).Disjoint (polyRegion l))
    (hap : (polyRegion a).Disjoint (polyRegion p)) (hal : (polyRegion a).Disjoint (polyRegion l))
    {j : Nat} (hj : j≤64) : LowPrefix m (lowRun m g B p a l j).mem g p a l (4*j) := by
  induction j with
  | zero => constructor <;> intro i hi <;> simp [lowRun]
  | succ j ih =>
    have hp := ih (by omega)
    have ha := fun (i : Nat) (hi : i<256) => lowRun_input (m:=m) (g:=g) (B:=B) (j:=j) (i:=i) (by omega) hi hap hal
    have hh (i : Nat) (hi : i<256) (hn : ¬i<4*j) :
        lowCanonical (lowRun m g B p a l j).mem p a i=lowCanonical m p a i := by
      simp only [lowCanonical,hp.1 i hi,ite_eq_right hn,ha i hi]
    constructor
    · intro i hi
      rw [lowRun,lowStep_high (by omega) hi hpl]
      by_cases before : i<4*j
      · rw [ite_eq_right (by omega),hp.1 i hi,ite_eq_left before,ite_eq_left (by omega)]
      · by_cases inside : i<4*j+4
        · rw [ite_eq_left (by omega),lowInput_coeff _ _ _ _ (by omega),
            show 4*j+(i-4*j)=i by omega,hh i hi before,ite_eq_left (by omega)]
          rfl
        · rw [ite_eq_right (by omega),hp.1 i hi,ite_eq_right before,ite_eq_right (by omega)]
    · intro i hi
      rw [lowRun,lowStep_low (by omega) hi hpl]
      by_cases before : i<4*j
      · rw [ite_eq_right (by omega),hp.2 i hi,ite_eq_left before,ite_eq_left (by omega)]
      · by_cases inside : i<4*j+4
        · rw [ite_eq_left (by omega),lowOutput_coeff _ _ _ _ _ (by omega),
            show 4*j+(i-4*j)=i by omega,ite_eq_left (by omega)]
          simp only [lowSigned,lowHigh,hh i hi before]
        · rw [ite_eq_right (by omega),hp.2 i hi,ite_eq_right before,ite_eq_right (by omega)]

theorem lowRun_coeff (m : Mem) (g B : Nat) (p a l : Addr)
    (hpl : (polyRegion p).Disjoint (polyRegion l))
    (hap : (polyRegion a).Disjoint (polyRegion p)) (hal : (polyRegion a).Disjoint (polyRegion l))
    {i : Nat} (hi : i<256) :
    coeffAt (lowRun m g B p a l 64).mem p i=lowHigh m g p a i ∧
    coeffAt (lowRun m g B p a l 64).mem l i=lowSigned m g p a i := by
  have h := lowRun_prefix m g B p a l hpl hap hal (by decide : 64≤64)
  exact ⟨by rw [h.1 i hi,ite_eq_left hi],by rw [h.2 i hi,ite_eq_left hi]⟩

end VG.Proof.MlDsa.AArch64.Optimized.Response

end
