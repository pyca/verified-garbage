import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackBlock
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.MlDsa.Pack.Mem

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

/-- Gathering keeps the low byte of each 32-bit coefficient. -/
theorem lowWordByte (x : BitVec 128) (j : Nat) :
    vbyte x (4*j)=(vword x j).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vbyte,vword,BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,
    hb,show b<32 by omega,decide_true,Bool.true_and]
  congr 1
  omega

/-- The gather permutation preserves the original coefficient ordering. -/
theorem gathered_word (s : State) {i : Nat} (hi : i<16) :
    vbyte (gathered s) i =
      (vword (s.v ([.v0,.v1,.v2,.v3] : List VReg)[i/4]!) (i%4)).setWidth 8 := by
  unfold gathered
  rw [gatherSixteen_byte _ _ _ _ hi]
  rcases (by omega : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceLT,ite_true,ite_false,Nat.reduceSub,Nat.reduceDiv,Nat.reduceMod,
      List.getElem!_cons_zero,List.getElem!_cons_succ] <;> exact lowWordByte _ _

/-- Once the arithmetic kernel supplies exact lanes, the byte gather exposes
those same high bits, without a second representation assumption. -/
theorem gathered_highWord {g : Nat} {s : State} {m : Mem} {a : Addr}
    (h : ∀ j<4, ∀ e<4,
      vword (s.v ([.v0,.v1,.v2,.v3] : List VReg)[j]!) e=
        highWord g (vword (m.read (a+BitVec.ofNat 64 (16*j)) 16) e))
    {i : Nat} (hi : i<16) :
    vbyte (gathered s) i =
      (highWord g (m.readW (a+BitVec.ofNat 64 (4*i)) 32)).setWidth 8 := by
  rw [gathered_word s hi,h (i/4) (by omega) (i%4) (by omega),
    VG.AArch64.vword_read16 _ _ (by omega),Offset.add_add]
  rw [show 16*(i/4)+4*(i%4)=4*i by omega]


/-- A canonical input word computes exactly the corresponding FIPS HighBits
coefficient, including the zero-at-modulus correction. -/
theorem highWord_coefficient {g : Nat} (hg : IsG g) {m : Mem} {a : Addr}
    (hr : Reduced m a) {i : Nat} (hi : i<n) :
    (highWord g (coeffAt m a i)).toNat=(highCoefficients g (polyAt m a))[i] := by
  rw [highWord_spec hg (hr i hi)]
  simp only [highCoefficients,Vector.getElem_map]
  have hv : (⟨(coeffAt m a i).toNat,hr i hi⟩ : Zq)=(polyAt m a)[i] :=
    Fin.ext (VG.Proof.MlDsa.Pack.polyAt_val hr hi).symm
  rw [hv]


/-- At any of the sixteen block offsets, the gather bytes are the original
polynomial's HighBits coefficients in order. -/
theorem gathered_coefficients {g : Nat} (hg : IsG g) {s : State} {m : Mem} {a : Addr}
    (hr : Reduced m a) {block : Nat} (hb : block<16)
    (h : ∀ j<4, ∀ e<4,
      vword (s.v ([.v0,.v1,.v2,.v3] : List VReg)[j]!) e=
        highWord g (vword (m.read ((a+BitVec.ofNat 64 (64*block))+BitVec.ofNat 64 (16*j)) 16) e))
    {i : Nat} (hi : i<16) :
    vbyte (gathered s) i = BitVec.ofNat 8
      ((highCoefficients g (polyAt m a))[16*block+i]'(by change 16*block+i<256; omega)) := by
  rw [gathered_highWord h hi,Offset.add_add,
    show 64*block+4*i=4*(16*block+i) by omega]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  change (highWord g (coeffAt m a (16*block+i))).toNat%2^8 = _
  rw [highWord_coefficient hg hr (by change 16*block+i<256; omega)]

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
