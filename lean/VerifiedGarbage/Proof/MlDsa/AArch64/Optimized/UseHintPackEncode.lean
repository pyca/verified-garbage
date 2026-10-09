import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackEncode

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open HighPack

/-- The vector packing tail depends only on the bounded fields supplied in
its lanes, so it also applies after UseHint. -/
theorem packedVector_fields {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (L : Vector Nat 256) (hbound : ∀i (hi : i<256),L[i]'hi<2^packWidth g)
    {s : State} (hc : PackConstants s) {block i : Nat}
    (hb : block<16) (hi : i<2*packWidth g)
    (hv : ∀j (hj : j<4),∀e (he : e<4),(vword (s.v ([.v0,.v1,.v2,.v3] : List VReg)[j]!) e).toNat=
      L[16*block+4*j+e]'(by omega)) :
    vbyte (packedVector (packWidth g) s) i=
      (simpleBitPack L ((q-1)/(2*g)-1))[2*packWidth g*block+i]! := by
  have gathered : ∀j<16,vbyte (HighPack.gathered s) j=
      BitVec.ofNat 8 (L.toList.getD (16*block+j) 0) := by
    intro j hj
    rw [gathered_word s hj]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth,BitVec.toNat_ofNat,hv (j/4) (by omega) (j%4) (by omega)]
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simp; omega),Option.getD_some]
    simp only [Vector.getElem_toList]
    congr 2
    omega
  have hlen : L.toList.length=256 := by simp
  have bounds : ∀a∈L.toList,a<2^packWidth g := by
    intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp ha
    exact hbound j (by simpa using hj)
  have hw : bitlen ((q-1)/(2*g)-1)=packWidth g := by rcases hg with rfl|rfl <;> rfl
  rw [simpleBitPack_eq,hw]
  rcases hg with rfl|rfl
  · exact encode4_byte hlen bounds hb hi gathered
  · exact encode6_byte hlen bounds hb hi hc gathered

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
