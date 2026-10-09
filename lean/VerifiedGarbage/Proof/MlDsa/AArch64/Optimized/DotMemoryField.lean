import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemoryValues
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemoryCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FusedRepresentation
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotCore

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem dotMemoryBank_bound {m : Mem} {a b : Addr} {f g : Nat → Poly} {u count : Nat}
    (hu : u<8) (hc : count≤7)
    (hf : ∀k<count,PosPolyIs m (a+BitVec.ofNat 64 (1024*k)) (f k))
    (hg : ∀k<count,PosPolyIs m (b+BitVec.ofNat 64 (1024*k)) (g k)) :
    BankBound (dotMemoryBank m (a+BitVec.ofNat 64 (128*u))
      (b+BitVec.ofNat 64 (128*u)) count) 8380417 := by
  intro j e he
  rw [dotMemoryBank_word _ _ _ _ j he,dotMemoryWord_offset _ _ _ _ _ _ _ he]
  have hk : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega
  have hbnd := centeredDot_bound _ _ hc
    (fun k hkc => (hf k hkc).bound _ hk) (fun k hkc => (hg k hkc).bound _ hk)
  exact ⟨hbnd.1,Int.le_of_lt hbnd.2⟩

theorem dotMemoryBank_field {m : Mem} {a b : Addr} {f g : Nat → Poly} {u count : Nat}
    (hu : u<8) (hc : count≤7)
    (hf : ∀k<count,PosPolyIs m (a+BitVec.ofNat 64 (1024*k)) (f k))
    (hg : ∀k<count,PosPolyIs m (b+BitVec.ofNat 64 (1024*k)) (g k)) :
    InnerBankField u (dotMemoryBank m (a+BitVec.ofNat 64 (128*u))
      (b+BitVec.ofNat 64 (128*u)) count) (Representation.encode true (dotPoly f g count)) := by
  intro j e he
  rw [dotMemoryBank_word _ _ _ _ j he,dotMemoryWord_offset _ _ _ _ _ _ _ he]
  have hk : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega
  refine centeredDot_field _ _ f g hc (fun k hkc => (hf k hkc).bound _ hk)
    (fun k hkc => (hg k hkc).bound _ hk) hk ?_ ?_
  · intro k hkc; rw [ofInt_nat_eq,← polyAt_get _ _ hk,(hf k hkc).value]; rfl
  · intro k hkc; rw [ofInt_nat_eq,← polyAt_get _ _ hk,(hg k hkc).value]; rfl

theorem dotPass_field {m : Mem} {p a b : Addr} {f g : Nat → Poly} {count : Nat}
    (hc : count≤7)
    (hf : ∀k<count,PosPolyIs m (a+BitVec.ofNat 64 (1024*k)) (f k))
    (hg : ∀k<count,PosPolyIs m (b+BitVec.ofNat 64 (1024*k)) (g k))
    (ha : ∀k<count,(polyRegion (a+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p))
    (hb : ∀k<count,(polyRegion (b+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p)) :
    SignedPolyIs (dotPassMem m p a b count 8) p
      (InverseTraversal.run InverseTraversal.localSchedule (Representation.encode true (dotPoly f g count)))
      (-268173344) 268173344 := by
  have bank (u : Nat) (hu : u<8) := fiveValues_field _ _ hu
    (dotMemoryBank_bound hu hc hf hg) (dotMemoryBank_field hu hc hf hg)
  have hout (k : Nat) (hk : k<n) :
      -268173344≤(coeffAt (dotPassMem m p a b count 8) p k).toInt ∧
      (coeffAt (dotPassMem m p a b count 8) p k).toInt≤268173344 ∧
      ofInt (coeffAt (dotPassMem m p a b count 8) p k).toInt=
        (InverseTraversal.run InverseTraversal.localSchedule (Representation.encode true (dotPoly f g count)))[k]! := by
    have hu : k/32<8 := by change k<256 at hk; omega
    have hi : (k%32)/4<8 := by omega
    have he : k%4<4 := by omega
    rw [dotPass_processed ha hb (by decide) hk hu,
      getElem!_pos (fiveValues (k/32) (dotMemoryBank m (a+BitVec.ofNat 64 (128*(k/32)))
        (b+BitVec.ofNat 64 (128*(k/32))) count)) ((k%32)/4) hi]
    have hbank := bank (k/32) hu
    refine ⟨(hbank.1 ⟨(k%32)/4,hi⟩ _ he).1,(hbank.1 ⟨(k%32)/4,hi⟩ _ he).2,?_⟩
    have hv := hbank.2 ⟨(k%32)/4,hi⟩ _ he
    have hidx : 32*(k/32)+4*((k%32)/4)+k%4=k := by omega
    simp only [Traversal.innerLoc] at hv
    rw [hidx] at hv
    have hcoord := InverseTraversal.prefix_selected InverseTraversal.localSlice (fun k => k/32) 8
      (fun u hu => InverseTraversal.local_supported ⟨u,hu⟩)
      (Representation.encode true (dotPoly f g count)) hk hu
    exact hv.trans hcoord.symm
  exact ⟨fun k hk => ⟨(hout k hk).1,(hout k hk).2.1⟩,fun k hk => (hout k hk).2.2⟩

theorem dotInverseMem_field {m : Mem} {p a b : Addr} {f g : Nat → Poly} {count : Nat}
    (hc : count≤7)
    (hf : ∀k<count,PosPolyIs m (a+BitVec.ofNat 64 (1024*k)) (f k))
    (hg : ∀k<count,PosPolyIs m (b+BitVec.ofNat 64 (1024*k)) (g k))
    (ha : ∀k<count,(polyRegion (a+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p))
    (hb : ∀k<count,(polyRegion (b+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p)) :
    PolyIs (dotInverseMem m p a b count) p (nttInv (dotNTT f g count)) := by
  have hp := finalPass_field (dotPass_field hc hf hg ha hb) (qv:=HighPack.repeatedWord 8380417)
    (fun e he => HighPack.repeatedWord_lane _ he)
  simpa only [dotInverseMem,InverseTraversal.traversal_montgomery,inverse_dotNTT] using hp

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
