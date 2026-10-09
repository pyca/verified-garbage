import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableDecode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPackedRoot
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedTable

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Inverse

theorem local_words {m : Mem} {p : Addr} (h : PairedTable.Words m p)
    {u : Nat} (hu : u<8) (i : Fin 7) {e : Nat} (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+localOffset i.val)) 16) e=BitVec.ofInt 32 (localRoot u i.val e) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+localOffset i.val+16)) 16) e=
      BitVec.ofInt 32 (reciprocal (localRoot u i.val e)) := by
  by_cases hi : i.val<4
  · simp only [localOffset,localRoot,localIndex,hi,ite_true,← Nat.add_assoc]
    exact nat_row (n := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (63-4*u-i.val)) (h.layer4 (u := u) (g := i.val) (e := e) hu hi he)
  · by_cases hj : i.val<6
    · simp only [localOffset,localRoot,localIndex,hi,hj,ite_false,ite_true,← Nat.add_assoc]
      exact nat_row (n := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (31-2*u-(i.val-4))) (h.layer8 (u := u) (g := i.val-4) (e := e) hu (by omega) he)
    · simp only [localOffset,localRoot,localIndex,hi,hj,ite_false]
      exact nat_row (n := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (15-u)) (h.layer16 (u := u) (e := e) hu he)


theorem packed_words {m : Mem} {p : Addr} (h : PairedTable.Words m p)
    {u g len e : Nat} (hu : u<8) (hg : g<4) (hl : len=1 ∨ len=2) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+packedOffset g len)) 16) e=BitVec.ofInt 32 (packedRoot u g len e) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+packedOffset g len+16)) 16) e=
      BitVec.ofInt 32 (reciprocal (packedRoot u g len e)) := by
  rcases hl with rfl | rfl
  · simp only [packedRoot,packedOffset,ite_true,← Nat.add_assoc]
    exact nat_row (n := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (255-16*u-4*g-e))
      (h.layer1 (u := u) (g := g) (e := e) hu hg he)
  · simp only [packedRoot,packedOffset,show ¬(2=1) by decide,ite_false,← Nat.add_assoc]
    exact nat_row (n := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (127-8*u-2*g-e/2))
      (h.layer2 (u := u) (g := g) (e := e) hu hg he)

theorem packed_tableRoots {s : State} {p : Addr} {u : Nat} (hu : u<8)
    (h : PairedTable.Words s.mem p)
    (hr : ∀ off, off+16≤4096 → InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 off) 16)
    (hx : s.gpr .x1=p+BitVec.ofNat 64 (480*u))
    (hq : ∀ e<4, vword (s.v .v31) e=8380417#32) : PackedRoots s (packedRoot u) := by
  refine ⟨hq,fun g _ len _ e _ => packedRoot_range u g len e,?_,?_,?_⟩
  · intro g hg len hl b hb
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    have ho : packedOffset g len≤224 := by
      rcases hl with rfl | rfl <;> simp [packedOffset] <;> omega
    exact hr _ (by rcases hb with rfl | rfl <;> omega)
  · intro g hg len hl e he
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    exact (packed_words h hu hg hl he).1
  · intro g hg len hl e he
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    simpa only [Nat.add_assoc] using (packed_words h hu hg hl he).2

theorem local_tableReady {s : State} {p : Addr} {u : Nat} (hu : u<8)
    (h : PairedTable.Words s.mem p)
    (hr : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 off) 16)
    (hx : s.gpr .x1=p+BitVec.ofNat 64 (480*u)) (i : Fin 7) :
    RootReady s (localOffset i.val) (localRoot u i.val) := by
  have hb := localOffset_bound i
  refine ⟨hb.2,by omega,?_,?_,fun e _ => localRoot_range u i e,?_,?_⟩
  · rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    exact hr _ (by omega)
  · rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    exact hr _ (by omega)
  · intro e he
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    exact (local_words h hu i he).1
  · intro e he
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    simpa only [Nat.add_assoc] using (local_words h hu i he).2

end VG.Proof.MlDsa.AArch64.Optimized.Paired
