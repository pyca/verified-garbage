import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseLocalTable

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64

def packedRoot (u g len e : Nat) : Int := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z
  (if len=1 then 255-16*u-4*g-e else 127-8*u-2*g-e/2)

theorem packedRoot_range (u g len e : Nat) : 0≤packedRoot u g len e ∧ packedRoot u g len e<8380417 := by
  unfold packedRoot VG.Impl.MlDsa.AArch64.Optimized.Inverse.z
  exact ⟨Int.natCast_nonneg _,Int.ofNat_lt.mpr (Nat.mod_lt _ (by decide))⟩

theorem packed_words {m : Mem} {p : Addr} (h : InverseTable.Words m p)
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
    (h : InverseTable.Words s.mem p)
    (hr : ∀ off, off+16≤3904 → InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 off) 16)
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

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
