import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseLocalRoots

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64

def localOffset (i : Nat) : Nat := if i<4 then 256+32*i else if i<6 then 384+32*(i-4) else 448

def localIndex (u i : Nat) : Nat := if i<4 then 63-4*u-i else if i<6 then 31-2*u-(i-4) else 15-u

def localRoot (u i : Nat) (_e : Nat) : Int := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (localIndex u i)

theorem reciprocal_nat (n : Nat) :
    BitVec.ofNat 32 (VG.Impl.MlDsa.AArch64.Optimized.Inverse.bar n)=BitVec.ofInt 32 (reciprocal (n : Int)) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.Inverse.bar
  rw [← BitVec.ofInt_natCast, Int.natCast_ediv, Int.natCast_mul]
  rfl

theorem localRoot_range (u : Nat) (i : Fin 7) (e : Nat) :
    0≤localRoot u i.val e ∧ localRoot u i.val e<8380417 := by
  have h := Nat.mod_lt (8380417-1753^VG.Spec.MlDsa.bitRev8 (localIndex u i.val)%8380417) (by decide : 0<8380417)
  change 0≤(VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (localIndex u i.val) : Int) ∧ _
  exact ⟨Int.natCast_nonneg _,Int.ofNat_lt.mpr h⟩

theorem nat_row {a b : BitVec 32} {n : Nat}
    (h : a=BitVec.ofNat 32 n ∧ b=BitVec.ofNat 32 (VG.Impl.MlDsa.AArch64.Optimized.Inverse.bar n)) :
    a=BitVec.ofInt 32 (n : Int) ∧ b=BitVec.ofInt 32 (reciprocal (n : Int)) := by
  exact ⟨h.1.trans (BitVec.ofInt_natCast ..).symm,h.2.trans (reciprocal_nat n)⟩

theorem local_words {m : Mem} {p : Addr} (h : InverseTable.Words m p)
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


theorem localOffset_bound (i : Fin 7) : localOffset i.val≤448 ∧ localOffset i.val%16=0 := by
  exact (show ∀ i : Fin 7, localOffset i.val≤448 ∧ localOffset i.val%16=0 by decide +kernel) i

theorem local_tableRoots {s : State} {p : Addr} {u : Nat} (hu : u<8)
    (h : InverseTable.Words s.mem p)
    (hr : ∀ off, off+16≤3904 → InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 off) 16)
    (hx : s.gpr .x1=p+BitVec.ofNat 64 (480*u))
    (hq : ∀ e<4, vword (s.v .v31) e=8380417#32) :
    TableRoots localOffset (localRoot u) s := by
  refine ⟨hq,?_,?_,?_⟩
  · intro i b hb
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    have ho := (localOffset_bound i).1
    exact hr _ (by rcases hb with rfl | rfl <;> omega)
  · intro i e he
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    exact (local_words h hu i he).1
  · intro i e he
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    simpa only [Nat.add_assoc] using (local_words h hu i he).2

def localPlan (u : Nat) : RootPlan :=
  tablePlan localOffset (localRoot u)
    (fun i => (localOffset_bound i).2)
    (fun i => by have := (localOffset_bound i).1; omega)
    (fun i e _ => localRoot_range u i e)

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
