import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowWriteValues

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def lowAddr (base : Addr) (i : LowIndex) (half : Fin 2) : Addr :=
  base+BitVec.ofNat 64 (lowOff i+128*half.val)

theorem lowAddr_sep (base : Addr) {i j : LowIndex} {h k : Fin 2}
    (hne : i≠j ∨ h≠k) : Mem.Sep (lowAddr base i h) 16 (lowAddr base j k) 16 := by
  have hi : i.1.val≠j.1.val ∨ i.2.val≠j.2.val ∨ h.val≠k.val := by
    by_contra hn
    simp only [not_or,not_not] at hn
    have he : i=j := Prod.ext (Fin.ext hn.1) (Fin.ext hn.2.1)
    have hh : h=k := Fin.ext hn.2.2
    rcases hne with hn | hn
    · exact hn he
    · exact hn hh
  simp only [lowAddr,lowOff]
  exact Offset.sep base (by omega) (by omega) (by omega)

theorem lowAddr_contains (base : Addr) {u : Nat} (hu : u<8) (i : LowIndex) (h : Fin 2) :
    (⟨base,2048⟩ : Region).Contains (lowAddr (base+BitVec.ofNat 64 (16*u)) i h) 16 := by
  simp only [lowAddr,lowOff,BitVec.add_assoc,←BitVec.ofNat_add]
  exact Offset.contains_base base (by omega) (by omega)

/-- Disjoint later paired checks preserve either half of either output. -/
theorem lowRun_read_slot_other (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (i : LowIndex) (h : Fin 2)
    (hn : i∉is) (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowRun g v out aux c d is).mem.read (lowAddr out i h) 16=d.mem.read (lowAddr out i h) 16 := by
  apply lowRun_read_other
  intro j hj
  have hnij : i≠j := by intro he; subst j; exact hn hj
  have ho0 := lowAddr_sep (h:=h) (k:=0) out (Or.inl hnij)
  have ho1 := lowAddr_sep (h:=h) (k:=1) out (Or.inl hnij)
  have contain (base : Addr) (i : LowIndex) (h : Fin 2) :
      (⟨base,2048⟩ : Region).Contains (lowAddr base i h) 16 := by
    simp only [lowAddr,lowOff]
    exact Offset.contains_base base (by omega) (by omega)
  have ha0 := hd.sep (contain out i h) (contain aux j 0)
  have ha1 := hd.sep (contain out i h) (contain aux j 1)
  simpa only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using
    And.intro ho0 (And.intro ho1 (And.intro ha0 ha1))

end VG.Proof.MlDsa.AArch64.Optimized.Paired
