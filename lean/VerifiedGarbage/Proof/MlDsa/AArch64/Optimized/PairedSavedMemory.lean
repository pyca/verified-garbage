import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedExtra
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired

private theorem read_write_self (m : Mem) (a : Addr) (v : BitVec 128) :
    (m.write a 16 v).read a 16 = v := by
  simpa only [Mem.writeW,Mem.readW,BitVec.setWidth_eq] using
    Mem.readW_writeW_self m a 16 v (by decide)

theorem writeSlice_read_other (xs : List (VReg × Nat)) (base a : Addr)
    (v : VReg → BitVec 128) (m : Mem)
    (hs : ∀ p∈xs,Mem.Sep a 16 (base+BitVec.ofNat 64 p.2) 16) :
    (writeSlice xs base v m).read a 16=m.read a 16 := by
  induction xs generalizing m with
  | nil => rfl
  | cons p xs ih =>
    change (writeSlice xs base v (m.write (base+BitVec.ofNat 64 p.2) 16 (v p.1))).read a 16=_
    rw [ih _ (fun q hq => hs q (List.mem_cons_of_mem _ hq)),
      Mem.read_write_sep (hs p (by simp)) (by decide)]

theorem writeSlice_read_slot (xs : List (VReg × Nat)) (base : Addr)
    (v : VReg → BitVec 128) (m : Mem) (p : VReg × Nat) (hp : p∈xs)
    (hs : ∀ q∈xs,q≠p → Mem.Sep (base+BitVec.ofNat 64 p.2) 16
      (base+BitVec.ofNat 64 q.2) 16) :
    (writeSlice xs base v m).read (base+BitVec.ofNat 64 p.2) 16=v p.1 := by
  induction xs generalizing m with
  | nil => simp at hp
  | cons q xs ih =>
    change (writeSlice xs base v (m.write (base+BitVec.ofNat 64 q.2) 16 (v q.1))).read _ 16=_
    by_cases ht : p∈xs
    · exact ih _ ht (fun r hr => hs r (List.mem_cons_of_mem _ hr))
    · have he : p=q := (List.mem_cons.mp hp).resolve_right ht
      subst q
      rw [writeSlice_read_other _ _ _ _ _ (fun r hr => hs r (List.mem_cons_of_mem _ hr)
        (by intro h; subst r; exact ht hr)),read_write_self]

theorem writeSlice_frame (xs : List (VReg × Nat)) (base : Addr)
    (v : VReg → BitVec 128) (m : Mem) (r : Region)
    (hc : ∀ p∈xs,r.Contains (base+BitVec.ofNat 64 p.2) 16) :
    Frame [r] m (writeSlice xs base v m) := by
  induction xs generalizing m with
  | nil => exact Frame.refl _ _
  | cons p xs ih =>
    change Frame [r] m (writeSlice xs base v (m.write (base+BitVec.ofNat 64 p.2) 16 (v p.1)))
    exact ((Frame.refl [r] m).write (List.mem_singleton_self _) _ (hc p (by simp))).trans
      (ih _ (fun q hq => hc q (List.mem_cons_of_mem _ hq)))

/-- An explicit index for each callee-saved vector. -/
def savedReg (i : Fin 8) : VReg := saved[i.val]!

theorem extraSlots_mem (off : Nat) (p : VReg × Nat) :
    p∈extraSlots off ↔ ∃ i : Fin 8,p=(savedReg i,off+16*i.val) := by
  have he : extraSlots off = (List.finRange 8).map (fun i => (savedReg i,off+16*i.val)) := rfl
  rw [he]
  simp only [List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨i,hi⟩; exact ⟨i,hi.symm⟩
  · rintro ⟨i,hi⟩; exact ⟨i,hi.symm⟩
end VG.Proof.MlDsa.AArch64.Optimized.Paired
