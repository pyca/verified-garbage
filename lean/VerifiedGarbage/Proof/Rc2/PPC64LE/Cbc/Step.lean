module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Rc2.PPC64LE.Run
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Rc2.CbcList
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RC2-CBC on PPC64LE: one block

`body_run`: an iteration of the loop takes the invariant `Inv` from `j` blocks
done to `j + 1`.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE.Cbc

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE VG.Impl.Rc2.PPC64LE.Cbc

/-- The buffers: the schedule at `T`, the chaining value at `I`, `n` blocks
at `D` and the working space at `W`, apart. -/
structure Regions (T I D W : Addr) (n : Nat) : Prop where
  TI : (⟨T, 128⟩ : Region).Disjoint ⟨I, 8⟩
  TD : (⟨T, 128⟩ : Region).Disjoint ⟨D, 8 * n⟩
  TW : (⟨T, 128⟩ : Region).Disjoint ⟨W, 512⟩
  ID : (⟨I, 8⟩ : Region).Disjoint ⟨D, 8 * n⟩
  IW : (⟨I, 8⟩ : Region).Disjoint ⟨W, 512⟩
  DW : (⟨D, 8 * n⟩ : Region).Disjoint ⟨W, 512⟩
  fit : 8 * n ≤ 2 ^ 64

/-- After `j` of the `n` blocks, from memory `m₀` and with our caller's
registers `g`. -/
structure Inv (d : Spec.Rc2.Direction) (T I D W : Addr) (n : Nat) (g : Reg → BitVec 64) (m₀ : Mem)
    (s₀ : State) (j : Nat) (t : State) : Prop where
  rd : t.rd = [⟨T, 128⟩]
  wr : t.wr = [⟨I, 8⟩, ⟨D, 8 * n⟩, ⟨W, 512⟩]
  r26 : t.gpr .r26 = T
  r27 : t.gpr .r27 = I
  r28 : t.gpr .r28 = D + BitVec.ofNat 64 (8 * j)
  r29 : t.gpr .r29 = BitVec.ofNat 64 (n - j)
  r30 : t.gpr .r30 = W
  pres : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → t.gpr r = s₀.gpr r
  saved : Spill.Saved W g saved t.mem
  sched : Spec.Rc2.scheduleAt t.mem T = Spec.Rc2.scheduleAt m₀ T
  done : Spec.Rc2.blocksAt t.mem D j =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt m₀ T) d (Spec.Rc2.blockAt m₀ I) (Spec.Rc2.blocksAt m₀ D j)).1
  iv : Spec.Rc2.blockAt t.mem I =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt m₀ T) d (Spec.Rc2.blockAt m₀ I) (Spec.Rc2.blocksAt m₀ D j)).2
  rest : ∀ i, j ≤ i → i < n → Spec.Rc2.blockAt t.mem (D + BitVec.ofNat 64 (8 * i)) =
    Spec.Rc2.blockAt m₀ (D + BitVec.ofNat 64 (8 * i))

theorem saved_fits : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide
theorem saved_in : ∀ p ∈ saved, 256 ≤ p.2 ∧ p.2 + 8 ≤ 312 := by decide

/-- What a step leaves alone: anything apart from the block, the chaining
value and the block function's working space. -/
theorem step_frame {T I D W : Addr} {n j : Nat} (R : Regions T I D W n) (hj : j < n) {m m' : Mem}
    (F : Frame [⟨D + BitVec.ofNat 64 (8 * j), 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] m m') :
    Spec.Rc2.scheduleAt m' T = Spec.Rc2.scheduleAt m T ∧
    (∀ g, Spill.Saved W g saved m → Spill.Saved W g saved m') ∧
    (∀ i, i < n → i ≠ j → Spec.Rc2.blockAt m' (D + BitVec.ofNat 64 (8 * i)) =
      Spec.Rc2.blockAt m (D + BitVec.ofNat 64 (8 * i))) ∧
    Spec.Rc2.blocksAt m' D j = Spec.Rc2.blocksAt m D j := by
  have hf := R.fit
  have bj : Region.Sub ⟨D + BitVec.ofNat 64 (8 * j), 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega)
  have W256 : Region.Sub ⟨W, 256⟩ ⟨W, 512⟩ := Region.sub_prefix (by decide)
  refine ⟨Proof.Rc2.scheduleAt_frame F T ?_, fun g sv => sv.frame F ?_, fun i hi hne => Proof.Rc2.blockAt_frame F _ ?_,
    Proof.Rc2.blocksAt_frame F D j ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact R.TD.sub_right bj
    · exact R.TI
    · exact R.TW.sub_right W256
  · intro p hp r hr
    have hb := saved_in p hp
    have slot : Region.Sub ⟨W + BitVec.ofNat 64 p.2, 8⟩ ⟨W, 512⟩ := Offset.sub_base W (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (R.DW.sub_left bj).symm.sub_left slot
    · exact (R.IW.symm.sub_left slot)
    · exact Offset.disjoint_base W (by omega) (by omega)
  · have bi : Region.Sub ⟨D + BitVec.ofNat 64 (8 * i), 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact Offset.disjoint D (by omega) (by omega) (by omega)
    · exact (R.ID.sub_right bi).symm
    · exact (R.DW.sub_left bi).sub_right W256
  · have bp : Region.Sub ⟨D, 8 * j⟩ ⟨D, 8 * n⟩ := Region.sub_prefix (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact Offset.base_disjoint D (by omega) (by omega)
    · exact (R.ID.sub_right bp).symm
    · exact (R.DW.sub_left bp).sub_right W256

theorem blocksAt_one (m : Mem) (p : Addr) : Spec.Rc2.blocksAt m p 1 = [Spec.Rc2.blockAt m p] := by
  simp [Spec.Rc2.blocksAt]

/-- The done blocks, one more. -/
theorem done_succ (m : Mem) (D : Addr) (j : Nat) :
    Spec.Rc2.blocksAt m D (j + 1) = Spec.Rc2.blocksAt m D j ++ [Spec.Rc2.blockAt m (D + BitVec.ofNat 64 (8 * j))] := by
  rw [Proof.Rc2.blocksAt_add, blocksAt_one]

theorem covers {T I D W : Addr} {n j : Nat} (hj : j < n) :
    Covers ([⟨T, 128⟩] ++ [⟨D + BitVec.ofNat 64 (8 * j), 8⟩, ⟨W, 256⟩])
      ([⟨T, 128⟩] ++ [⟨I, 8⟩, ⟨D, 8 * n⟩, ⟨W, 512⟩]) := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨⟨D, 8 * n⟩, by simp, 8 * j, rfl, by simp; omega⟩
  · exact ⟨⟨W, 512⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩

theorem covers_wr {I D W : Addr} {n j : Nat} (hj : j < n) :
    Covers [⟨D + BitVec.ofNat 64 (8 * j), 8⟩, ⟨W, 256⟩] [⟨I, 8⟩, ⟨D, 8 * n⟩, ⟨W, 512⟩] := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨D, 8 * n⟩, by simp, 8 * j, rfl, by simp; omega⟩
  · exact ⟨⟨W, 512⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩

end VG.Proof.Rc2.PPC64LE.Cbc
