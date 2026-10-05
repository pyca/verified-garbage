import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Bytes`. -/
section

namespace VG.Proof.TripleDes

open VG.Spec.TripleDes

def catBlock (b : Block) : BitVec 64 :=
  b[0] ++ b[1] ++ b[2] ++ b[3] ++ b[4] ++ b[5] ++ b[6] ++ b[7]

theorem block_list (b : Block) : b.toList = List.ofFn (fun i : Fin 8 => b[i.val]) := by
  simpa only [Vector.toList_ofFn] using
    (congrArg (fun v : Block => v.toList) (Vector.ofFn_getElem (xs := b))).symm

theorem decodeBlock_cat (b : Block) : decodeBlock b = VG.Proof.TripleDes.catBlock b := by
  unfold decodeBlock
  rw [VG.Proof.TripleDes.block_list]
  simp only [List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil]
  have h : (VG.Proof.TripleDes.catBlock b).setWidth 64 = VG.Proof.TripleDes.catBlock b := by simp
  rw [← h]
  simp only [VG.Proof.TripleDes.catBlock, BitVec.setWidth_append_eq_shiftLeft_setWidth_or]
  simp
  rfl


theorem blockAt_eq_of_frame {rs : List VG.Region} {m m' : VG.Mem} (p : VG.Addr)
    (hf : VG.Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : VG.Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes hd (by change 8 ≤ 2 ^ 64; decide) hi

theorem bytesAt_eq_of_frame {rs : List VG.Region} {m m' : VG.Mem} (p : VG.Addr) (n : Nat)
    (hf : VG.Frame rs m m') (hn : n ≤ 2 ^ 64)
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : VG.Region).Disjoint r) : bytesAt m' p n = bytesAt m p n := by
  unfold bytesAt
  apply List.map_congr_left
  intro i hi
  exact hf.bytes hd hn (List.mem_range.mp hi)


end VG.Proof.TripleDes

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.EcbMemory`. -/
section

namespace VG.Proof.TripleDes

open VG

theorem blocksAt_cons (m : Mem) (p : Addr) (n : Nat) :
    Spec.TripleDes.blocksAt m p (n + 1) = Spec.TripleDes.blockAt m p :: Spec.TripleDes.blocksAt m (p + 8) n := by
  rw [Spec.TripleDes.blocksAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.cons.injEq, true_and]
  apply List.map_congr_left
  intro i _
  apply congrArg (Spec.TripleDes.blockAt m)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (fun j => p + BitVec.ofNat 64 j) (by omega)

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (p : Addr) (n : Nat)
    (hd : ∀ r ∈ rs, (Region.mk p (8 * n)).Disjoint r) :
    Spec.TripleDes.blocksAt m' p n = Spec.TripleDes.blocksAt m p n := by
  unfold Spec.TripleDes.blocksAt
  apply List.map_congr_left
  intro i hi
  apply VG.Proof.TripleDes.blockAt_eq_of_frame _ hf
  intro r hr
  exact (hd r hr).sub_left (Offset.sub_base p (by
    have h := List.mem_range.mp hi
    omega))

end VG.Proof.TripleDes

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Schedule`. -/
section

namespace VG.Proof.TripleDes

open VG VG.Spec.TripleDes

theorem reverse_or8 (a b c d e f g h : BitVec 64) :
    a ||| b ||| c ||| d ||| e ||| f ||| g ||| h =
      h ||| g ||| f ||| e ||| d ||| c ||| b ||| a := by ac_rfl

theorem littleEndian_word (b : Nat → Byte) :
    (List.range 8).foldl (fun out j => out ||| ((b j).zeroExtend 64 <<< (8 * j))) (0 : BitVec 64) =
      (b 7 ++ b 6 ++ b 5 ++ b 4 ++ b 3 ++ b 2 ++ b 1 ++ b 0 : BitVec 64).setWidth 64 := by
  simp only [List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons,
    List.foldl_nil, List.nil_append, Nat.reduceAdd, Nat.reduceMul, BitVec.shiftLeft_zero]
  rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or]
  have hz : (0 : BitVec 64) ||| (b 0).zeroExtend 64 = (b 0).zeroExtend 64 := BitVec.zero_or
  rw [hz]
  simp only [BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add, Nat.reduceAdd]
  exact VG.Proof.TripleDes.reverse_or8 _ _ _ _ _ _ _ _


theorem readW64_cat (m : Mem) (p : Addr) :
    m.readW p 64 = (m (p + BitVec.ofNat 64 7) ++ m (p + BitVec.ofNat 64 6) ++
      m (p + BitVec.ofNat 64 5) ++ m (p + BitVec.ofNat 64 4) ++ m (p + BitVec.ofNat 64 3) ++
      m (p + BitVec.ofNat 64 2) ++ m (p + BitVec.ofNat 64 1) ++ m p : BitVec 64).setWidth 64 := by
  simp only [Mem.readW, Mem.read, BitVec.add_assoc]
  rw [BitVec.zero_width_append]
  rfl

theorem scheduleAt_readW (m : Mem) (p : Addr) (i : Nat) (hi : i < 48) :
    (scheduleAt m p)[i] = m.readW (p + BitVec.ofNat 64 (8 * i)) 64 := by
  have h := VG.Proof.TripleDes.littleEndian_word (fun j => m (p + BitVec.ofNat 64 (8 * i + j)))
  have hread := VG.Proof.TripleDes.readW64_cat m (p + BitVec.ofNat 64 (8 * i))
  rw [Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat,
    Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat,
    Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat,
    Offset.add_ofNat_add_ofNat] at hread
  simp only [scheduleAt, Vector.getElem_ofFn]
  exact h.trans hread.symm


theorem vector_getD {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) (fallback : α) :
    v.getD i fallback = v[i]'hi :=
  (Array.getElem_eq_getD fallback).symm

theorem componentSchedule_readW (m : Mem) (p : Addr) (c j : Nat) (hc : c < 3) (hj : j < 16) :
    (componentSchedule (scheduleAt m p) c).getD j 0 =
      (m.readW (p + BitVec.ofNat 64 (8 * (16 * c + j))) 64).setWidth 48 := by
  rw [VG.Proof.TripleDes.vector_getD _ j hj 0]
  simp only [componentSchedule, Vector.getElem_ofFn]
  rw [VG.Proof.TripleDes.vector_getD _ (16 * c + j) (by omega) 0, VG.Proof.TripleDes.scheduleAt_readW m p _ (by omega)]

theorem scheduleAt_eq_of_frame {rs : List Region} {m m' : Mem} (p : Addr)
    (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨p, 384⟩ : Region).Disjoint r) : scheduleAt m' p = scheduleAt m p := by
  apply Vector.ext
  intro i hi
  rw [VG.Proof.TripleDes.scheduleAt_readW m' p i hi, VG.Proof.TripleDes.scheduleAt_readW m p i hi]
  exact hf.readW (r := ⟨p, 384⟩)
    (Offset.contains_base p (by omega) (by omega)) hd (by decide)


end VG.Proof.TripleDes

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.KeyMemory`. -/
section

namespace VG.Proof.TripleDes

open VG VG.Spec.TripleDes

def componentOffset (n c : Nat) : Nat := if c = 2 ∧ n = 16 then 0 else 8 * c

def componentKeys (m : Mem) (p : Addr) (n c : Nat) : DesSchedule :=
  expandDesKey (decodeBlock (blockAt m (p + BitVec.ofNat 64 (VG.Proof.TripleDes.componentOffset n c))))

def expandedMemory (m : Mem) (p : Addr) (n : Nat) : Schedule :=
  Vector.ofFn fun i => ((if i.val < 16 then VG.Proof.TripleDes.componentKeys m p n 0 else
    if i.val < 32 then VG.Proof.TripleDes.componentKeys m p n 1 else VG.Proof.TripleDes.componentKeys m p n 2).getD (i.val % 16) 0).setWidth 64

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

theorem bytesAt_getD (m : Mem) (p : Addr) (n i : Nat) (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]

theorem bytesAt_component (m : Mem) (p : Addr) (n offset : Nat) (hi : offset + 8 ≤ n) :
    (Vector.ofFn fun j : Fin 8 => (bytesAt m p n).getD (offset + j.val) 0) =
      blockAt m (p + BitVec.ofNat 64 offset) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, blockAt]
  rw [VG.Proof.TripleDes.bytesAt_getD m p n _ (by omega), Offset.add_ofNat_add_ofNat]

theorem componentOffset_bound (n c : Nat) (hn : validKey n) (hc : c < 3) :
    VG.Proof.TripleDes.componentOffset n c + 8 ≤ n := by
  rcases hn with rfl | rfl <;> unfold VG.Proof.TripleDes.componentOffset
  · by_cases h : c = 2
    · rw [ite_eq_left (by simp only [h, and_self])]; decide
    · rw [ite_eq_right (by simp only [h, false_and, not_false_eq_true])]; omega
  · rw [ite_eq_right (by simp only [show ¬(24 : Nat) = 16 by decide, and_false, not_false_eq_true])]
    omega

theorem expandKey_memory (m : Mem) (p : Addr) (n : Nat) (hn : validKey n) :
    expandKey (bytesAt m p n) = VG.Proof.TripleDes.expandedMemory m p n := by
  have component (c : Nat) (hc : c < 3) :
      expandDesKey (decodeBlock (Vector.ofFn fun j : Fin 8 =>
        (bytesAt m p n).getD ((if c = 2 ∧ (bytesAt m p n).length = 16 then 0 else 8 * c) + j.val) 0)) =
        VG.Proof.TripleDes.componentKeys m p n c := by
    rw [VG.Proof.TripleDes.bytesAt_length]
    unfold VG.Proof.TripleDes.componentKeys
    exact congrArg (fun b => expandDesKey (decodeBlock b))
      (VG.Proof.TripleDes.bytesAt_component m p n (VG.Proof.TripleDes.componentOffset n c) (VG.Proof.TripleDes.componentOffset_bound n c hn hc))
  have third := component 2 (by decide)
  simp only [true_and] at third
  apply Vector.ext
  intro i hi
  simp only [expandKey, VG.Proof.TripleDes.expandedMemory, Vector.getElem_ofFn,
    component 0 (by decide), component 1 (by decide)]
  simp only [true_and, third]

end VG.Proof.TripleDes

end
