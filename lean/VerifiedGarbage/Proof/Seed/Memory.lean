import VerifiedGarbage.Spec.Seed
import VerifiedGarbage.Proof.Seed.Rounds
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SEED's contracts' views of memory, as loads

The schedule's words are little-endian 32-bit loads (`scheduleAt_readW`,
`roundKey_readW`), and a block's words big-endian ones: byte-reversed
little-endian loads (`decodeQ_blockAt`).
-/

namespace VG.Proof.Seed

open VG VG.Spec.Seed

theorem reverse_or4 (a b c d : BitVec 32) : a ||| b ||| c ||| d = d ||| c ||| b ||| a := by ac_rfl

theorem littleEndian_word32 (b : Nat → Byte) :
    (List.range 4).foldl (fun out j => out ||| ((b j).zeroExtend 32 <<< (8 * j))) (0 : BitVec 32) =
      (b 3 ++ b 2 ++ b 1 ++ b 0 : BitVec 32).setWidth 32 := by
  simp only [List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons,
    List.foldl_nil, List.nil_append, Nat.reduceAdd, Nat.reduceMul, BitVec.shiftLeft_zero]
  rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or]
  have hz : (0 : BitVec 32) ||| (b 0).zeroExtend 32 = (b 0).zeroExtend 32 := BitVec.zero_or
  rw [hz]
  simp only [BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add, Nat.reduceAdd]
  exact reverse_or4 _ _ _ _

theorem readW32_cat (m : Mem) (p : Addr) :
    m.readW p 32 = (m (p + BitVec.ofNat 64 3) ++ m (p + BitVec.ofNat 64 2) ++
      m (p + BitVec.ofNat 64 1) ++ m p : BitVec 32) := by
  simp only [Mem.readW, Mem.read, BitVec.add_assoc]
  rw [BitVec.zero_width_append]
  rfl

theorem scheduleAt_readW (m : Mem) (p : Addr) (i : Nat) (hi : i < 32) :
    (scheduleAt m p)[i] = m.readW (p + BitVec.ofNat 64 (4 * i)) 32 := by
  have h := littleEndian_word32 (fun j => m (p + BitVec.ofNat 64 (4 * i + j)))
  have hread := readW32_cat m (p + BitVec.ofNat 64 (4 * i))
  rw [Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat] at hread
  simp only [scheduleAt, Vector.getElem_ofFn]
  rw [h, hread, BitVec.setWidth_eq]
  simp only [Nat.add_zero]

theorem vector_getD {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) (fallback : α) :
    v.getD i fallback = v[i]'hi :=
  (Array.getElem_eq_getD fallback).symm

theorem roundKey_readW (m : Mem) (p : Addr) {j : Nat} (hj : j < 16) :
    roundKey (scheduleAt m p) j =
      (m.readW (p + BitVec.ofNat 64 (8 * j)) 32, m.readW (p + BitVec.ofNat 64 (8 * j) + 4) 32) := by
  rw [roundKey, vector_getD _ (2 * j) (by omega), vector_getD _ (2 * j + 1) (by omega),
    scheduleAt_readW _ _ (2 * j) (by omega), scheduleAt_readW _ _ (2 * j + 1) (by omega),
    show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_ofNat_add_ofNat,
    show 4 * (2 * j) = 8 * j by omega, show 4 * (2 * j + 1) = 8 * j + 4 by omega]

/-- A block's word at `k`, big-endian, from the byte-reversed load. -/
theorem wordAt_blockAt (m : Mem) (q : Addr) {k : Nat} (hk : k ≤ 12) :
    wordAt (blockAt m q) k = byteRev32 (m.readW (q + BitVec.ofNat 64 k) 32) := by
  rw [byteRev32_readW]
  simp only [wordAt, blockAt]
  rw [vector_getD _ _ (by omega), vector_getD _ _ (by omega), vector_getD _ _ (by omega),
    vector_getD _ _ (by omega)]
  simp only [Vector.getElem_ofFn]
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.add_ofNat_add_ofNat,
    Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat]

/-- A block's words, big-endian, from the byte-reversed loads. -/
theorem decodeQ_blockAt (m : Mem) (q : Addr) :
    decodeQ (blockAt m q) = (byteRev32 (m.readW (q + BitVec.ofNat 64 0) 32),
      byteRev32 (m.readW (q + BitVec.ofNat 64 4) 32), byteRev32 (m.readW (q + BitVec.ofNat 64 8) 32),
      byteRev32 (m.readW (q + BitVec.ofNat 64 12) 32)) := by
  have hw : ∀ k : Nat, k ≤ 12 → wordAt (blockAt m q) k =
      byteRev32 (m.readW (q + BitVec.ofNat 64 k) 32) := fun k hk => wordAt_blockAt m q hk
  simp only [decodeQ]
  rw [hw 0 (by decide), hw 4 (by decide), hw 8 (by decide), hw 12 (by decide)]

end VG.Proof.Seed
