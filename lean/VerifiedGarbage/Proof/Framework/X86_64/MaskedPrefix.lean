module
public import VerifiedGarbage.TCB.X86_64.State
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp

import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Masked 512-bit moves of the first quadwords

With a mask enabling the first `2 c` quadwords (`c ≤ 4` blocks of 16
bytes), a masked load (`State.loadMasked512`) is the `c` blocks at its
address in the lanes below `c` and zero in the others (`loadMasked512_lanes`),
and a masked store (`State.storeMasked512`) is a write of its `c` low lanes
(`storeMasked512_prefix`), so that the lemmas about loads and writes apply.
-/

@[expose] public section

namespace VG.X86_64

/-- The bytes of quadword writes, each at most once: byte `x` is that of
the last quadword written over it, else memory's. -/
theorem foldl_qwrites_byte {a : Addr} (f : Nat → BitVec 64) :
    ∀ (l : List Nat), (∀ j ∈ l, j < 8) → ∀ (m : Mem) (x : Addr),
      l.foldl (fun m j => m.writeW (State.qAddr a j) (f j)) m x =
        if (x - a).toNat < 64 ∧ (x - a).toNat / 8 ∈ l then
          (f ((x - a).toNat / 8)).extractLsb' (8 * ((x - a).toNat % 8)) 8
        else m x
  | [], _, m, x => by simp
  | j :: l, hl, m, x => by
    simp only [List.foldl_cons]
    rw [foldl_qwrites_byte f l (fun j h => hl j (List.mem_cons_of_mem _ h))]
    have hj := hl j List.mem_cons_self
    -- The offset of `x` in quadword `j`.
    have e : (x - State.qAddr a j).toNat < 8 ↔ (x - a).toNat < 64 ∧ (x - a).toNat / 8 = j := by
      simp only [State.qAddr]
      rw [Offset.sub_add_eq, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * j < 2 ^ 64)]
      have := (x - a).isLt
      constructor
      · intro h
        by_cases hge : 8 * j ≤ (x - a).toNat
        · rw [show 2 ^ 64 - 8 * j + (x - a).toNat = 2 ^ 64 + ((x - a).toNat - 8 * j) by omega,
            Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at h
          omega
        · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
      · rintro ⟨h1, h2⟩
        rw [show 2 ^ 64 - 8 * j + (x - a).toNat = 2 ^ 64 + ((x - a).toNat - 8 * j) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        omega
    have eo : (x - a).toNat < 64 ∧ (x - a).toNat / 8 = j →
        (x - State.qAddr a j).toNat = (x - a).toNat % 8 := fun ⟨h1, h2⟩ => by
      simp only [State.qAddr]
      rw [Offset.sub_add_eq, BitVec.toNat_sub, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 8 * j < 2 ^ 64),
        show 2 ^ 64 - 8 * j + (x - a).toNat = 2 ^ 64 + ((x - a).toNat - 8 * j) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      omega
    by_cases hin : (x - a).toNat < 64 ∧ (x - a).toNat / 8 ∈ l
    · have hin' : (x - a).toNat < 64 ∧ (x - a).toNat / 8 ∈ j :: l := ⟨hin.1, List.mem_cons_of_mem _ hin.2⟩
      simp only [hin, hin', and_self, ite_true]
    · simp only [hin, ite_false, Mem.writeW, Mem.write]
      by_cases hq : (x - State.qAddr a j).toNat < 8
      · obtain ⟨h1, h2⟩ := e.mp hq
        have hin' : (x - a).toNat < 64 ∧ (x - a).toNat / 8 ∈ j :: l := ⟨h1, by rw [h2]; exact List.mem_cons_self⟩
        rw [ite_eq_left (show (x - State.qAddr a j).toNat < 64 / 8 from hq), ite_eq_left hin', eo ⟨h1, h2⟩, h2,
          BitVec.setWidth_eq]
      · have hin' : ¬ ((x - a).toNat < 64 ∧ (x - a).toNat / 8 ∈ j :: l) := by
          rintro ⟨h1, h2⟩
          rcases List.mem_cons.mp h2 with h2 | h2
          · exact hq (e.mpr ⟨h1, h2⟩)
          · exact hin ⟨h1, h2⟩
        rw [ite_eq_right (show ¬ (x - State.qAddr a j).toNat < 64 / 8 from hq), ite_eq_right hin']

/-- A masked store of the first `c` blocks of `v`: the write of its `c`
low lanes. -/
theorem State.storeMasked512_prefix {s : State} {a : Addr} {k : BitVec 64} {c : Nat} (hc : c ≤ 4)
    (hk : State.qOn k = List.range (2 * c)) (hin : InRegions s.wr a (16 * c)) (v : BitVec 512) :
    s.storeMasked512 a k v = some { s with mem := s.mem.writeW a (v.setWidth (128 * c)) } := by
  have hq : ∀ j ∈ State.qOn k, InRegions s.wr (State.qAddr a j) 8 := fun j hj => by
    rw [hk, List.mem_range] at hj
    exact CallLay.inRegions_sub hin (by omega) (by omega)
  unfold State.storeMasked512
  rw [ite_eq_left hq]
  congr 2
  funext x
  rw [foldl_qwrites_byte _ _ (qOn_lt k), hk]
  simp only [Mem.writeW, Mem.write, List.mem_range, show 128 * c / 8 = 16 * c by omega]
  by_cases hx : (x - a).toNat < 16 * c
  · rw [ite_eq_left (show (x - a).toNat < 64 ∧ (x - a).toNat / 8 < 2 * c by omega), ite_eq_left hx]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
    rw [decide_eq_true (show 8 * (x - a).toNat + i < 8 * (128 * c / 8) by omega),
      decide_eq_true (show 8 * (x - a).toNat + i < 128 * c by omega),
      decide_eq_true (show 8 * ((x - a).toNat % 8) + i < 64 by omega), Bool.true_and, Bool.true_and,
      Bool.true_and]
    exact congrArg _ (by omega)
  · rw [ite_eq_right (show ¬ ((x - a).toNat < 64 ∧ (x - a).toNat / 8 < 2 * c) by omega), ite_eq_right hx]

/-- Bit `n` of eight quadwords, the first the least significant. -/
theorem getLsbD_concat8 (q : Nat → BitVec 64) {n : Nat} (hn : n < 512) :
    (q 7 ++ q 6 ++ q 5 ++ q 4 ++ q 3 ++ q 2 ++ q 1 ++ q 0).getLsbD n = (q (n / 64)).getLsbD (n % 64) := by
  simp only [BitVec.getLsbD_append]
  split
  · rw [show n / 64 = 0 by omega, Nat.mod_eq_of_lt (by omega)]
  split
  · rw [show n / 64 = 1 by omega]; exact congrArg _ (by omega)
  split
  · rw [show n / 64 = 2 by omega]; exact congrArg _ (by omega)
  split
  · rw [show n / 64 = 3 by omega]; exact congrArg _ (by omega)
  split
  · rw [show n / 64 = 4 by omega]; exact congrArg _ (by omega)
  split
  · rw [show n / 64 = 5 by omega]; exact congrArg _ (by omega)
  split
  · rw [show n / 64 = 6 by omega]; exact congrArg _ (by omega)
  rw [show n / 64 = 7 by omega]; exact congrArg _ (by omega)

/-- A masked load of the first `c` blocks at `a`: those blocks in the lanes
below `c`, zero in the others. -/
theorem State.loadMasked512_prefix {s : State} {a : Addr} {k : BitVec 64} {c : Nat} (hc : c ≤ 4)
    (hk : State.qOn k = List.range (2 * c)) (hb : ∀ j < 8, k.getLsbD j = decide (j < 2 * c))
    (hin : InRegions (s.rd ++ s.wr) a (16 * c)) :
    ∃ v, s.loadMasked512 a k = some v ∧ ∀ l < 4, v.extractLsb' (128 * l) 128 =
      if l < c then s.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 else 0 := by
  have hq : ∀ j ∈ State.qOn k, InRegions (s.rd ++ s.wr) (State.qAddr a j) 8 := fun j hj => by
    rw [hk, List.mem_range] at hj
    exact CallLay.inRegions_sub hin (by omega) (by omega)
  unfold State.loadMasked512
  rw [ite_eq_left hq]
  refine ⟨_, rfl, fun l hl => ?_⟩
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_extractLsb', decide_eq_true hi, Bool.true_and,
    getLsbD_concat8 (fun j => if k.getLsbD j then s.mem.readW (State.qAddr a j) 64 else 0) (by omega)]
  have hj : (128 * l + i) / 64 < 8 := by omega
  simp only [hb _ hj]
  by_cases hlc : l < c
  · rw [decide_eq_true (show (128 * l + i) / 64 < 2 * c by omega), ite_eq_left rfl, ite_eq_left hlc]
    simp only [Mem.readW, BitVec.getLsbD_setWidth]
    rw [decide_eq_true (show (128 * l + i) % 64 < 64 by omega), decide_eq_true hi, Bool.true_and, Bool.true_and,
      getLsbD_read _ _ (by omega), getLsbD_read _ _ (by omega), State.qAddr, Offset.add_add, Offset.add_add]
    rw [show 8 * ((128 * l + i) / 64) + (128 * l + i) % 64 / 8 = 16 * l + i / 8 by omega,
      show (128 * l + i) % 64 % 8 = i % 8 by omega]
  · rw [decide_eq_false (show ¬ (128 * l + i) / 64 < 2 * c by omega), ite_eq_right hlc,
      ite_eq_right (by decide)]
    simp

end VG.X86_64
