import VerifiedGarbage.Proof.Blowfish.Table
import VerifiedGarbage.Proof.Blowfish.KeySched

/-!
# Key expansion's facts about memory, on every target

The table of the initial schedule as bytes and words (`table_byte`,
`table_P`); memory holding the initial S-boxes and the keyed P-array holds
`keyed key` (`keyed_of_mem`); the key's bytes and words; where the S-box
entries the encryptions write go (`entryOff_sbox`).
-/

namespace VG.Proof.Blowfish

open VG VG.Spec.Blowfish

theorem readW64_byte (m : Mem) (a : Addr) {b : Nat} (hb : b < 8) :
    m (a + BitVec.ofNat 64 b) = (m.readW a 64).extractLsb' (8 * b) 8 := by
  rw [← Mem.extractLsb'_read m a (n := 8) hb]
  simp only [Mem.readW]
  rfl

theorem initWords_getD {i : Nat} (hi : i < 521) : Impl.Blowfish.initWords.getD i 0 = Impl.Blowfish.initWord i := by
  simp [Impl.Blowfish.initWords, hi]

/-- The table's bytes are the initial schedule's. -/
theorem table_byte {m : Mem} {T : Addr}
    (held : ∀ i < 521, m.readW (T + BitVec.ofNat 64 (8 * i)) 64 = Impl.Blowfish.initWords.getD i 0)
    {o : Nat} (ho : o < 4168) : m (T + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o := by
  have e := initWord_byte (o / 8) (b := o % 8) (Nat.mod_lt _ (by decide))
  rw [show 8 * (o / 8) + o % 8 = o by omega] at e
  rw [← e, ← initWords_getD (by omega), ← held _ (by omega),
    ← readW64_byte _ _ (Nat.mod_lt _ (by decide)), Offset.add_add, show 8 * (o / 8) + o % 8 = o by omega]

/-- The initial P-array's words. -/
theorem table_P {m : Mem} {T : Addr}
    (hT : ∀ o < 4168, m (T + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o) {i : Nat} (hi : i < 18) :
    m.readW (T + BitVec.ofNat 64 (4096 + 4 * i)) 32 = initial.getD i 0 := by
  refine word_ext fun b hb => ?_
  rw [← Mem.readW_byte m _ hb, Offset.add_add, hT _ (by omega),
    show 4096 + 4 * i + b = entryOff i b by simp [entryOff, hi], initByte_entry (by omega) hb]

theorem keyed_getD (key : List Byte) {i : Nat} (hi : i < 1042) :
    (keyed key).getD i 0 =
      if i < 18 then initial.getD i 0 ^^^ keyWord key i else initial.getD i 0 := by
  rw [keyed, getD_ofFn _ hi]

/-- Memory holding the initial S-boxes and the keyed P-array holds `keyed key`. -/
theorem keyed_of_mem {m : Mem} {S : Addr} {key : List Byte}
    (hS : ∀ o < 4096, m (S + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o)
    (hP : ∀ i < 18, m.readW (S + BitVec.ofNat 64 (4096 + 4 * i)) 32 = initial.getD i 0 ^^^ keyWord key i) :
    scheduleAt m S = keyed key := by
  refine scheduleAt_of_bytes fun i hi b hb => ?_
  rw [keyed_getD _ hi]
  by_cases h : i < 18
  · simp only [h, ite_true]
    rw [show entryOff i b = 4096 + 4 * i + b by simp [entryOff, h], ← Offset.add_add,
      Mem.readW_byte m (S + BitVec.ofNat 64 (4096 + 4 * i)) hb, hP i h]
  · simp only [h, ite_false]
    have := entryOff_lt hi hb
    rw [hS _ (by unfold entryOff at this ⊢; simp only [h, ite_false] at this ⊢; omega), initByte_entry hi hb]

theorem bytesAt_getD (m : Mem) (K : Addr) {L c : Nat} (hc : c < L) :
    (bytesAt m K L).getD c 0 = m (K + BitVec.ofNat 64 c) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hc]

theorem keyWord_eq (key : List Byte) (i : Nat) :
    keyWord key i = ((((0 : Word) <<< 8 ||| (key.getD ((4 * i + 0) % key.length) 0).zeroExtend 32) <<< 8 |||
      (key.getD ((4 * i + 1) % key.length) 0).zeroExtend 32) <<< 8 |||
      (key.getD ((4 * i + 2) % key.length) 0).zeroExtend 32) <<< 8 |||
      (key.getD ((4 * i + 3) % key.length) 0).zeroExtend 32 := rfl

theorem mod_succ (a L : Nat) (_hL : 0 < L) : (a % L + 1) % L = (a + 1) % L := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem shr_byte (x : BitVec 32) (k : Nat) : (x >>> k).setWidth 8 = x.extractLsb' k 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', hi,
    decide_true, Bool.true_and]

theorem set!_eq_set {α : Type} {n : Nat} (xs : Vector α n) {i : Nat} (h : i < n) (x : α) :
    xs.set! i x = xs.set i x h := by
  apply Vector.toArray_inj.mp
  simp [Vector.toArray_set!, Array.set!_eq_setIfInBounds, Array.setIfInBounds, h]

/-- The S-box entries written after `j` encryptions. -/
def sDone (j : Nat) : Nat := 2 * (j - 9)

/-- Entry `2 j` is byte `sDone j` of the S-boxes, at its offset in the planes. -/
theorem entryOff_sbox {j b : Nat} (hj : 9 ≤ j) (hj' : j < 521) (k : Nat) (hk : k < 2) :
    1024 * (sDone j / 256) + sDone j % 256 + (256 * b + k) = entryOff (2 * j + k) b := by
  unfold entryOff sDone; simp only [show ¬ 2 * j + k < 18 by omega, ite_false]; omega

theorem ksIter_zero (key : List Byte) : ksIter key 0 = (keyed key, 0, 0) := rfl

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr} {L : Nat}
    (h : ∀ c < L, ∀ r ∈ rs, ¬ r.Contains (K + BitVec.ofNat 64 c) 1) : bytesAt m' K L = bytesAt m K L := by
  simp only [bytesAt]
  exact List.map_congr_left fun c hc => hf _ fun r hr => h c (List.mem_range.mp hc) r hr

end VG.Proof.Blowfish
