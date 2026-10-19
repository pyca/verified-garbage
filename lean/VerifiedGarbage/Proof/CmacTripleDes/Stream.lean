module

public import VerifiedGarbage.Spec.Cmac.TripleDesContract
public import Mathlib.Data.List.Induction
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.CmacTripleDes.Scratch
import VerifiedGarbage.Proof.Cmac.Spec

/-!
# Streaming TDEA-CMAC: lemmas about the state

What every target's `vg_cmac_triple_des_absorb` and `vg_cmac_triple_des_finish`
need of the streaming state (`Spec.Cmac.tdesRepr`), whatever the ISA, as
`Proof/Cmac/Stream.lean` has them for AES's, with 8-byte blocks:

* `held n`, the number of bytes a state for a message of `n` bytes holds
  back: none for the empty message, else 1 to 8.
* `repr_fill`: absorbing `d` that fits in the block being held back
  (`d.length ≤ 8 - held n`) only appends `d` to the bytes held back.
* `repr_chain`: absorbing more chains the block held back, completed with
  the first `8 - held n` bytes of `d`, and then the whole blocks of the
  rest of `d` but its last 1 to 8 bytes, which it holds back.
* `repr_finish`: the chaining value and the bytes held back are what
  `vg_cmac_triple_des_finalize` takes, and its result is the MAC.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream

open VG Spec.Cmac

/-! ## Lengths -/

/-- The number of bytes held back for a message of `n` bytes. -/
def held (n : Nat) : Nat := n - chainedLen 8 n

theorem held_zero : held 0 = 0 := rfl

theorem held_pos {n : Nat} (h : 0 < n) : held n = (n - 1) % 8 + 1 := by
  unfold held chainedLen; omega

theorem held_le (n : Nat) : held n ≤ 8 := by unfold held chainedLen; omega

theorem chainedLen_add_held (n : Nat) : chainedLen 8 n + held n = n := by
  unfold held chainedLen; omega

theorem chainedLen_mod (n : Nat) : chainedLen 8 n % 8 = 0 := by unfold chainedLen; omega

theorem chainedLen_fill {n l : Nat} (h : l ≤ 8 - held n) : chainedLen 8 (n + l) = chainedLen 8 n := by
  unfold held chainedLen at *; omega

theorem held_fill {n l : Nat} (h : l ≤ 8 - held n) : held (n + l) = held n + l := by
  unfold held chainedLen at *; omega

/-- The number of whole blocks of `d` chained after the block held back is
completed with the first `8 - held n` bytes of `d`. -/
def nblocks (n l : Nat) : Nat := (l - (8 - held n) - 1) / 8

theorem chainedLen_chain {n l : Nat} (h : 8 - held n < l) :
    chainedLen 8 (n + l) = chainedLen 8 n + 8 + 8 * nblocks n l := by
  unfold nblocks held chainedLen at *; omega

theorem held_chain {n l : Nat} (h : 8 - held n < l) :
    held (n + l) = l - (8 - held n) - 8 * nblocks n l := by
  unfold nblocks held chainedLen at *; omega

theorem held_chain_pos {n l : Nat} (h : 8 - held n < l) :
    0 < l - (8 - held n) - 8 * nblocks n l ∧ l - (8 - held n) - 8 * nblocks n l ≤ 8 := by
  unfold nblocks; omega

/-! ## Blocks -/

theorem blocks_append {xs ys : List Byte} (hx : xs.length % 8 = 0) :
    blocks 8 (xs ++ ys) = blocks 8 xs ++ blocks 8 ys := by
  obtain ⟨q, hq⟩ : ∃ q, xs.length = 8 * q := ⟨xs.length / 8, by omega⟩
  simp only [blocks, List.length_append, hq,
    show (8 * q + ys.length) / 8 = q + ys.length / 8 by omega,
    Nat.mul_div_cancel_left _ (by decide : 0 < 8), List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  · apply List.map_congr_left
    intro i _
    simp only [Function.comp, Nat.mul_add, List.drop_append, hq]
    rw [List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]

theorem blocks_single {x : List Byte} (hx : x.length = 8) : blocks 8 x = [x] := by
  simp [blocks, hx, List.take_of_length_le]

theorem blocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    blocksAt m p 8 n = blocks 8 (Spec.Aes.bytesAt m p (8 * n)) := by
  simp only [blocksAt, blocks, Proof.Cmac.bytesAt_length, Nat.mul_div_cancel_left _ (by decide : 0 < 8)]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt]; omega)
  intro k h₁ h₂
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h₁
  simp [Spec.Aes.bytesAt, BitVec.add_assoc, BitVec.ofNat_add]

theorem bytesAt_congr {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m' p n = Spec.Aes.bytesAt m p n := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-! ## The state -/

/-- The key schedule and the subkeys at `p` are those of `key`, as `tdesRepr`
requires: `vg_cmac_triple_des_finalize`'s `key`. -/
def KeyAt (mem : Mem) (p : Addr) (key : List Byte) : Prop :=
  let ks := subkeys (tdes key) 8
  Spec.TripleDes.validKey key.length ∧ Spec.TripleDes.scheduleAt mem p = Spec.TripleDes.expandKey key ∧
    Spec.Aes.bytesAt mem (p + 384) 16 = ks.1 ++ ks.2

/-- `KeyAt` depends only on the first 400 bytes. -/
theorem KeyAt.congr {m m' : Mem} {p : Addr} {key : List Byte} (hk : KeyAt m p key)
    (h : ∀ i < 400, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) : KeyAt m' p key := by
  obtain ⟨hl, hs, hsk⟩ := hk
  refine ⟨hl, ?_, ?_⟩
  · rw [Proof.CmacTripleDes.scheduleAt_congr fun i hi => h i (by omega), hs]
  · rw [show p + 384 = p + BitVec.ofNat 64 384 from rfl,
      bytesAt_congr (m := m) fun i hi => by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h _ (by omega)]
    exact hsk

theorem repr_iff (mem : Mem) (p : Addr) (key msg : List Byte) :
    tdesRepr mem p key msg ↔ KeyAt mem p key ∧
      Spec.Aes.bytesAt mem (p + 400) 8 =
        chain (tdes key) (zeros 8) (blocks 8 (msg.take (chainedLen 8 msg.length))) ∧
      Spec.Aes.bytesAt mem (p + 408) (held msg.length) = msg.drop (chainedLen 8 msg.length) := by
  simp only [tdesRepr, KeyAt, held, and_assoc]

theorem length_take_chained (msg : List Byte) :
    (msg.take (chainedLen 8 msg.length)).length = chainedLen 8 msg.length := by
  have := chainedLen_add_held msg.length
  simp only [List.length_take]; omega

/-- Absorbing `d` that fits in the block held back. -/
theorem repr_fill {m m' : Mem} {p : Addr} {key msg d : List Byte} (hr : tdesRepr m p key msg)
    (hk : ∀ i < 400, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hl : d.length ≤ 8 - held msg.length)
    (hc : Spec.Aes.bytesAt m' (p + 400) 8 = Spec.Aes.bytesAt m (p + 400) 8)
    (hh : Spec.Aes.bytesAt m' (p + 408) (held msg.length + d.length) =
      Spec.Aes.bytesAt m (p + 408) (held msg.length) ++ d) :
    tdesRepr m' p key (msg ++ d) := by
  rw [repr_iff] at hr ⊢
  obtain ⟨hk', hc', hh'⟩ := hr
  have hn := chainedLen_add_held msg.length
  rw [List.length_append, chainedLen_fill hl, held_fill hl]
  refine ⟨hk'.congr hk, ?_, ?_⟩
  · rw [hc, hc', List.take_append_of_le_length (by omega)]
  · rw [hh, hh', List.drop_append_of_le_length (by omega)]

/-- Absorbing `d` that does not fit in the block held back. -/
theorem repr_chain {m m' : Mem} {p : Addr} {key msg d : List Byte} (hr : tdesRepr m p key msg)
    (hk : ∀ i < 400, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hl : 8 - held msg.length < d.length)
    (hc : Spec.Aes.bytesAt m' (p + 400) 8 =
      Spec.Cmac.chain (tdes key) (Spec.Aes.bytesAt m (p + 400) 8)
        ([Spec.Aes.bytesAt m (p + 408) (held msg.length) ++ d.take (8 - held msg.length)] ++
          blocks 8 ((d.drop (8 - held msg.length)).take (8 * nblocks msg.length d.length))))
    (hh : Spec.Aes.bytesAt m' (p + 408) (d.length - (8 - held msg.length) - 8 * nblocks msg.length d.length) =
      (d.drop (8 - held msg.length)).drop (8 * nblocks msg.length d.length)) :
    tdesRepr m' p key (msg ++ d) := by
  rw [repr_iff] at hr ⊢
  obtain ⟨hk', hc', hh'⟩ := hr
  have hn := chainedLen_add_held msg.length
  have hm := chainedLen_mod msg.length
  have hp := held_chain_pos hl
  have hle := held_le msg.length
  rw [List.length_append, chainedLen_chain hl, held_chain hl]
  generalize hcd : chainedLen 8 msg.length = c at *
  generalize hhd : held msg.length = h at *
  generalize hnb : nblocks msg.length d.length = nb at *
  have hdc : (msg.drop c).length = h := by simp; omega
  refine ⟨hk'.congr hk, ?_, ?_⟩
  · have e : (msg ++ d).take (c + 8 + 8 * nb) =
        msg.take c ++ ((msg.drop c ++ d.take (8 - h)) ++ (d.drop (8 - h)).take (8 * nb)) := by
      rw [List.take_append, List.take_of_length_le (by omega),
        show c + 8 + 8 * nb - msg.length = (8 - h) + 8 * nb by omega, List.take_add]
      simp only [List.append_assoc]
      rw [← List.append_assoc (List.take c msg), List.take_append_drop]
    have hx : (msg.drop c ++ d.take (8 - h)).length = 8 := by simp; omega
    rw [hc, hc', hh', e, blocks_append (by rw [List.length_take]; omega),
      blocks_append (by rw [hx]), blocks_single hx, Proof.Cmac.chain_append, Proof.Cmac.chain_append,
      Proof.Cmac.chain_append]
  · have e : (msg ++ d).drop (c + 8 + 8 * nb) = (d.drop (8 - h)).drop (8 * nb) := by
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, List.drop_drop]
      congr 1; omega
    rw [hh, e]

/-- The MAC is `macFull`'s, which has 8 bytes. -/
theorem tdesCmac_eq (key msg : List Byte) : tdesCmac key 8 msg = macFull (tdes key) 8 msg := by
  simp only [tdesCmac, mac]
  apply List.take_of_length_le
  simp only [macFull, Proof.Cmac.chain_append, Proof.Cmac.chain_single, tdes, tdesWith,
    Vector.length_toList, Nat.le_refl]

/-- What `vg_cmac_triple_des_finalize` takes of a state that represents `msg`. -/
theorem repr_finish {m : Mem} {p : Addr} {key msg : List Byte} (hr : tdesRepr m p key msg) :
    let c := chainedLen 8 msg.length
    (msg.take c).length % 8 = 0 ∧ (msg.take c = [] ∨ 0 < held msg.length) ∧
      Spec.Aes.bytesAt m (p + 400) 8 = Spec.Cmac.chain (tdes key) (zeros 8) (blocks 8 (msg.take c)) ∧
      msg.take c ++ Spec.Aes.bytesAt m (p + 408) (held msg.length) = msg := by
  rw [repr_iff] at hr
  obtain ⟨_, hc, hh⟩ := hr
  have hn := chainedLen_add_held msg.length
  refine ⟨by rw [length_take_chained]; exact chainedLen_mod _, ?_, hc, by rw [hh, List.take_append_drop]⟩
  by_cases h0 : msg.length = 0
  · exact .inl (by simp [List.eq_nil_of_length_eq_zero h0])
  · exact .inr (by rw [held_pos (by omega)]; omega)

/-- The streaming state represents a message by its 416 bytes alone. -/
theorem repr_congr_416 {m₁ m₂ : Mem} {p : Addr} {key msg : List Byte}
    (h : ∀ i < 416, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i))
    (hr : tdesRepr m₁ p key msg) : tdesRepr m₂ p key msg := by
  rw [repr_iff] at hr ⊢
  obtain ⟨hk, h3, h4⟩ := hr
  have hc := held_le msg.length
  refine ⟨hk.congr fun i hi => h i (by omega), ?_, ?_⟩
  · rw [show p + 400 = p + BitVec.ofNat 64 400 from rfl, bytesAt_congr (m := m₁) fun i hi => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h _ (by omega)]
    exact h3
  · rw [show p + 408 = p + BitVec.ofNat 64 408 from rfl, bytesAt_congr (m := m₁) fun i hi => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h _ (by omega)]
    exact h4

end VG.Proof.CmacTripleDes.Stream
