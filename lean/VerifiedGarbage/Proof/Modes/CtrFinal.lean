module

public import VerifiedGarbage.Spec.Ctr.Final
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.AesCbc.Spec

/-!
# CTR of a message's last piece, for any block cipher and target

Not trusted. A final CTR function (`vg_<cipher>_ctr_final`) calls the
whole-block CTR function on the `n = len / 16` whole blocks of its data,
which leaves `Tₙ₊₁` in the counter block, then, if `u = len % 16 ≠ 0` bytes
are left, the same function on one block of zeros of its own, which leaves
`Oₙ₊₁ = CIPH_K(Tₙ₊₁)` there (`crypt_zero`) and `Tₙ₊₂` in the counter block,
and XORs the first `u` bytes of that block into the data. `cryptFinal_of`:
what that leaves is `Spec.Ctr.CryptFinal`. Nothing here depends on a cipher
or a target.
-/

@[expose] public section

namespace VG.Proof.Modes.CtrFinal

open VG
open VG.Spec.Aes (bytesAt)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map, Function.comp_def, BitVec.ofNat_add,
    BitVec.add_assoc]

/-- `16 n` bytes, as `n` blocks. -/
theorem bytesAt_blocks (m : Mem) (p : Addr) : ∀ n, bytesAt m p (16 * n) = (Spec.Cbc.blocksAt m p n).flatten
  | 0 => by simp [bytesAt, Spec.Cbc.blocksAt]
  | n + 1 => by
    have e : Spec.Cbc.blocksAt m p (n + 1) =
        Spec.Cbc.blocksAt m p n ++ [bytesAt m (p + BitVec.ofNat 64 (16 * n)) 16] := by
      simp [Spec.Cbc.blocksAt, List.range_succ]
    rw [Nat.mul_succ, bytesAt_add, bytesAt_blocks m p n, e, List.flatten_append, List.flatten_singleton]

/-- The `len` bytes at `p`: its whole blocks, then the rest. -/
theorem bytesAt_blocks_tail (m : Mem) (p : Addr) (len : Nat) :
    bytesAt m p len = (Spec.Cbc.blocksAt m p (len / 16)).flatten ++
      bytesAt m (p + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) := by
  have h := bytesAt_add m p (16 * (len / 16)) (len % 16)
  rw [Nat.div_add_mod] at h
  rw [h, bytesAt_blocks]

/-- The `u` bytes at `T` XORed with the first `u` of `o`, a byte at a time. -/
theorem bytesAt_xor {m₀ m' : Mem} {T : Addr} {u : Nat} {o : List Byte} (hu : u ≤ o.length)
    (h : ∀ q < u, m' (T + BitVec.ofNat 64 q) = m₀ (T + BitVec.ofNat 64 q) ^^^ o.getD q 0) :
    bytesAt m' T u = Spec.Cbc.xor (bytesAt m₀ T u) o := by
  apply List.ext_getElem (by simp [bytesAt, Spec.Cbc.xor]; omega)
  intro q h₁ h₂
  have hq : q < u := by simpa [bytesAt] using h₁
  simp only [bytesAt, Spec.Cbc.xor, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  rw [h q hq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- XORing blocks of 16 bytes, all at once. -/
theorem xor_flatten : ∀ (xs os : List (List Byte)), (∀ x ∈ xs, x.length = 16) → (∀ o ∈ os, o.length = 16) →
    xs.length = os.length → Spec.Cbc.xor xs.flatten os.flatten = (List.zipWith Spec.Cbc.xor xs os).flatten
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => absurd h (by simp)
  | _ :: _, [], _, _, h => absurd h (by simp)
  | x :: xs, o :: os, hx, ho, h => by
    simp only [List.flatten_cons, List.zipWith_cons_cons, Spec.Cbc.xor]
    rw [List.zipWith_append (by rw [hx x (by simp), ho o (by simp)])]
    exact congrArg _ (xor_flatten xs os (fun y hy => hx y (by simp [hy])) (fun y hy => ho y (by simp [hy]))
      (by simpa using h))

theorem blocksAt_length16 (m : Mem) (p : Addr) (n : Nat) : ∀ x ∈ Spec.Cbc.blocksAt m p n, x.length = 16 := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  exact bytesAt_length _ _ _

theorem outputs_length16 {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = 16) (t : List Byte) (n : Nat) :
    ∀ o ∈ (Spec.Ctr.counters t n).map ciph, o.length = 16 := by
  intro o ho
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp ho
  exact hc a

theorem outputs_flatten_length {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = 16) :
    ∀ (t : List Byte) (n : Nat), ((Spec.Ctr.counters t n).map ciph).flatten.length = 16 * n
  | _, 0 => rfl
  | t, n + 1 => by
    simp only [Spec.Ctr.counters, List.map_cons, List.flatten_cons, List.length_append, hc,
      outputs_flatten_length hc (Spec.Ctr.inc t) n]
    omega

theorem flatten_length {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = 16) (m : Mem) (p : Addr)
    (t : List Byte) (n : Nat) :
    (Spec.Cbc.blocksAt m p n).flatten.length = ((Spec.Ctr.counters t n).map ciph).flatten.length := by
  rw [← bytesAt_blocks, bytesAt_length, outputs_flatten_length hc]

/-- CTR's whole blocks, flattened. -/
theorem crypt_flatten {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = 16) (m : Mem) (p : Addr)
    (t : List Byte) (n : Nat) :
    Spec.Cbc.xor (Spec.Cbc.blocksAt m p n).flatten ((Spec.Ctr.counters t n).map ciph).flatten =
      (Spec.Ctr.crypt ciph t (Spec.Cbc.blocksAt m p n)).flatten := by
  rw [xor_flatten _ _ (blocksAt_length16 m p n) (outputs_length16 hc t n)
    (by simp [AesCbc.length_blocksAt, AesCtr.length_counters]), Spec.Ctr.crypt, AesCbc.length_blocksAt]

/-- The number of blocks of `len` bytes, the last possibly partial. -/
theorem blockCount_eq (len : Nat) :
    Spec.Ctr.blockCount len = if len % 16 = 0 then len / 16 else len / 16 + 1 := by
  unfold Spec.Ctr.blockCount
  split <;> omega

/-- CTR of one block of zeros: the output block. -/
theorem crypt_zero {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = 16) (t : List Byte) :
    Spec.Ctr.crypt ciph t [List.replicate 16 0] = [ciph t] := by
  simp only [Spec.Ctr.crypt, List.length_singleton, Spec.Ctr.counters, List.map_cons, List.map_nil,
    List.zipWith_cons_cons, List.zipWith_nil_left]
  refine congrArg (· :: []) (List.ext_getElem (by simp [Spec.Cbc.xor, hc]) fun i h₁ h₂ => ?_)
  simp only [Spec.Cbc.xor, List.getElem_zipWith, List.getElem_replicate]
  exact BitVec.zero_xor

/-- The block at `p` after the one-block call, from the zeros it held. -/
theorem bytesAt_of_blocksAt_one {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = 16) {m₀ m : Mem}
    {p : Addr} {t : List Byte} (hz : bytesAt m₀ p 16 = List.replicate 16 0)
    (h : Spec.Cbc.blocksAt m p 1 = Spec.Ctr.crypt ciph t (Spec.Cbc.blocksAt m₀ p 1)) : bytesAt m p 16 = ciph t := by
  have e : ∀ m' : Mem, Spec.Cbc.blocksAt m' p 1 = [bytesAt m' p 16] := fun m' => by
    simp [Spec.Cbc.blocksAt]
  rw [e, e, hz, crypt_zero hc] at h
  exact List.head_eq_of_cons_eq h

/-- CTR of the `len` bytes at `D` from the counter block at `P`, from what a
final function leaves: its `n = len / 16` whole blocks as CTR's from
`T₁`, its last `len % 16` bytes XORed a byte at a time with
`CIPH_K(Tₙ₊₁)`, and the counter block advanced once per block, a partial
one included. -/
theorem cryptFinal_of {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = 16) {m₀ m' : Mem} {P D : Addr}
    {len : Nat}
    (hblocks : Spec.Cbc.blocksAt m' D (len / 16) =
      Spec.Ctr.crypt ciph (bytesAt m₀ P 16) (Spec.Cbc.blocksAt m₀ D (len / 16)))
    (htail : ∀ q < len % 16, m' (D + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 q) =
      m₀ (D + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 q) ^^^
        (ciph (Spec.Ctr.next (bytesAt m₀ P 16) (len / 16))).getD q 0)
    (hctr : bytesAt m' P 16 =
      Spec.Ctr.next (bytesAt m₀ P 16) (if len % 16 = 0 then len / 16 else len / 16 + 1)) :
    Spec.Ctr.CryptFinal ciph m₀ m' P D len := by
  refine ⟨?_, by rw [hctr, blockCount_eq]⟩
  have hu : len % 16 < 16 := Nat.mod_lt _ (by decide)
  have ht := bytesAt_xor (o := ciph (Spec.Ctr.next (bytesAt m₀ P 16) (len / 16))) (by rw [hc]; omega) htail
  have hx := crypt_flatten hc m₀ D (bytesAt m₀ P 16) (len / 16)
  rw [Spec.Ctr.cryptFinal, bytesAt_length, blockCount_eq, bytesAt_blocks_tail m' D len, hblocks, ht,
    bytesAt_blocks_tail m₀ D len]
  split
  · rename_i h0
    have e : ∀ (m : Mem) (p : Addr), bytesAt m p (len % 16) = [] := fun m p => by rw [h0]; rfl
    rw [e, List.append_nil, ← hx]
    simp only [Spec.Cbc.xor, List.zipWith_nil_left, List.append_nil]
  · rw [AesCtr.counters_succ, List.map_append, List.flatten_append, List.map_singleton, List.flatten_singleton]
    simp only [Spec.Cbc.xor] at hx ⊢
    rw [List.zipWith_append (flatten_length hc m₀ D _ _), hx]

end VG.Proof.Modes.CtrFinal
