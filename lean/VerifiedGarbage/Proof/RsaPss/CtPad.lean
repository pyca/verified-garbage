import VerifiedGarbage.Proof.MdStream.Spec

/-!
# Padding a message of secret length

The constant-time hashing of RSASSA-PSS's verification
(`Proof/RsaPss/X86_64/CtHash.lean`) pads a message of `ℓ` bytes, followed
by zeros, in a buffer of `nbm` blocks, without looking at `ℓ` but through
masks: it sets byte `ℓ` to `0x80` and writes the length field at the end of
block `⌊(ℓ + L) / B⌋`. `padded` is what the buffer then holds, and it is
the padded message `Md.pad` over its first `⌊(ℓ + L) / B⌋ + 1` blocks
(`pad_length`, `pad_getD`).
-/

namespace VG.Proof.RsaPss

open VG.Proof.MdStream

/-- The index of the last block of the padded message of `ℓ` bytes. -/
def lastBlk (B L ℓ : Nat) : Nat := (ℓ + L) / B

/-- Byte `i` of the padded message, from the message, its length field
`len`, and the sizes. -/
def padded (B L : Nat) (msg len : List Byte) (i : Nat) : Byte :=
  if i < msg.length then msg.getD i 0
  else if i = msg.length then 0x80
  else if B * lastBlk B L msg.length + B - L ≤ i ∧ i < B * lastBlk B L msg.length + B then
    len.getD (i - (B * lastBlk B L msg.length + B - L)) 0
  else 0

theorem getD_app {l l' : List Byte} {n : Nat} :
    (l ++ l').getD n 0 = if n < l.length then l.getD n 0 else l'.getD (n - l.length) 0 := by
  simp only [List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by omega)]
  · rw [List.getElem?_append_right (by omega)]

/-- The padded message's length, `ℓ + 1 + z + L`, fills `⌊(ℓ + L) / B⌋ + 1` blocks. -/
theorem pad_total {B L ℓ : Nat} (hB : 0 < B) (hLB : L < B) :
    ℓ + 1 + (2 * B - L - 1 - ℓ % B) % B + L = B * (lastBlk B L ℓ + 1) := by
  unfold lastBlk
  have e := Nat.div_add_mod ℓ B
  have hr := Nat.mod_lt ℓ hB
  generalize ℓ / B = q at e
  generalize ℓ % B = r at e hr ⊢
  subst e
  by_cases h : r + L + 1 ≤ B
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.div_eq_of_lt_le (k := q) (by rw [Nat.mul_comm]; omega) (by rw [Nat.mul_comm, Nat.succ_mul]; omega)]
    rw [Nat.mul_add]; omega
  · rw [Nat.mod_eq_of_lt (by omega),
      Nat.div_eq_of_lt_le (k := q + 1) (by rw [Nat.mul_comm, Nat.mul_add]; omega)
        (by rw [Nat.add_mul, Nat.add_mul]; rw [Nat.mul_comm] at *; omega)]
    rw [Nat.mul_add, Nat.mul_add]; omega

variable {B N L : Nat} (H : Md B N L)

theorem pad_length (msg : List Byte) (hB : 0 < B) (hLB : L < B) :
    (H.pad msg).length = B * (lastBlk B L msg.length + 1) := by
  simp only [Md.pad, List.length_append, List.length_cons, List.length_nil, List.length_replicate,
    H.lenBytes_length]
  have := pad_total (ℓ := msg.length) hB hLB
  omega

theorem pad_getD (msg : List Byte) (hB : 0 < B) (hLB : L < B) {i : Nat}
    (hi : i < B * (lastBlk B L msg.length + 1)) :
    (H.pad msg).getD i 0 = padded B L msg (H.lenBytes msg.length) i := by
  have hz := pad_total (ℓ := msg.length) hB hLB
  have hlen := H.lenBytes_length msg.length
  simp only [Md.pad, padded]
  generalize (2 * B - L - 1 - msg.length % B) % B = z at hz
  generalize lastBlk B L msg.length = fb at hz hi
  rw [Nat.mul_add, Nat.mul_one] at hz hi
  simp only [getD_app, List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  by_cases h1 : i < msg.length
  · simp only [h1, ite_true, show i < msg.length + (0 + 1) by omega, show i < msg.length + (0 + 1) + z by omega]
  · by_cases h2 : i = msg.length
    · subst h2
      repeat' split
      all_goals first | omega | simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Nat.sub_self,
        Option.getD_some]
    · have h3 : ¬ i < msg.length + (0 + 1) := by omega
      by_cases h4 : i < msg.length + (0 + 1) + z
      · simp only [h1, h2, h3, h4, ite_true, ite_false, List.getD_eq_getElem?_getD,
          List.getElem?_replicate]
        repeat' split
        all_goals first | rfl | omega
      · simp only [h1, h2, h3, h4, ite_false]
        split
        · congr 1; omega
        · omega

end VG.Proof.RsaPss
