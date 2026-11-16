module

public import VerifiedGarbage.Proof.Aes.AArch64.Encrypt
public import VerifiedGarbage.Proof.Framework.Bitslice.Sym
public import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
@[expose] public section

section

/-!
# AES counter mode on AArch64: the data's invariant

What the proofs of the counter-mode functions share: arithmetic of their
loops, and the data after `k` blocks, with the keystream (`keyStream`) XORed
into the first `16 k` bytes in place (`DataInv`) or out of place
(`DataInvM`).
-/

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes
open VG.Spec.Aes (roundKey)

/-! ## The loop -/

theorem ofNat_sub_one {j : Nat} (h : 0 < j) : BitVec.ofNat 64 j - 1 = BitVec.ofNat 64 (j - 1) := by
  rw [show j = (j - 1) + 1 by omega_arith, BitVec.ofNat_add, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

end VG.Proof.Aes.AArch64

end


namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes

/-- An access at an offset of a region. -/
theorem in_off {rs : List Region} {b : Addr} {len : Nat} (hr : (⟨b, len⟩ : Region) ∈ rs)
    {off n : Nat} (h : off + n ≤ len) (hl : len < 2 ^ 64) :
    InRegions rs (b + BitVec.ofNat 64 off) n :=
  ⟨_, hr, Offset.contains_base b h (by omega_arith)⟩

/-! ## The counter blocks -/

theorem sw_32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by simp

/-! ## The counter blocks as states -/

theorem rev32_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (rev32 v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  unfold rev32
  obtain ⟨t0, t1, t2, t3⟩ := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp
    (show (List.range 4).all (fun k => (List.range 8).all fun j => decide (
      (8 * k + j < 8 → 24 + (8 * k + j) = 8 * (3 - k) + j) ∧
      (¬ 8 * k + j < 8 ∧ 8 * k + j - 8 < 8 → 16 + (8 * k + j - 8) = 8 * (3 - k) + j) ∧
      (¬ 8 * k + j < 8 ∧ ¬ 8 * k + j - 8 < 8 ∧ 8 * k + j - 8 - 8 < 8 →
        8 + (8 * k + j - 8 - 8) = 8 * (3 - k) + j) ∧
      (¬ 8 * k + j < 8 ∧ ¬ 8 * k + j - 8 < 8 ∧ ¬ 8 * k + j - 8 - 8 < 8 →
        8 * k + j - 8 - 8 - 8 < 8 ∧ 0 + (8 * k + j - 8 - 8 - 8) = 8 * (3 - k) + j))) = true by decide +kernel)
    k (List.mem_range.mpr hk)) j (List.mem_range.mpr hj))
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split
  next h0 => rw [decide_eq_true h0, Bool.true_and, t0 h0]
  next h0 =>
    split
    next h1 => rw [decide_eq_true h1, Bool.true_and, t1 ⟨h0, h1⟩]
    next h1 =>
      split
      next h2 => rw [decide_eq_true h2, Bool.true_and, t2 ⟨h0, h1, h2⟩]
      next h2 => rw [decide_eq_true (t3 ⟨h0, h1, h2⟩).1, Bool.true_and, (t3 ⟨h0, h1, h2⟩).2]

/-! ## XOR into the data -/

/-- The data after `k` blocks: the keystream `ks` XORed into the first
`16 k` of the `16 n` bytes at `D`. -/
def DataInv (m₀ m : Mem) (D : Addr) (n k : Nat) (ks : Nat → Byte) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    m₀ (D + BitVec.ofNat 64 i) ^^^ (if i < 16 * k then ks i else 0)

theorem off_toNat (D : Addr) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 j)).toNat =
      if j ≤ i then i - j else 2 ^ 64 + i - j := Offset.sub_toNat' D hj hi

/-- The bytes at `O`: the `16 k` first, the `16 k` at `D` XORed with the
keystream; the rest, as they were. With `O = D`, `DataInv` (`dataInvM_self`). -/
def DataInvM (m₀ m : Mem) (D O : Addr) (n k : Nat) (ks : Nat → Byte) : Prop :=
  ∀ i < 16 * n, m (O + BitVec.ofNat 64 i) =
    if i < 16 * k then m₀ (D + BitVec.ofNat 64 i) ^^^ ks i else m₀ (O + BitVec.ofNat 64 i)

theorem dataInvM_self {m₀ m : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} :
    DataInvM m₀ m D D n k ks ↔ DataInv m₀ m D n k ks := by
  refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩ <;> rw [h i hi] <;> by_cases hk : i < 16 * k
  · rw [ite_eq_left hk, ite_eq_left hk]
  · rw [ite_eq_right hk, ite_eq_right hk]; exact BitVec.xor_zero.symm
  · rw [ite_eq_left hk, ite_eq_left hk]
  · rw [ite_eq_right hk, ite_eq_right hk]; exact BitVec.xor_zero

/-- A block of the text at `D` XORed with the keystream, stored at `O`. -/
theorem dataInvM_store1 {m₀ m : Mem} {D O : Addr} {n k : Nat} {ks : Nat → Byte} {v : BitVec 128}
    (hn : 16 * n < 2 ^ 64) (hk : k < n) (h : DataInvM m₀ m D O n k ks)
    (hv : ∀ t < 16, vbyte v t = ks (16 * k + t) ^^^ m₀ (D + BitVec.ofNat 64 (16 * k + t))) :
    DataInvM m₀ (m.write (O + BitVec.ofNat 64 (16 * k)) 16 v) D O n (k + 1) ks ∧
      Frame [⟨O, 16 * n⟩] m (m.write (O + BitVec.ofNat 64 (16 * k)) 16 v) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · show (if _ then _ else _) = _
    rw [off_toNat O (by omega_arith) (by omega_arith)]
    by_cases h1 : 16 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 16 * k < 16
      · rw [ite_eq_left h2, ite_eq_left (show i < 16 * (k + 1) by omega_arith)]
        show vbyte _ _ = _
        rw [hv _ h2, show 16 * k + (i - 16 * k) = i by omega_arith, BitVec.xor_comm]
      · rw [ite_eq_right h2, h i hi, ite_eq_right (show ¬ i < 16 * k by omega_arith),
          ite_eq_right (show ¬ i < 16 * (k + 1) by omega_arith)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 16 * k < 16 by omega_arith), h i hi,
        ite_eq_left (show i < 16 * k by omega_arith), ite_eq_left (show i < 16 * (k + 1) by omega_arith)]
  · have hx' : ¬ (x - O).toNat + 1 ≤ 16 * n := hx ⟨O, 16 * n⟩ (List.mem_singleton_self _)
    show (if _ then _ else _) = _
    rw [ite_eq_right]
    intro hlt
    apply hx'
    have e := Offset.toNat_sub_add x O (d := 16 * k) (by omega_arith)
    rw [Offset.sub_add_eq] at hlt
    have := (x - O).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 16 * k < 2 ^ 64 by omega_arith)] at hlt
    omega_arith

/-- The text at `D` from block `k` on is as in `m₀`: in place by `DataInvM`;
out of place, as in `m₃` (from block `j` on), which only the output's
stores, which do not overlap it, changed. -/
theorem src_keep {m₀ m₃ m : Mem} {D O : Addr} {n k j : Nat} {ks : Nat → Byte}
    (hDO : O = D ∨ Region.Disjoint ⟨D, 16 * n⟩ ⟨O, 16 * n⟩) (hn : 16 * n < 2 ^ 64)
    (h₃ : ∀ i, 16 * j ≤ i → i < 16 * n → m₃ (D + BitVec.ofNat 64 i) = m₀ (D + BitVec.ofNat 64 i))
    (hf : Frame [⟨O, 16 * n⟩] m₃ m) (h : DataInvM m₀ m D O n k ks) :
    ∀ i, 16 * k ≤ i → 16 * j ≤ i → i < 16 * n → m (D + BitVec.ofNat 64 i) = m₀ (D + BitVec.ofNat 64 i) := by
  intro i hk hj hi
  rcases hDO with rfl | hd
  · rw [h i hi, ite_eq_right (by omega_arith)]
  · rw [hf.bytes (R := ⟨D, 16 * n⟩) (by simp only [List.mem_singleton, forall_eq]; exact hd)
      (by simp only; omega_arith) hi]
    exact h₃ i hj hi

/-- The keystream, byte by byte: byte `i` is byte `i mod 16` of the
encrypted counter block `i / 16`. -/
def keyStream (R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) (i : Nat) : Byte :=
  (Spec.Aes.cipher R w (ctrState icb (i / 16))).getD (i % 16) 0

/-! ## A group -/

theorem dataInvM_frame {m₀ m m' : Mem} {D O : Addr} {n k : Nat} {ks : Nat → Byte} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨O, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : DataInvM m₀ m D O n k ks) : DataInvM m₀ m' D O n k ks := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨O, 16 * n⟩) hd (by simp only; omega_using [hn]) hi

end VG.Proof.Aes.AArch64
