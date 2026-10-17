module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.Arm.Isa
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The ARMv7 PKCS #1 v1.5 functions: bytes and words in memory

Strings of bytes and words (`Spec.Rsa.bytesAt`, `Spec.Rsa.wordsAt`) that
memory changes elsewhere keep, and strings of bytes from their bytes.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm

open VG

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem wordsAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n * 8⟩ r) (hn : n * 8 ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf.readW (r := ⟨p, n * 8⟩) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

/-- A string of bytes from each of its bytes. -/
theorem bytesAt_eq {m : Mem} {p : Addr} {xs : List Byte}
    (h : ∀ i < xs.length, m (p + BitVec.ofNat 64 i) = xs.getD i 0) :
    Spec.Rsa.bytesAt m p xs.length = xs := by
  apply List.ext_getElem (bytesAt_length _ _ _)
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  rw [h i h₂, ← List.getElem_eq_getD 0]

/-- Byte `i` of a string of bytes. -/
theorem bytesAt_getD {m : Mem} {p : Addr} {n i : Nat} (hi : i < n) (d : Byte) :
    (Spec.Rsa.bytesAt m p n).getD i d = m (p + BitVec.ofNat 64 i) := by
  rw [← List.getElem_eq_getD (h := by rw [bytesAt_length]; exact hi) d]
  simp [Spec.Rsa.bytesAt]

/-- Strings of bytes that read alike. -/
theorem bytesAt_of_read {m m' : Mem} {a b : Addr} {n : Nat} (h : m'.read a n = m.read b n) : Spec.Rsa.bytesAt m' a n = Spec.Rsa.bytesAt m b n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have e₁ := Mem.extractLsb'_read m' a hi
  have e₂ := Mem.extractLsb'_read m b hi
  rw [← e₁, ← e₂, h]

theorem getD_append_right {α : Type} (l l' : List α) (d : α) {n : Nat} (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_append_left {α : Type} (l l' : List α) (d : α) {n : Nat} (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- A byte apart from what memory changed. -/
theorem _root_.VG.Frame.byte1 {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {x : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨x, 1⟩ r) : m' x = m x :=
  hf x fun r hr hc => hd r hr x (by simp [Region.Contains]) hc

/-- A down-counter after one step. -/
theorem sub_one_ofNat {k : Nat} (h : k + 1 < 2 ^ 32) : BitVec.ofNat 32 (k + 1) - 1 = BitVec.ofNat 32 k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  rw [Nat.mod_eq_of_lt (a := k + 1) h, show 2 ^ 32 - 1 + (k + 1) = k + 2 ^ 32 by omega, Nat.add_mod_right]

/-- `subs`'s Z flag of a down-counter, as `bne`'s condition. -/
theorem ne_counter {k : Nat} (h : k + 1 < 2 ^ 32) :
    (!(BitVec.ofNat 32 (k + 1) - 1 == 0)) = decide (0 < k) := by
  rw [sub_one_ofNat h]
  by_cases hk : k = 0
  · subst hk; rfl
  · have : (BitVec.ofNat 32 k == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact hk this
    rw [this]; simp; omega

/-- An immediate below 256 is encodable (rotation 0). -/
theorem encodable_of_lt {v : BitVec 32} (h : v.toNat < 256) : VG.Arm.encodable v = true :=
  List.any_eq_true.2 ⟨0, by simp, by
    have h0 : v.rotateLeft (2 * 0) = v := by ext i; simp
    simpa only [h0, decide_eq_true_eq] using h⟩

end VG.Proof.RsaPkcs1Sig.Arm
