module

public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Arrays and header words apart from a literal list of ranges

Many steps of key generation keep an array, or the header, because what they
change is a short literal list of ranges: arrays (`(slot w j, 8 * (w + 2))`)
and header words (`(8 * k, 8)`). `SlotShape w L H js` says once that each range
of `L` is a header range of `H` or array `j` for some `j ∈ js`; from it,
`SlotShape.apartW`, `geD` and `leD` give the facts the frame lemmas take,

* `∀ r ∈ L, slot w a + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w a`,
* `∀ r ∈ L, c ≤ r.1`,
* `∀ r ∈ L, r.1 + r.2 ≤ slot w a`,

from Boolean side conditions about the indices and the header ranges alone,
which `rfl` decides. A proof term at the call site, rather than a tactic that
unfolds every constant and runs `omega` on each range, keeps the step cheap in
the large contexts of the proofs that use it.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG.Proof.Bignum VG.Impl.Bignum.Public
open VG.Impl.Bignum (hdrBytes)

theorem slot_lo {w a j n : Nat} (hn : n ≤ 8 * (w + 2)) (h : a < j) : slot w a + n ≤ slot w j := by
  have := Nat.mul_le_mul_right (8 * (w + 2)) (show a + 1 ≤ j from h)
  rw [Nat.add_mul, Nat.one_mul] at this
  unfold slot
  omega_using [this, hn]

theorem slot_hi {w a j : Nat} (h : j < a) : slot w j + 8 * (w + 2) ≤ slot w a := by
  have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ a from h)
  rw [Nat.add_mul, Nat.one_mul] at this
  unfold slot
  omega_using [this]

theorem le_slot {c w j : Nat} (h : c ≤ hdrBytes) : c ≤ slot w j :=
  Nat.le_trans h (Nat.le_add_right _ _)

theorem hdr_le_slot {o l w a : Nat} (h : o + l ≤ hdrBytes) : o + l ≤ slot w a :=
  Nat.le_trans h (Nat.le_add_right _ _)

theorem mul_le_w2 {w : Nat} : 8 * w ≤ 8 * (w + 2) := Nat.mul_le_mul_left 8 (Nat.le_add_right _ _)

theorem mul_le_w1 {w : Nat} : 8 * (w + 1) ≤ 8 * (w + 2) :=
  Nat.mul_le_mul_left 8 (Nat.add_le_add_left (by decide) _)

/-- Each range of `L` is a header range of `H`, or array `j` for some `j ∈ js`. -/
def SlotShape (w : Nat) (L H : List (Nat × Nat)) (js : List Nat) : Prop :=
  ∀ r ∈ L, r ∈ H ∨ ∃ j ∈ js, r = (slot w j, 8 * (w + 2))

/-- Array `a`'s first `n` bytes are apart from each range. -/
theorem SlotShape.apart {w a n : Nat} {L H : List (Nat × Nat)} {js : List Nat} (hs : SlotShape w L H js)
    (hn : n ≤ 8 * (w + 2)) (hH : ∀ h ∈ H, h.1 + h.2 ≤ hdrBytes) (hj : ∀ j ∈ js, j ≠ a) :
    ∀ r ∈ L, slot w a + n ≤ r.1 ∨ r.1 + r.2 ≤ slot w a := fun r hr =>
  match hs r hr with
  | .inl h => .inr (hdr_le_slot (hH r h))
  | .inr ⟨j, hj', e⟩ => by
    subst e
    rcases Nat.lt_or_gt_of_ne (hj j hj') with h | h
    exacts [.inr (slot_hi h), .inl (slot_lo hn h)]

/-- Each range starts at `c` or later. -/
theorem SlotShape.ge {w c : Nat} {L H : List (Nat × Nat)} {js : List Nat} (hs : SlotShape w L H js)
    (hc : c ≤ hdrBytes) (hH : ∀ h ∈ H, c ≤ h.1) : ∀ r ∈ L, c ≤ r.1 := fun r hr =>
  match hs r hr with
  | .inl h => hH r h
  | .inr ⟨_, _, e⟩ => e ▸ le_slot hc

/-- Each range ends at array `a` or before. -/
theorem SlotShape.le {w a : Nat} {L H : List (Nat × Nat)} {js : List Nat} (hs : SlotShape w L H js)
    (hH : ∀ h ∈ H, h.1 + h.2 ≤ hdrBytes) (hj : ∀ j ∈ js, j < a) : ∀ r ∈ L, r.1 + r.2 ≤ slot w a := fun r hr =>
  match hs r hr with
  | .inl h => hdr_le_slot (hH r h)
  | .inr ⟨j, hj', e⟩ => e ▸ slot_hi (hj j hj')

/-! The same, with the closed side conditions as `decide`d Booleans, for a
proof term to give by `rfl`. -/

theorem SlotShape.apartW {w a : Nat} {L H : List (Nat × Nat)} {js : List Nat} (hs : SlotShape w L H js)
    (hH : H.all (fun h => decide (h.1 + h.2 ≤ hdrBytes)) = true) (hj : js.all (fun j => decide (j ≠ a)) = true) :
    ∀ r ∈ L, slot w a + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w a :=
  hs.apart mul_le_w2 (fun h hh => of_decide_eq_true (List.all_eq_true.mp hH h hh))
    (fun j hj' => of_decide_eq_true (List.all_eq_true.mp hj j hj'))

theorem SlotShape.apartW1 {w a : Nat} {L H : List (Nat × Nat)} {js : List Nat} (hs : SlotShape w L H js)
    (hH : H.all (fun h => decide (h.1 + h.2 ≤ hdrBytes)) = true) (hj : js.all (fun j => decide (j ≠ a)) = true) :
    ∀ r ∈ L, slot w a + 8 * (w + 1) ≤ r.1 ∨ r.1 + r.2 ≤ slot w a :=
  hs.apart mul_le_w1 (fun h hh => of_decide_eq_true (List.all_eq_true.mp hH h hh))
    (fun j hj' => of_decide_eq_true (List.all_eq_true.mp hj j hj'))

theorem SlotShape.geD {w c : Nat} {L H : List (Nat × Nat)} {js : List Nat} (hs : SlotShape w L H js)
    (hc : decide (c ≤ hdrBytes) = true) (hH : H.all (fun h => decide (c ≤ h.1)) = true) : ∀ r ∈ L, c ≤ r.1 :=
  hs.ge (of_decide_eq_true hc) (fun h hh => of_decide_eq_true (List.all_eq_true.mp hH h hh))

theorem SlotShape.leD {w a : Nat} {L H : List (Nat × Nat)} {js : List Nat} (hs : SlotShape w L H js)
    (hH : H.all (fun h => decide (h.1 + h.2 ≤ hdrBytes)) = true) (hj : js.all (fun j => decide (j < a)) = true) :
    ∀ r ∈ L, r.1 + r.2 ≤ slot w a :=
  hs.le (fun h hh => of_decide_eq_true (List.all_eq_true.mp hH h hh))
    (fun j hj' => of_decide_eq_true (List.all_eq_true.mp hj j hj'))

/-- Header word `k` is apart from each range. -/
theorem SlotShape.hdrW {w k : Nat} {L H : List (Nat × Nat)} {js : List Nat} (hs : SlotShape w L H js)
    (hk : decide (8 * k + 8 ≤ hdrBytes) = true)
    (hH : H.all (fun h => decide (8 * k + 8 ≤ h.1 ∨ h.1 + h.2 ≤ 8 * k)) = true) :
    ∀ r ∈ L, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := fun r hr =>
  match hs r hr with
  | .inl h => of_decide_eq_true (List.all_eq_true.mp hH r h)
  | .inr ⟨_, _, e⟩ => e ▸ .inl (le_slot (of_decide_eq_true hk))

/-- Header word `k` is apart from one range past the header. -/
theorem past_hdrW {w j l k : Nat} (hk : decide (8 * k + 8 ≤ hdrBytes) = true) :
    ∀ r ∈ [(slot w j, l)], 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := fun _ hr =>
  List.mem_singleton.mp hr ▸ .inl (le_slot (of_decide_eq_true hk))

/-- Array `a` is apart from one array-sized range at array `j`. -/
theorem apart_one {w a j l : Nat} (hl : l ≤ 8 * (w + 2)) (hj : decide (j ≠ a) = true) :
    ∀ r ∈ [(slot w j, l)], slot w a + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w a := fun _ hr => by
  obtain rfl := List.mem_singleton.mp hr
  rcases Nat.lt_or_gt_of_ne (of_decide_eq_true hj) with h | h
  exacts [.inr (Nat.le_trans (Nat.add_le_add_left hl _) (slot_hi h)), .inl (slot_lo mul_le_w2 h)]

/-- One array. -/
theorem arr_shape (w j : Nat) : SlotShape w [(slot w j, 8 * (w + 2))] [] [j] := fun _ hr =>
  .inr ⟨j, .head _, List.mem_singleton.mp hr⟩

/-- A list of header ranges. -/
theorem hdr_shape (w : Nat) (L : List (Nat × Nat)) : SlotShape w L L [] := fun _ h => .inl h

/-- What a Montgomery product into array `a` changes (`aAcc`, `aTmp` and `a`). -/
theorem mm_shape (w a : Nat) :
    SlotShape w [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w a, 8 * (w + 2))] []
      [aAcc, aTmp, a] := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [.inr ⟨_, .head _, rfl⟩, .inr ⟨_, .tail _ (.head _), rfl⟩, .inr ⟨_, .tail _ (.tail _ (.head _)), rfl⟩]

end VG.Proof.RsaKeyGen
