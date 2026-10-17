module

public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The values of the arrays of the key working space

`Arrs m B w A live`: each array `j ∈ live` holds `A j`. A step that writes
the arrays `js` keeps the others (`Arrs.keep`), and one that writes `o`
updates `A` there (`Arrs.write`, with `upd`). The lists are literals, so the
side conditions are decided.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- `A` with `j ↦ v`. -/
def upd (A : Nat → Nat) (j v : Nat) : Nat → Nat := fun i => if i = j then v else A i

/-- The arrays `live` hold `A`. -/
def Arrs (m : Mem) (B : BitVec 32) (w : Nat) (A : Nat → Nat) (live : List Nat) : Prop :=
  ∀ j ∈ live, num m B w j = A j

theorem Arrs.get {m : Mem} {B : BitVec 32} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {j : Nat} (hj : j ∈ live) : num m B w j = A j := h j hj

theorem Arrs.nil (m : Mem) (B : BitVec 32) (w : Nat) (A : Nat → Nat) : Arrs m B w A [] :=
  fun _ h => absurd h List.not_mem_nil

/-- Tracking one more array. -/
theorem Arrs.add {m : Mem} {B : BitVec 32} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {o v : Nat} (e : num m B w o = v) : Arrs m B w (upd A o v) (o :: live) := by
  intro j hj
  simp only [upd]
  split
  · subst j; exact e
  · rename_i hne
    exact h j ((List.mem_cons.mp hj).resolve_left hne)

/-- One more array, whose value is already `A`'s. -/
theorem Arrs.cons {m : Mem} {B : BitVec 32} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {o : Nat} (e : num m B w o = A o) : Arrs m B w A (o :: live) := by
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj'
  · exact e
  · exact h j hj'

/-- Fewer arrays. -/
theorem Arrs.sub {m : Mem} {B : BitVec 32} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {live' : List Nat} (hs : ∀ j ∈ live', j ∈ live) : Arrs m B w A live' :=
  fun j hj => h j (hs j hj)

/-- The same values, as another function. -/
theorem Arrs.congr {m : Mem} {B : BitVec 32} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {A' : Nat → Nat} (e : live.map A = live.map A') : Arrs m B w A' live := by
  intro j hj
  rw [h j hj]
  induction live with
  | nil => exact absurd hj List.not_mem_nil
  | cons k l ih =>
    simp only [List.map_cons, List.cons.injEq] at e
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact e.1
    · exact ih (fun i hi => h i (List.mem_cons_of_mem _ hi)) e.2 hj'

/-- A step that writes none of the arrays `live`. -/
theorem Arrs.keep {m m' : Mem} {B : BitVec 32} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {js ds : List Nat} (k : Keep B w js ds m m') {s : State} {Z N : Nat}
    (hw : Ws s B Z w N) (hl : ∀ j ∈ live, j < N ∧ j ∉ js) (hd : ∀ d ∈ ds, d + 4 ≤ hdr) :
    Arrs m' B w A live := by
  intro j hj
  rw [k.num (fun k' hk e => (hl j hj).2 (by subst e; exact hk)) hd (hw.fit64 (hl j hj).1)]
  exact h j hj

/-- A step that writes `o := v`, and of the arrays `live` no other. -/
theorem Arrs.write {m m' : Mem} {B : BitVec 32} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {js ds : List Nat} (k : Keep B w js ds m m') {s : State} {Z N : Nat}
    (hw : Ws s B Z w N) {o v : Nat} (e : num m' B w o = v)
    (hl : ∀ j ∈ live, j = o ∨ (j < N ∧ j ∉ js)) (hd : ∀ d ∈ ds, d + 4 ≤ hdr) :
    Arrs m' B w (upd A o v) live := by
  intro j hj
  simp only [upd]
  split
  · subst j; exact e
  · rcases hl j hj with e' | ⟨hN, hn⟩
    · contradiction
    · rw [k.num (fun k' hk e => hn (by subst e; exact hk)) hd (hw.fit64 hN)]
      exact h j hj

/-- `upd` at another index. -/
theorem upd_ne (A : Nat → Nat) {i j : Nat} (v : Nat) (h : i ≠ j) : upd A j v i = A i := by
  simp only [upd, h, ↓reduceIte]

theorem upd_self (A : Nat → Nat) (j v : Nat) : upd A j v j = v := by simp only [upd, ↓reduceIte]

/-- `upd` to the value already there. -/
theorem upd_noop {A : Nat → Nat} {j v : Nat} (h : A j = v) : upd A j v = A :=
  funext fun i => by
    simp only [upd]
    split
    · subst i; exact h.symm
    · rfl

end VG.Proof.Rsa.Arm.Keys
