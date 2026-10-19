module

public import VerifiedGarbage.Proof.Rsa.KeyArrays
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs

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
def upd (A : Nat → Nat) (j v : Nat) : Nat → Nat :=
  fun i => if i = j then v else A i

/-- The arrays `live` hold `A`. -/
def Arrs (m : Mem) (B : BitVec 32) (w : Nat) (A : Nat → Nat) (live : List Nat) : Prop :=
  ∀ j ∈ live, num m B w j = A j

theorem Arrs.get {m : Mem} {B : BitVec 32} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {j : Nat} (hj : j ∈ live) : num m B w j = A j :=
  VG.Proof.Rsa.KeyWorkspace.Arrs.get h hj

theorem Arrs.nil (m : Mem) (B : BitVec 32) (w : Nat) (A : Nat → Nat) : Arrs m B w A [] :=
  VG.Proof.Rsa.KeyWorkspace.Arrs.nil m (State.addr B) w A

/-- Tracking one more array. -/
theorem Arrs.add {m : Mem} {B : BitVec 32} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {o v : Nat} (e : num m B w o = v) : Arrs m B w (upd A o v) (o :: live) :=
  VG.Proof.Rsa.KeyWorkspace.Arrs.add h e

/-- One more array, whose value is already `A`'s. -/
theorem Arrs.cons {m : Mem} {B : BitVec 32} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {o : Nat} (e : num m B w o = A o) : Arrs m B w A (o :: live) :=
  VG.Proof.Rsa.KeyWorkspace.Arrs.cons h e

/-- Fewer arrays. -/
theorem Arrs.sub {m : Mem} {B : BitVec 32} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {live' : List Nat} (hs : ∀ j ∈ live', j ∈ live) : Arrs m B w A live' :=
  VG.Proof.Rsa.KeyWorkspace.Arrs.sub h hs

/-- The same values, as another function. -/
theorem Arrs.congr {m : Mem} {B : BitVec 32} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {A' : Nat → Nat} (e : live.map A = live.map A') : Arrs m B w A' live :=
  VG.Proof.Rsa.KeyWorkspace.Arrs.congr h e

/-- A step that writes none of the arrays `live`. -/
theorem Arrs.keep {m m' : Mem} {B : BitVec 32} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {js ds : List Nat} (k : Keep B w js ds m m') {s : State} {Z N : Nat}
    (hw : Ws s B Z w N) (hl : ∀ j ∈ live, j < N ∧ j ∉ js) (hd : ∀ d ∈ ds, d + 4 ≤ hdr) :
    Arrs m' B w A live := by
  intro j hj
  change num m' B w j = A j
  rw [k.num (fun k' hk e => (hl j hj).2 (by subst e; exact hk)) hd (hw.fit64 (hl j hj).1)]
  exact h j hj

/-- A step that writes `o := v`, and of the arrays `live` no other. -/
theorem Arrs.write {m m' : Mem} {B : BitVec 32} {w : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B w A live) {js ds : List Nat} (k : Keep B w js ds m m') {s : State} {Z N : Nat}
    (hw : Ws s B Z w N) {o v : Nat} (e : num m' B w o = v)
    (hl : ∀ j ∈ live, j = o ∨ (j < N ∧ j ∉ js)) (hd : ∀ d ∈ ds, d + 4 ≤ hdr) :
    Arrs m' B w (upd A o v) live := by
  intro j hj
  change num m' B w j = upd A o v j
  simp only [upd]
  split
  · subst j; exact e
  · rcases hl j hj with e' | ⟨hN, hn⟩
    · contradiction
    · rw [k.num (fun k' hk e => hn (by subst e; exact hk)) hd (hw.fit64 hN)]
      exact h j hj

/-- `upd` at another index. -/
theorem upd_ne (A : Nat → Nat) {i j : Nat} (v : Nat) (h : i ≠ j) : upd A j v i = A i :=
  VG.Proof.Rsa.KeyWorkspace.upd_ne A v h

theorem upd_self (A : Nat → Nat) (j v : Nat) : upd A j v j = v :=
  VG.Proof.Rsa.KeyWorkspace.upd_self A j v

/-- `upd` to the value already there. -/
theorem upd_noop {A : Nat → Nat} {j v : Nat} (h : A j = v) : upd A j v = A :=
  VG.Proof.Rsa.KeyWorkspace.upd_noop h

end VG.Proof.Rsa.Arm.Keys
