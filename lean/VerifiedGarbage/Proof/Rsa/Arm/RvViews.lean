module

public import VerifiedGarbage.Proof.Rsa.Arm.RvBase
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The key working space read with `w` and with `W = 2 w + 2` words

With `W` words, the stride is twice that with `w`, and array `j` is the
arrays `2 j` and `2 j + 1` with `w`. A step that changes some arrays read
one way changes the arrays that contain them read the other way
(`Keep.toW`, `Keep.ofW`), and the arrays it does not change keep their
values (`Arrs.keepOf`). A number of `W` words is the number of `w` words
in array `2 j`, when the rest of the two arrays is zero (`numW_of`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

theorem S_W (w : Nat) : S (2 * w + 2) = 2 * S w := by simp only [S]; omega

theorem arr_W (w j : Nat) : arr (2 * w + 2) j = arr w (2 * j) := by
  simp only [arr, S]; rw [Nat.mul_comm 2 j, Nat.mul_assoc]; congr 2; omega

end VG.Proof.Rsa.Arm.Recover

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Recover VG.Impl.Rsa.Arm.Keys

/-- A step that keeps the arrays read with `w` but `js` keeps the arrays
read with `W` but those that contain them. -/
theorem Keep.toW {B : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem} (k : Keep B w js ds m m') :
    Keep B (2 * w + 2) (js.map (· / 2)) ds m m' := by
  intro x hx
  refine k x fun r hr => ?_
  simp only [ranges, List.mem_append, List.mem_map] at hr hx
  rcases hr with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
  · have := hx (arr (2 * w + 2) (j / 2), S (2 * w + 2)) (.inl ⟨j / 2, ⟨j, hj, rfl⟩, rfl⟩)
    rw [arr_W, S_W] at this
    have e1 : arr w (2 * (j / 2)) ≤ arr w j := arr_mono (by omega)
    have e2 : arr w j + S w ≤ arr w (2 * (j / 2)) + 2 * S w := by
      rw [← arr_succ, show 2 * S w = S w + S w by omega, ← Nat.add_assoc, ← arr_succ, ← arr_succ]
      exact arr_mono (by omega)
    dsimp only at this ⊢
    omega
  · exact hx (d, 4) (.inr ⟨d, hd, rfl⟩)

/-- A step that keeps the arrays read with `W` but `js` keeps the arrays
read with `w` but the two in each. -/
theorem Keep.ofW {B : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (k : Keep B (2 * w + 2) js ds m m') :
    Keep B w (js.flatMap fun j => [2 * j, 2 * j + 1]) ds m m' := by
  intro x hx
  refine k x fun r hr => ?_
  simp only [ranges, List.mem_append, List.mem_map, List.mem_flatMap] at hr hx
  rcases hr with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
  · have h1 := hx (arr w (2 * j), S w) (.inl ⟨2 * j, ⟨j, hj, by simp⟩, rfl⟩)
    have h2 := hx (arr w (2 * j + 1), S w) (.inl ⟨2 * j + 1, ⟨j, hj, by simp⟩, rfl⟩)
    rw [arr_W, S_W]
    rw [arr_succ] at h2
    dsimp only at h1 h2 ⊢
    omega
  · exact hx (d, 4) (.inr ⟨d, hd, rfl⟩)

/-- The arrays a step does not change keep their values, given that they
fit in the address space. -/
theorem Arrs.keepOf {m m' : Mem} {B : BitVec 32} {v : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B v A live) {js ds : List Nat} (k : Keep B v js ds m m')
    (hl : ∀ j ∈ live, ∀ i ∈ js, i ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (fit : ∀ j ∈ live, arr v j + S v ≤ 2 ^ 64) : Arrs m' B v A live := by
  intro j hj
  rw [k.num (hl j hj) hd (fit j hj)]
  exact h j hj

end VG.Proof.Rsa.Arm.Keys

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys

/-- A number of `W` words: the `w + 2` words of array `2 j` and the `w`
words of array `2 j + 1`. -/
theorem numW (m : Mem) (B : BitVec 32) (w j : Nat) :
    num m B (2 * w + 2) j = val32 m (State.addr B) (arr w (2 * j)) (w + 2) +
      2 ^ (32 * (w + 2)) * num m B w (2 * j + 1) := by
  simp only [num]
  rw [arr_W, show 2 * w + 2 = (w + 2) + w by omega, val32_append, arr_succ]

theorem numW_of {m : Mem} {B : BitVec 32} {w j x : Nat}
    (h0 : val32 m (State.addr B) (arr w (2 * j)) (w + 2) = x) (h1 : num m B w (2 * j + 1) = 0) :
    num m B (2 * w + 2) j = x := by
  rw [numW, h0, h1, Nat.mul_zero, Nat.add_zero]

end VG.Proof.Rsa.Arm.Recover
