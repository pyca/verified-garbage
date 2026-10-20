module

public import VerifiedGarbage.Proof.Rsa.KeyArrays

/-! # The key working space read with `w` and with `W = 2 w + 2` words

With `W` words, the stride is twice that with `w`, and array `j` is the
arrays `2 j` and `2 j + 1` with `w`. A step that changes some arrays read
one way changes the arrays that contain them read the other way
(`Keep.toW`, `Keep.ofW`), and the arrays it does not change keep their
values (`Arrs.keepOf`). A number of `W` words is the number of `w` words
in array `2 j`, when the rest of the two arrays is zero (`numW_of`).
-/

@[expose] public section

namespace VG.Proof.Rsa.KeyWorkspace
open VG VG.Proof.Mont

theorem S_W (w : Nat) : S (2 * w + 2) = 2 * S w := by simp only [S]; omega

theorem arr_W (w j : Nat) : arr (2 * w + 2) j = arr w (2 * j) := by
  simp only [arr, S]; rw [Nat.mul_comm 2 j, Nat.mul_assoc]; congr 2; omega

end VG.Proof.Rsa.KeyWorkspace

namespace VG.Proof.Rsa.KeyWorkspace
open VG VG.Proof.Mont

/-- A step that keeps the arrays read with `w` but `js` keeps the arrays
read with `W` but those that contain them. -/
theorem Keep.toW {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem} (k : Keep B w js ds m m') :
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
theorem Keep.ofW {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
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
theorem Arrs.keepOf {m m' : Mem} {B : Addr} {v : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B v A live) {js ds : List Nat} (k : Keep B v js ds m m')
    (hl : ∀ j ∈ live, ∀ i ∈ js, i ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (fit : ∀ j ∈ live, arr v j + S v ≤ 2 ^ 64) : Arrs m' B v A live := by
  intro j hj
  rw [k.num (hl j hj) hd (fit j hj)]
  exact h j hj

end VG.Proof.Rsa.KeyWorkspace

namespace VG.Proof.Rsa.KeyWorkspace
open VG VG.Proof.Mont

/-- A number of `W` words: the `w + 2` words of array `2 j` and the `w`
words of array `2 j + 1`. -/
theorem numW (m : Mem) (B : Addr) (w j : Nat) :
    num m B (2 * w + 2) j = val32 m B (arr w (2 * j)) (w + 2) +
      2 ^ (32 * (w + 2)) * num m B w (2 * j + 1) := by
  simp only [num]
  rw [arr_W, show 2 * w + 2 = (w + 2) + w by omega, val32_append, arr_succ]

theorem numW_of {m : Mem} {B : Addr} {w j x : Nat}
    (h0 : val32 m B (arr w (2 * j)) (w + 2) = x) (h1 : num m B w (2 * j + 1) = 0) :
    num m B (2 * w + 2) j = x := by
  rw [numW, h0, h1, Nat.mul_zero, Nat.add_zero]

/-- The arrays after a step that writes `[o] := x` alone. -/
theorem Arrs.upd1 {m m' : Mem} {B : Addr} {v : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B v A live) {o x : Nat} {ds : List Nat} (k : Keep B v [o] ds m m')
    (hd : ∀ d ∈ ds, d + 4 ≤ hdr) (fit : ∀ j ∈ live, arr v j + S v ≤ 2 ^ 64)
    (e : num m' B v o = x) : Arrs m' B v (upd A o x) (o :: live) := by
  intro j hj
  by_cases hjo : j = o
  · subst hjo; rw [upd_self]; exact e
  · have hj' : j ∈ live := (List.mem_cons.mp hj).resolve_left hjo
    rw [upd_ne _ _ hjo, k.num (fun i hi ei => hjo (by simp at hi; subst hi; exact ei.symm)) hd (fit j hj')]
    exact h j hj'

end VG.Proof.Rsa.KeyWorkspace
