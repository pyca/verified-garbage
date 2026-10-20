module

public import VerifiedGarbage.Proof.Rsa.X86.KeyArrs
import VerifiedGarbage.Proof.Rsa.KeyViews
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The key working space read with `w` and with `W = 2 w + 2` words

With `W` words, the stride is twice that with `w`, and array `j` is the
arrays `2 j` and `2 j + 1` with `w`. A step that changes some arrays read
one way changes the arrays that contain them read the other way
(`Keep.toW`, `Keep.ofW`), and the arrays it does not change keep their
values (`Arrs.keepOf`). A number of `W` words is the number of `w` words
in array `2 j`, when the rest of the two arrays is zero (`numW_of`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Impl.Rsa.X86.Keys VG.Proof.Rsa.X86.Keys

theorem S_W (w : Nat) : S (2 * w + 2) = 2 * S w :=
  VG.Proof.Rsa.KeyWorkspace.S_W w

theorem arr_W (w j : Nat) : arr (2 * w + 2) j = arr w (2 * j) :=
  VG.Proof.Rsa.KeyWorkspace.arr_W w j

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.Proof.Mont VG.Proof.Rsa.X86.Recover VG.Impl.Rsa.X86.Keys

/-- A step that keeps the arrays read with `w` but `js` keeps the arrays
read with `W` but those that contain them. -/
theorem Keep.toW {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem} (k : Keep B w js ds m m') :
    Keep B (2 * w + 2) (js.map (· / 2)) ds m m' :=
  VG.Proof.Rsa.KeyWorkspace.Keep.toW k

/-- A step that keeps the arrays read with `W` but `js` keeps the arrays
read with `w` but the two in each. -/
theorem Keep.ofW {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (k : Keep B (2 * w + 2) js ds m m') :
    Keep B w (js.flatMap fun j => [2 * j, 2 * j + 1]) ds m m' :=
  VG.Proof.Rsa.KeyWorkspace.Keep.ofW k

/-- The arrays a step does not change keep their values, given that they
fit in the address space. -/
theorem Arrs.keepOf {m m' : Mem} {B : Addr} {v : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B v A live) {js ds : List Nat} (k : Keep B v js ds m m')
    (hl : ∀ j ∈ live, ∀ i ∈ js, i ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (fit : ∀ j ∈ live, arr v j + S v ≤ 2 ^ 64) : Arrs m' B v A live :=
  VG.Proof.Rsa.KeyWorkspace.Arrs.keepOf h k hl hd fit

/-- The arrays after a step that writes `[o] := x` alone. -/
theorem Arrs.upd1 {m m' : Mem} {B : Addr} {v : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B v A live) {o x : Nat} {ds : List Nat} (k : Keep B v [o] ds m m')
    (hd : ∀ d ∈ ds, d + 4 ≤ hdr) (fit : ∀ j ∈ live, arr v j + S v ≤ 2 ^ 64)
    (e : num m' B v o = x) : Arrs m' B v (upd A o x) (o :: live) :=
  VG.Proof.Rsa.KeyWorkspace.Arrs.upd1 h k hd fit e

end VG.Proof.Rsa.X86.Keys

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Impl.Rsa.X86.Keys VG.Proof.Rsa.X86.Keys

/-- A number of `W` words: the `w + 2` words of array `2 j` and the `w`
words of array `2 j + 1`. -/
theorem numW (m : Mem) (B : Addr) (w j : Nat) :
    num m B (2 * w + 2) j = val32 m B (arr w (2 * j)) (w + 2) +
      2 ^ (32 * (w + 2)) * num m B w (2 * j + 1) :=
  VG.Proof.Rsa.KeyWorkspace.numW m B w j

theorem numW_of {m : Mem} {B : Addr} {w j x : Nat}
    (h0 : val32 m B (arr w (2 * j)) (w + 2) = x) (h1 : num m B w (2 * j + 1) = 0) :
    num m B (2 * w + 2) j = x :=
  VG.Proof.Rsa.KeyWorkspace.numW_of h0 h1

end VG.Proof.Rsa.X86.Recover
