module
public import VerifiedGarbage.Proof.Rsa.Arm.KeyArrs

import VerifiedGarbage.Proof.Rsa.KeyViews
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Impl.Rsa.Arm.Recover
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import VerifiedGarbage.TCB.Arm.Isa

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

theorem S_W (w : Nat) : S (2 * w + 2) = 2 * S w :=
  VG.Proof.Rsa.KeyWorkspace.S_W w

theorem arr_W (w j : Nat) : arr (2 * w + 2) j = arr w (2 * j) :=
  VG.Proof.Rsa.KeyWorkspace.arr_W w j

end VG.Proof.Rsa.Arm.Recover

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Recover VG.Impl.Rsa.Arm.Keys

/-- A step that keeps the arrays read with `w` but `js` keeps the arrays
read with `W` but those that contain them. -/
theorem Keep.toW {B : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem} (k : Keep B w js ds m m') :
    Keep B (2 * w + 2) (js.map (· / 2)) ds m m' :=
  VG.Proof.Rsa.KeyWorkspace.Keep.toW k

/-- A step that keeps the arrays read with `W` but `js` keeps the arrays
read with `w` but the two in each. -/
theorem Keep.ofW {B : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (k : Keep B (2 * w + 2) js ds m m') :
    Keep B w (js.flatMap fun j => [2 * j, 2 * j + 1]) ds m m' :=
  VG.Proof.Rsa.KeyWorkspace.Keep.ofW k

/-- The arrays a step does not change keep their values, given that they
fit in the address space. -/
theorem Arrs.keepOf {m m' : Mem} {B : BitVec 32} {v : Nat} {A : Nat → Nat} {live : List Nat}
    (h : Arrs m B v A live) {js ds : List Nat} (k : Keep B v js ds m m')
    (hl : ∀ j ∈ live, ∀ i ∈ js, i ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (fit : ∀ j ∈ live, arr v j + S v ≤ 2 ^ 64) : Arrs m' B v A live :=
  VG.Proof.Rsa.KeyWorkspace.Arrs.keepOf h k hl hd fit

end VG.Proof.Rsa.Arm.Keys

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys

/-- A number of `W` words: the `w + 2` words of array `2 j` and the `w`
words of array `2 j + 1`. -/
theorem numW (m : Mem) (B : BitVec 32) (w j : Nat) :
    num m B (2 * w + 2) j = val32 m (State.addr B) (arr w (2 * j)) (w + 2) +
      2 ^ (32 * (w + 2)) * num m B w (2 * j + 1) :=
  VG.Proof.Rsa.KeyWorkspace.numW m (State.addr B) w j

theorem numW_of {m : Mem} {B : BitVec 32} {w j x : Nat}
    (h0 : val32 m (State.addr B) (arr w (2 * j)) (w + 2) = x) (h1 : num m B w (2 * j + 1) = 0) :
    num m B (2 * w + 2) j = x :=
  VG.Proof.Rsa.KeyWorkspace.numW_of h0 h1

end VG.Proof.Rsa.Arm.Recover
