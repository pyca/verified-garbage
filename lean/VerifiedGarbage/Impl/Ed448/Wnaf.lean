module


/-! Public width-five non-adjacent recoding. The integer is used in full,
without reduction modulo the group order. -/

@[expose] public section

namespace VG.Impl.Ed448.Wnaf

/-- Signed odd digit in `[-15, 15]`, or zero for an even residual. -/
def digit (k : Nat) : Int :=
  if k % 2 = 0 then 0 else if k % 32 < 16 then (k % 32 : Nat) else (k % 32 : Nat) - 32

/-- Residual after removing the low digit and dividing by two. -/
def next (k : Nat) : Nat :=
  if k % 2 = 0 then k / 2 else (k + 16) / 32 * 16

def residual (k : Nat) : Nat → Nat
  | 0 => k
  | n + 1 => next (residual k n)

def digitAt (k n : Nat) : Int := digit (residual k n)

/-- Carry is biased by 16 so the implementation keeps it nonnegative. -/
def localDigit (bits carry : Nat) : Int := digit ((bits + carry + 16) % 32)

def carryNext (bits carry : Nat) : Nat :=
  (((bits % 2 : Nat) : Int) + carry + 16 - localDigit bits carry).toNat / 2

end VG.Impl.Ed448.Wnaf
