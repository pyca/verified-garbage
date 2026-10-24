module

/-! Public signed recoding for five-bit and eight-bit Ed448 verification windows.
The original scalar is retained in full; no group-order reduction occurs here. -/

@[expose] public section

namespace VG.Impl.Ed448.WnafWide

/-- The full 57-byte scalar input range, including unreduced challenges. -/
def pow2 (n : Nat) : Nat := 2 ^ n

def scalarLimit : Nat := pow2 456

/-- Five-bit public-key digits, or eight-bit fixed-base digits. -/
def half (wide : Bool) : Nat := if wide then 128 else 16

def radix (wide : Bool) : Nat := 2 * half wide

def digit (wide : Bool) (k : Nat) : Int :=
  if k % 2 = 0 then 0
  else if k % radix wide < half wide then (k % radix wide : Nat)
  else (k % radix wide : Nat) - radix wide

def next (wide : Bool) (k : Nat) : Nat :=
  if k % 2 = 0 then k / 2 else (k + half wide) / radix wide * half wide

def residual (wide : Bool) (k : Nat) : Nat → Nat
  | 0 => k
  | n + 1 => next wide (residual wide k n)

def digitAt (wide : Bool) (k n : Nat) : Int := digit wide (residual wide k n)

def localDigit (wide : Bool) (bits carry : Nat) : Int :=
  digit wide ((bits + carry + half wide) % radix wide)

def carryNext (wide : Bool) (bits carry : Nat) : Nat :=
  (((bits % 2 : Nat) : Int) + carry + half wide - localDigit wide bits carry).toNat / 2

end VG.Impl.Ed448.WnafWide
