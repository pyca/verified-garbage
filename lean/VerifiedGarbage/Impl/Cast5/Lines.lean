/-!
# CAST5 key schedule: the lines of RFC 2144 §2.4, as data

Every line of §2.4 XORs `S5[a] ^ S6[b] ^ S7[c] ^ S8[d]` (its *main* bytes)
with one more S-box value, `Sₑ[f]` (its *extra* byte), and, for the lines
computing `z` or `x`, with a quadruple of the other array. The lines come in
groups of four (`zLines`, `aLines`, …) whose extra S-boxes are S5–S8, one
each, so the implementations make a group's four extra lookups at once.
-/

namespace VG.Impl.Cast5

/-- The arrays of the key schedule: `x0 … xF` and `z0 … zF`. -/
inductive Arr | x | z
  deriving DecidableEq, Repr, Inhabited

/-- A byte of `x` or `z`. -/
abbrev Pos := Arr × Nat

/-- A line of §2.4: the main bytes for S5–S8, the extra S-box (5–8) and byte,
and the quadruple XORed in, if any. -/
structure Line where
  main : Pos × Pos × Pos × Pos
  extra : Nat × Pos
  word : Option (Arr × Nat)
  deriving Inhabited

def x (i : Nat) : Pos := (.x, i)
def z (i : Nat) : Pos := (.z, i)

/-- `zOfX`: the four lines computing `z` from `x`, quadruple `k` from line `k`. -/
def zLines : List Line := [
  ⟨(x 0xD, x 0xF, x 0xC, x 0xE), (7, x 0x8), some (.x, 0)⟩,
  ⟨(z 0x0, z 0x2, z 0x1, z 0x3), (8, x 0xA), some (.x, 2)⟩,
  ⟨(z 0x7, z 0x6, z 0x5, z 0x4), (5, x 0x9), some (.x, 3)⟩,
  ⟨(z 0xA, z 0x9, z 0xB, z 0x8), (6, x 0xB), some (.x, 1)⟩]

/-- `xOfZ`: the four lines computing `x` from `z`. -/
def xLines : List Line := [
  ⟨(z 0x5, z 0x7, z 0x4, z 0x6), (7, z 0x0), some (.z, 2)⟩,
  ⟨(x 0x0, x 0x2, x 0x1, x 0x3), (8, z 0x2), some (.z, 0)⟩,
  ⟨(x 0x7, x 0x6, x 0x5, x 0x4), (5, z 0x1), some (.z, 1)⟩,
  ⟨(x 0xA, x 0x9, x 0xB, x 0x8), (6, z 0x3), some (.z, 3)⟩]

/-- `keysA` (from `z`). -/
def aLines : List Line := [
  ⟨(z 0x8, z 0x9, z 0x7, z 0x6), (5, z 0x2), none⟩,
  ⟨(z 0xA, z 0xB, z 0x5, z 0x4), (6, z 0x6), none⟩,
  ⟨(z 0xC, z 0xD, z 0x3, z 0x2), (7, z 0x9), none⟩,
  ⟨(z 0xE, z 0xF, z 0x1, z 0x0), (8, z 0xC), none⟩]

/-- `keysB` (from `x`). -/
def bLines : List Line := [
  ⟨(x 0x3, x 0x2, x 0xC, x 0xD), (5, x 0x8), none⟩,
  ⟨(x 0x1, x 0x0, x 0xE, x 0xF), (6, x 0xD), none⟩,
  ⟨(x 0x7, x 0x6, x 0x8, x 0x9), (7, x 0x3), none⟩,
  ⟨(x 0x5, x 0x4, x 0xA, x 0xB), (8, x 0x7), none⟩]

/-- `keysC` (from `z`). -/
def cLines : List Line := [
  ⟨(z 0x3, z 0x2, z 0xC, z 0xD), (5, z 0x9), none⟩,
  ⟨(z 0x1, z 0x0, z 0xE, z 0xF), (6, z 0xC), none⟩,
  ⟨(z 0x7, z 0x6, z 0x8, z 0x9), (7, z 0x2), none⟩,
  ⟨(z 0x5, z 0x4, z 0xA, z 0xB), (8, z 0x6), none⟩]

/-- `keysD` (from `x`). -/
def dLines : List Line := [
  ⟨(x 0x8, x 0x9, x 0x7, x 0x6), (5, x 0x3), none⟩,
  ⟨(x 0xA, x 0xB, x 0x5, x 0x4), (6, x 0x7), none⟩,
  ⟨(x 0xC, x 0xD, x 0x3, x 0x2), (7, x 0x8), none⟩,
  ⟨(x 0xE, x 0xF, x 0x1, x 0x0), (8, x 0xD), none⟩]

/-- Where the implementations keep `x` and `z` in their working space. -/
def xOff : Nat := 16
def zOff : Nat := 32

/-- The offset of an array in the working space. -/
def off : Arr → Nat
  | .x => xOff
  | .z => zOff

/-- The address offset of a byte of `x` or `z`. -/
def srcOff (s : Pos) : Nat := off s.1 + s.2

/-- The extra byte of the group's line whose extra S-box is `e`. -/
def extraOf (ls : List Line) (e : Nat) : Pos :=
  ((ls.find? (·.extra.1 = e)).map (·.extra.2)).getD (.x, 0)

end VG.Impl.Cast5
