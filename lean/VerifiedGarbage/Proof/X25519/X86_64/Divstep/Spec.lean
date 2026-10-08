import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Divstep.PackedDef
import VerifiedGarbage.Impl.X25519.X86_64

/-!
# X25519 on x86-64, inversion by divsteps: what the code computes

The numbers `Impl/X25519/X86_64.lean`'s `invertDS` computes, exactly as it
computes them, for any words (`byAlg`): a batch (`dbatchV`) runs 59 packed
divsteps in four chunks (`pkBatchV`, each chunk `pkChunkV`: `Divstep.psteps`
on the rows, the matrix from them, the low words updated and the batch's
matrix multiplied) on the low words of `f` and `g`, then the rows `fRowV`
and `aRowV`. Every operation is on natural numbers or integers; the
proofs of the code show it computes these, and need no bounds.

That `byAlg x` is `x^(p-2)` is the theory of divsteps (bounds on the matrix,
`f` and `g`, and the number of steps), which needs Mathlib's algebra: the
code's callers take it as `DivstepInv`, an instance of which only the
registration files import (`Divstep/Sound.lean`).
-/

namespace VG.Proof.X25519.X86_64

open VG.Spec.X25519 VG.Proof.X25519

/-- `|m|`, for a word as a signed number. -/
def absN (m : BitVec 64) : Nat := m.toInt.natAbs

/-- `X ^ s` for the mask `s` of `m`'s sign: `X`, or `2²⁵⁶ - 1 - X` if `m < 0`. -/
def flipN (m : BitVec 64) (X : Nat) : Nat := if m.msb then 2 ^ 256 - 1 - X else X

/-- `|m|` if `m < 0`. -/
def negN (m : BitVec 64) : Nat := if m.msb then absN m else 0

/-- `|m|` if `X ^ s` is negative (as four words in two's complement). -/
def topN (m : BitVec 64) (X : Nat) : Nat := if 2 ^ 255 ≤ flipN m X then absN m else 0

/-- `|m₁| [m₁ < 0] + |m₂| [m₂ < 0]`, as the word `rbx` holds it. -/
def cN (m₁ m₂ : BitVec 64) : Nat := (negN m₁ + negN m₂) % 2 ^ 64

/-- A row of `f` and `g`: `(m₁ f + m₂ g) / 2⁵⁹` in four words, as the code
computes it for words `m₁`, `m₂` and four-word `X`, `Y`: the sum of the
products, less `2²⁵⁶` times the corrections of the tops (plus `2³²¹`, which
the shift and the four words drop). -/
def fRowV (m₁ m₂ : BitVec 64) (X Y : Nat) : Nat :=
  (absN m₁ * flipN m₁ X + absN m₂ * flipN m₂ Y + cN m₁ m₂ + (2 ^ 256 * 2 ^ 65 - 2 ^ 256 * (topN m₁ X + topN m₂ Y)))
    / 2 ^ 59 % 2 ^ 256

/-- `lo + 38 Q₄ - 37 c` for the five-word `Q`, below `2²⁵⁶`: its carry
folded in as `±38`. With `R = lo + 38 Q₄ + 2²⁵⁶ - 37 c` (`c < 2⁶⁴`): `R - 38`
if it is below `2²⁵⁶`, `R - 2²⁵⁶` if below `2²⁵⁷`, else `R - 2²⁵⁷ + 38`. -/
def foldV (Q c : Nat) : Nat :=
  let R := Q % 2 ^ 256 + 38 * (Q / 2 ^ 256) + 2 ^ 256 - 37 * c
  if R < 2 ^ 256 then R - 38 else if R < 2 ^ 257 then R - 2 ^ 256 else R - 2 ^ 257 + 38

/-- A row of `a` and `b`: `m₁ a + m₂ b` modulo `p`, below `2²⁵⁶`, as the code
computes it. -/
def aRowV (m₁ m₂ : BitVec 64) (A B : Nat) : Nat :=
  foldV (absN m₁ * flipN m₁ A + absN m₂ * flipN m₂ B) (cN m₁ m₂)

/-- The inversion's state between batches: `d`, and the four-word numbers
`f`, `g`, `a`, `b`. -/
structure DSt where
  D : BitVec 64
  f : Nat
  g : Nat
  a : Nat
  b : Nat

/-- The words of a batch's packed divsteps between chunks: `~d`, the low
words of `f` and `g`, and the batch's matrix so far. -/
structure PkSt where
  E : BitVec 64
  F : BitVec 64
  G : BitVec 64
  U : BitVec 64
  V : BitVec 64
  Q : BitVec 64
  R : BitVec 64

/-- A chunk of `n` packed steps (`pkChunk`): the rows from the low 15 bits of
`F` and `G`, their steps, the chunk's matrix from them, the low words by it
(but after the last chunk), and the batch's matrix times it (or it, for the
first). -/
def pkChunkV (n : Nat) (first last : Bool) (w : PkSt) : PkSt :=
  let r := Divstep.psteps n (w.E, (w.F &&& 0x7fff) + 2 ^ 31, (w.G &&& 0x7fff) + 2 ^ 47)
  let u := Divstep.pextLo r.2.1
  let v := Divstep.pextHi r.2.1
  let q := Divstep.pextLo r.2.2
  let rr := Divstep.pextHi r.2.2
  let F := if last then w.F else (w.G * v + w.F * u) >>> n
  let G := if last then w.G else (w.G * rr + w.F * q) >>> n
  if first then ⟨r.1, F, G, u, v, q, rr⟩
  else ⟨r.1, F, G, u * w.U + v * w.Q, u * w.V + v * w.R, rr * w.Q + q * w.U, rr * w.R + q * w.V⟩

/-- A batch's 59 packed divsteps from `d` and the low words `F`, `G`: chunks
of `15, 15, 15, 14`. -/
def pkBatchV (D F G : BitVec 64) : PkSt :=
  pkChunkV 14 false true <| pkChunkV 15 false false <| pkChunkV 15 false false <|
    pkChunkV 15 true false ⟨~~~D, F, G, 0, 0, 0, 0⟩

/-- A batch: 59 divsteps on the low words, then the rows. -/
def dbatchV (t : DSt) : DSt :=
  let w := pkBatchV t.D (BitVec.ofNat 64 t.f) (BitVec.ofNat 64 t.g)
  ⟨~~~w.E, fRowV w.U w.V t.f t.g, fRowV w.Q w.R t.f t.g, aRowV w.U w.V t.a t.b, aRowV w.Q w.R t.a t.b⟩

/-- `n` batches from `(d, f, g, a, b) = (1, p, x, 0, 1)`. -/
def drun (x : Nat) : Nat → DSt
  | 0 => ⟨1, P, x, 0, 1⟩
  | n + 1 => dbatchV (drun x n)

/-- `2⁻⁵⁹⁰`, or `p - 2⁻⁵⁹⁰` if `f < 0`. -/
def kSel (f : Nat) : Nat := if f < 2 ^ 255 then Impl.X25519.X86_64.kInv else Impl.X25519.X86_64.kInvNeg

/-- What the inversion computes from `x`. -/
def byAlg (x : Fe) : Fe := toFe (drun x.val 10).a * toFe (kSel (drun x.val 10).f)

/-- The inversion by divsteps is `x^(p-2)`: the theory of divsteps,
`Divstep/Sound.lean`. -/
class DivstepInv : Prop where
  eq : ∀ x : Fe, byAlg x = pow x (P - 2)

end VG.Proof.X25519.X86_64
