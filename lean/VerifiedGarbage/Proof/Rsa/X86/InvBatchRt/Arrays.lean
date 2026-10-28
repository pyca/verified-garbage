module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Ops
import VerifiedGarbage.Proof.Framework.Omega

/-! # Where the arrays are

The offsets of `Ref`s in terms of the primes' words `n`, for the proofs that place them by `omega`;
and what the inverse's statement needs (`virtualMod`, `bodyWrites`), for callers that state it
without its proof (`BatchLaw`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt VG.Proof.Rsa.X86.KeyRt

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem rv_arr (w j b : Nat) : rv w { arr := j, byte := b } = 160 + j * (4 * w + 8) + b := by
  simp only [rv, VG.Impl.Rsa.X86.InvBatchRt.offset]; omega

theorem rv_half1 (w : Nat) (x : Ref) (hx : x.half = 0) : rv w { x with half := 1 } = rv w x + 2 * w := by
  simp only [rv, hx]; omega

theorem rv_byte (w : Nat) (x : Ref) (d : Nat) : rv w { x with byte := x.byte + d } = rv w x + d := by
  simp only [rv]; omega

theorem rv_a (len j : Nat) : rv (kw len) (a j) = 160 + j * (8 * nw len + 8) := by
  have := rv_arr (kw len) j 0
  have ke := kw_eq len
  rw [show 4 * kw len + 8 = 8 * nw len + 8 by omega] at this
  simp only [a]; omega

theorem rv_half1' (len j : Nat) : rv (kw len) { arr := j, half := 1 } = rv (kw len) (a j) + 4 * nw len := by
  have := rv_half1 (kw len) (a j) rfl
  have ke := kw_eq len
  simp only [a] at this ⊢; omega

/-- The arrays fit: `[16]` begins inside the working space. -/
theorem Bx.fits16 {s : State} (h : Bx L s B Z len N) : 160 + 16 * (8 * nw len + 8) ≤ Z := by
  have := h.fits
  have ke := kw_eq len
  simp only [VG.Impl.Rsa.X86.InvBatchRt.offset] at this
  omega

/-- `1` replaced by `3`, an odd modulus the batches can run on. -/
def virtualMod (m : Nat) : Nat := if m = 1 then 3 else m

/-- What the inverse writes: the header from the window on, arrays 0 to 7 and 11 to 14. -/
def bodyWrites (len : Nat) : List (Nat × Nat) :=
  [(win, 88), (rv (kw len) (a 0), 8 * (8 * nw len + 8)), (rv (kw len) (a 11), 4 * (8 * nw len + 8))]

end VG.Proof.Rsa.X86.InvBatchRt
