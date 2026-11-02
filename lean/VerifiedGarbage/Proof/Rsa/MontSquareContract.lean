module

public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Fixed-slot Montgomery squares in the RSA working space

Not trusted: the contracts of internal functions (`Rust.Internal`), which only
verified code calls, that their proofs and their callers' compose.

Two callable specializations of RSA's Montgomery arithmetic:
the square of array 4 (R² during setup), and of array 6 (the exponentiation
accumulator). These use the existing layout and integer relation from
`Proof/Rsa/MontContract.lean`. Fixing the array in the function's identity lets callers
share the code without passing operand indices at each square.
-/

@[expose] public section

namespace VG.Proof.Rsa.MontSquare

open VG.Proof.Rsa.Mont

/-- The two in-place squares shared by RSA setup and exponentiation. -/
inductive Slot where
  | r2
  | y

/-- Array indices in the existing RSA working-space layout. -/
def Slot.index : Slot → Nat
  | .r2 => 4
  | .y => 6

/-- The working space, in 64-bit words; its address and length are public. -/
def sig : Sig where
  params := [("ws", .slice true .u64 "ws_len")]

/-- Square the designated array in place modulo array 0, in Montgomery
form. Only that array and the existing accumulator/temporary may change.
The width is public; all arithmetic values, including the modulus, remain
secret. Bounds and the final canonical result match `Mont.mulContract`. -/
def squareContract {I : ISA} (slot : Slot) (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws wsLen m =>
      let w := wOf m ws
      Layout m ws wsLen.toNat ∧
        ((m.readW (ws + BitVec.ofNat 64 (arrAt w aM)) 64).toNat *
          (wordAt m ws minvWord).toNat + 1) % 2 ^ 64 = 0 ∧
        numAt m ws w slot.index < numAt m ws w aM)
    (post := fun ws wsLen m m' _ =>
      let w := wOf m ws
      let M := numAt m ws w aM
      numAt m' ws w slot.index < M ∧
        numAt m' ws w slot.index * 2 ^ (64 * w) % M =
          numAt m ws w slot.index * numAt m ws w slot.index % M ∧
        Keeps ws wsLen.toNat w slot.index m m')
    (stack := stack)
    (leak := some fun ws _ m => [wOf m ws])

end VG.Proof.Rsa.MontSquare
