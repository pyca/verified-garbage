module

public import VerifiedGarbage.Spec.Rsa.Mont

/-!
# A shared five-bit Montgomery exponentiation window

**Trusted.** An internal RSA helper that squares the accumulator five times
and multiplies by a secretly selected entry of a 32-entry table. The contract
states its integer relation without requiring that the table contain powers
of a particular base. Table construction and the exponent's interpretation
remain obligations of the caller.
-/

@[expose] public section
namespace VG.Spec.Rsa.MontWindow
open VG.Spec.Rsa.Mont

/-- The fixed accumulator and selected-table-entry arrays. -/
def aY : Nat := 6
def aT : Nat := 5

/-- Header words in a CRT prime's workspace. -/
def pendingWord : Nat := 20
def tableWord : Nat := 25
def entryWord : Nat := 26
def digitWord : Nat := 27
def indexWord : Nat := 28

/-- The secret five-bit digit supplied by the caller. -/
def digit (m : Mem) (ws : Addr) : Nat := (wordAt m ws digitWord).toNat

/-- A standard Montgomery workspace followed by 32 table entries, each
occupying `w + 2` words. Only each entry's first `w` words hold its value. -/
def WindowLayout (m : Mem) (ws : Addr) (wsLen : Nat) : Prop :=
  let w := wOf m ws
  Layout m ws wsLen ∧ w < 2 ^ 30 ∧ arrAt w 40 ≤ 8 * wsLen ∧
    wordAt m ws tableWord = ws + BitVec.ofNat 64 (arrAt w 8)

/-- Only the accumulator, multiplication scratch, selected entry and four
window-control header words may change. In particular, the packed exponent
word, modulus, table pointer, and all 32 table entries are preserved. -/
def Keeps (ws : Addr) (wsLen w : Nat) (m m' : Mem) : Prop :=
  ∀ i < 8 * wsLen,
    (∀ j ∈ [aAcc, aTmp, aT, aY], i < arrAt w j ∨ arrAt w j + 8 * (w + 2) ≤ i) →
    (∀ j ∈ [pendingWord, entryWord, digitWord, indexWord], i < 8 * j ∨ 8 * j + 8 ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- The working-space address and length are public. Its contents, including
the modulus, accumulator, table and selected digit, remain secret. -/
def sig : Sig where
  params := [("ws", .slice true .u64 "ws_len")]

/-- For `R = 2^(64 w)`, the new canonical accumulator `Y'` satisfies
`Y' R^32 ≡ Y^32 T[d] (mod M)`. Five Montgomery squares contribute `R^31`
to the denominator, and the final product contributes one more `R`.
The digit and pending-bit counter are reset to zero for the next window. -/
def windowContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws wsLen m =>
      let w := wOf m ws
      let M := numAt m ws w aM
      WindowLayout m ws wsLen.toNat ∧
        ((m.readW (ws + BitVec.ofNat 64 (arrAt w aM)) 64).toNat *
          (wordAt m ws minvWord).toNat + 1) % 2 ^ 64 = 0 ∧
        numAt m ws w aY < M ∧ digit m ws < 32 ∧
        ∀ j < 32, numAt m ws w (8 + j) < M)
    (post := fun ws wsLen m m' _ =>
      let w := wOf m ws
      let M := numAt m ws w aM
      let R := 2 ^ (64 * w)
      numAt m' ws w aY < M ∧
        numAt m' ws w aY * R ^ 32 % M =
          numAt m ws w aY ^ 32 * numAt m ws w (8 + digit m ws) % M ∧
        wordAt m' ws pendingWord = 0 ∧ wordAt m' ws digitWord = 0 ∧
        Keeps ws wsLen.toNat w m m')
    (stack := stack)
    (leak := some fun ws _ m => [wOf m ws])

/-- A five-bit window with the same contract on every target. -/
def windowApi : Api where
  module := "rsa"
  name := "vg_rsa_square_window5"
  sig := sig
  contracts := some fun A stack => windowContract A stack
  summary := "Performs five Montgomery squares of accumulator array 6, then multiplies \
    it by entry `d` of the 32-entry table following the eight workspace arrays. For \
    `R = 2^(64 w)`, the canonical result `Y'` satisfies `Y' R^32 = Y^32 T[d] (mod M)`. \
    Header word 27 holds the secret digit `d`. Header words 20 and 27 are reset to zero. \
    Arrays 2, 3, 5 and 6, and header words 20, 26, 27 and 28 may change; all other \
    workspace bytes, including the entire table and packed exponent, are preserved.\n\n\
    Contract: `VG.Spec.Rsa.MontWindow.windowContract`. Constant time except for \
    the public workspace address, its length and limb count `w`; the modulus, \
    accumulator, selected digit and table contents remain secret."
  safety := ["Header word 6, `w`, must be in 2..2^30, and `ws_len` at least `32 + 40 * (w + 2)`.",
    "Header word `8 + j` must point to word `32 + j * (w + 2)` of `ws`, for every `j < 8`.",
    "Header word 25 must point to word `32 + 8 * (w + 2)`, the first of 32 table entries of `w + 2` words each.",
    "Header word 7 must be `-M⁻¹ mod 2^64` for the odd modulus `M` in array 0.",
    "The accumulator in array 6 and the first `w` words of every table entry must be below `M`.",
    "Header word 27, the secret selected digit, must be below 32.",
    "Arrays 2, 3 and 5 and control words 26 and 28 may contain intermediate values on return; the caller must destroy secret intermediates."]

end VG.Spec.Rsa.MontWindow
