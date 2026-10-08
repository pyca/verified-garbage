import VerifiedGarbage.TCB.Artifact

/-!
# Montgomery multiplication in the RSA working space, as a function

**Trusted** (as every file in `Spec/`). The contract of
`vg_rsa_mont_mul`, in the module `rsa_mont`, so that the code of the RSA
functions can call one copy of its Montgomery multiplication instead of
repeating it at every use. It is not an algorithm of a standard but the
arithmetic the RSA functions are built from: what it computes is stated on
integers.

The numbers live in a working space `ws` of `ws_len` 64-bit words, laid out
as the RSA functions lay out theirs: a header of 32 words, then 8 arrays of
`w + 2` words each. The header holds the count of words `w` of the numbers
(word 6), `-m⁻¹ mod 2⁶⁴` (word 7) and the addresses of the 8 arrays (words
8 to 15), which must be where the layout puts them (`Layout`). Array 0 holds
the modulus `m`, odd; arrays 2 and 3 are the function's own (its accumulator
and a temporary); the operands and the result are arrays given by their
indices `o`, `a` and `b`, each a number of `w` words, little-endian, at the
start of its array (`numAt`). The result may be either operand (`o = a` or
`o = b`), and the operands may be the same array (a square).

On return the function's own arrays are unspecified and may hold
intermediate values; every other byte of `ws` keeps its value but the
result's array (`Keeps`). Everything is secret but the pointer, `ws_len`,
the indices and `w`, which are public: `w` is the length of the numbers,
and timing may depend on it (`leak`). The function is otherwise constant
time.
-/

namespace VG.Spec.Rsa.Mont

/-- The bytes of the header. -/
def hdrBytes : Nat := 256

/-- The header word of `w`, and of `-m⁻¹ mod 2⁶⁴`. -/
def wWord : Nat := 6
def minvWord : Nat := 7

/-- The header word of the address of array `j`. -/
def arrWord (j : Nat) : Nat := 8 + j

/-- The byte offset of array `j` in the working space, for numbers of `w`
words. -/
def arrAt (w j : Nat) : Nat := hdrBytes + j * (8 * (w + 2))

/-- The arrays of the modulus, and of the function's own values. -/
def aM : Nat := 0
def aAcc : Nat := 2
def aTmp : Nat := 3

/-- The 64-bit word `i` of the working space `ws`. -/
def wordAt (m : Mem) (ws : Addr) (i : Nat) : BitVec 64 := m.readW (ws + BitVec.ofNat 64 (8 * i)) 64

/-- `w`, from the header. -/
def wOf (m : Mem) (ws : Addr) : Nat := (wordAt m ws wWord).toNat

/-- The number of `w` 64-bit words, little-endian, at the start of array `j`. -/
def numAt (m : Mem) (ws : Addr) (w j : Nat) : Nat :=
  (m.read (ws + BitVec.ofNat 64 (arrAt w j)) (8 * w)).toNat

/-- The header and the size of the working space: `w` is at least 2 and
below `2^31`, the 8 arrays fit in `ws_len` words, and the header gives each
array's address. -/
def Layout (m : Mem) (ws : Addr) (wsLen : Nat) : Prop :=
  let w := wOf m ws
  2 ≤ w ∧ w < 2 ^ 31 ∧ arrAt w 8 ≤ 8 * wsLen ∧
    ∀ j < 8, wordAt m ws (arrWord j) = ws + BitVec.ofNat 64 (arrAt w j)

/-- An index of an operand or the result: one of the 8 arrays, not the
function's own. -/
def Operand (j : Nat) : Prop := j < 8 ∧ j ≠ aAcc ∧ j ≠ aTmp

/-- Every byte of `ws` but those of the function's own arrays and of the
result's keeps its value. -/
def Keeps (ws : Addr) (wsLen w o : Nat) (m m' : Mem) : Prop :=
  ∀ i < 8 * wsLen, (∀ j ∈ [aAcc, aTmp, o], i < arrAt w j ∨ arrAt w j + 8 * (w + 2) ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut u64, ws_len: usize, o: u32, a: u32, b: u32`, the indices public. -/
def sig : Sig where
  params := [("ws", .slice true .u64 "ws_len"), ("o", .int .u32 true), ("a", .int .u32 true),
    ("b", .int .u32 true)]

/-- For `-m⁻¹ mod 2⁶⁴` in the header (the inverse of the low word of `m`,
negated: so `m` is odd) and `b` below `m`: the number at `o` is
below `m` and congruent to `a b R⁻¹` modulo `m`, `R = 2^(64 w)`, that is,
its product with `R` is congruent to `a b`. -/
def mulContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws wsLen o a b m =>
      let w := wOf m ws
      Layout m ws wsLen.toNat ∧ Operand o.toNat ∧ Operand a.toNat ∧ Operand b.toNat ∧
        ((m.readW (ws + BitVec.ofNat 64 (arrAt w aM)) 64).toNat * (wordAt m ws minvWord).toNat + 1) %
          2 ^ 64 = 0 ∧
        numAt m ws w b.toNat < numAt m ws w aM)
    (post := fun ws wsLen o a b m m' _ =>
      let w := wOf m ws
      let M := numAt m ws w aM
      numAt m' ws w o.toNat < M ∧
        numAt m' ws w o.toNat * 2 ^ (64 * w) % M = numAt m ws w a.toNat * numAt m ws w b.toNat % M ∧
        Keeps ws wsLen.toNat w o.toNat m m')
    (stack := stack)
    (leak := some fun ws _ _ _ _ m => [wOf m ws])

/-- `vg_rsa_mont_mul` on every target. -/
def mulApi : Api where
  module := "rsa_mont"
  name := "vg_rsa_mont_mul"
  sig := sig
  contracts := some fun A stack => mulContract A stack
  summary := "Montgomery multiplication in the working space of the RSA functions: writes to \
    array `o` the number below the modulus `m` (array 0) congruent to `a b 2^(-64 w)` modulo \
    `m`, for the numbers in arrays `a` and `b`. The working space is a header of 32 words, \
    then 8 arrays of `w + 2` words each: header word 6 holds `w`, word 7 `-m⁻¹ mod 2^64`, and \
    words 8 to 15 the addresses of the arrays. The numbers are `w` 64-bit words, \
    little-endian, at the start of their arrays; `o` may be `a` or `b`, and `a` may be `b`. \
    Every byte of `ws` but those of arrays 2 and 3 (the function's own) and of array `o` \
    keeps its value.\n\n\
    Contract: `VG.Spec.Rsa.Mont.mulContract`. Constant time but for `w`: timing may depend \
    on the pointer, `ws_len`, the indices and `w`, not on the numbers."
  safety := ["Header word 6 of `ws`, `w`, must be in 2..2^31, and `ws_len` at least \
      `32 + 8 * (w + 2)`.",
    "Header words 8 to 15 must hold the addresses of the arrays: word `8 + j` the address of \
      word `32 + j * (w + 2)` of `ws`.",
    "Header word 7 must be `-m⁻¹ mod 2^64` for the modulus `m` in array 0, which must be odd.",
    "`o`, `a` and `b` must be below 8, and not 2 or 3.",
    "The number in array `b` must be below `m`.",
    "Arrays 2 and 3 are unspecified on return and may hold intermediate values, which the \
      caller must destroy if they are secret."]

end VG.Spec.Rsa.Mont
