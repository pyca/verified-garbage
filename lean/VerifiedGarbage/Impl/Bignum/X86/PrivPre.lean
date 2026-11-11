module

public import VerifiedGarbage.Impl.Bignum.X86.CrtRt
public import VerifiedGarbage.Impl.Bignum.X86.CopyBytes

/-!
# An RSA private key's precomputed values on x86

`vg_rsa_private_precompute(pre, pre_len, n, n_len, p, p_len, q, q_len,
scratch, scratch_len)`: with the modulus `n` (`k = n_len` bytes) of
`w = ⌈k / 8⌉` words and its factors `p` and `q`, writes `n` and `R² mod n`
(`w` words each), then `R_p² mod p` for `R_p = 2^(64 w_p)` and
`w_p = max(2, ⌈p_len / 8⌉)` (`w_p` words), then the same for `q`, to `pre`
and returns 1 if `n` is valid and `p q = n`, and otherwise writes zeros and
returns 0.

* `n`'s values: `vg_rsa_public_precompute`, whose result is 1 if `n` is
  valid, and whose values are zeros otherwise.
* The factors' values: `primes`, an internal function with
  `vg_rsa_private_crt`'s arguments and working space (`CrtRt`), with `R² mod n`
  (in `pre`, after `n`) as its input, which loads `n`, `p` and `q`, accepts
  `p q = n` (as `CrtRt.validate` does, but at the factors' widths:
  `CrtRt.productBy`, `p`'s `⌈p_len / 4⌉` words by `q`'s `⌈q_len / 4⌉`), loads
  `x = R² mod n` (`loadX`), and for each factor, in the context of its width
  (at half the modulus's if its length fits, as `CrtRt.power` chooses), the
  factor made safe and its constants (`prepCore`), then `x R⁻ᴷ mod p` for the
  context's radix `R` by Montgomery multiplications by one, a chunk of `x` at
  a time (`reduceX`), and from it `2^(128 w_p) mod p`, which it is when `p`
  divides `n` (`x ≡ 2^(128 w) mod p`), by at most two more reductions and as
  many doublings as the lengths leave (`r2Fix`: none for factors of half the
  modulus's length), which it leaves in the working space's wide slot 16 (17
  for `q`). `pre` is not its output: it may write only `n_len` bytes there,
  as `vg_rsa_private_crt`'s output.
* The `8 w_p` bytes of each, little-endian, which is `w_p` words, copied to
  `pre` after `n`'s values (`copyPrimes`).
* The results and-ed together, and `pre` cleared unless it is 1.

Only the public lengths choose branches and loop counts: the factors' values
are computed whether or not `p q = n`, and cleared after.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.PrivPre
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt
open VG.Impl.Bignum.X86.PublicRt (argAt widthB)

/-! ## The factors' values -/

/-- `r` shifted left by `k`, doubled `k` times: the model has no `shl`. -/
def shl (r : Reg) : Nat → List Instr
  | 0 => []
  | k + 1 => .alu .add r (.reg r) :: shl r k

/-- `r = w_p = max(2, ⌈len / 8⌉)` for the length `len`, argument `i` with
`k` words pushed; `t` changes. -/
def primeWords (k i : Nat) (r t : Reg) : List Instr :=
  [.mov r (.mem (argAt k i)), .alu .add r (.imm 7), .shift .shr r 3,
    .mov t (.reg r), .alu .sub t (.imm 2), .shift .shr t 31, .alu .add r (.reg t)]

/-- `x = R² mod n` (`R = 2^(64 w)`) into the wide slot 18, `2 B` bytes, from
the input (argument 4): its `n_len` bytes, little-endian, which are the
words of `R² mod n` that `vg_rsa_public_precompute` wrote to `pre`, whose
higher bytes are zeros. -/
def loadX : Prog isa :=
  .seq (zero (.slot .wide 18) (two .wide)) <|
  .seq (.block (ptrTo (.slot .wide 18) .ebx .edx ++ [.mov .esi (.mem (argAt 0 4)), .mov .ecx (.mem (argAt 0 5))]))
    copyBytes

/-- `prepBase` without its power of two: the factor in slot 0 replaced by
three unless it is an odd number above one, one in slot 3 and
`-M⁻¹ mod 2³²`. -/
def prepCore (c : Ctx) : Prog isa :=
  .seq (setSmall (.slot c 3) (one c) 1) <|
  .seq (setSmall (.slot c 7) (one c) 3) <|
  .seq (lessThan (.slot c 3) (.slot c 0) (one c)) <|
  .seq (.block [.mov .edx (.mem (sc numBase)), .alu .and .edx (.imm 1), .mov .eax (.imm 0),
    .alu .sub .eax (.reg .edx), .alu .and .ecx (.reg .eax), .alu .xor .ecx (.imm (BitVec.allOnes 32))]) <|
  .seq (select (.slot c 7) (.slot c 0) (one c)) (.block (VG.Impl.Mont.X86.Dynamic.setupInverse numBase invOff))

/-- The chunks of `x` in the context (`Bc` bytes each). -/
def chunks : Ctx → Nat
  | .wide => 1
  | .half => 2

/-- `x R⁻ᴷ mod M` into slot 4 for `K = chunks c`, chunk by chunk, low to
high, by Montgomery multiplications by one (slot 3), which need only one
below `M`: in the wide context `x` is one chunk; in the half context, its
low half (slot 5) and its high half (slot 6), `lo R⁻² + hi R⁻¹`. -/
def reduceX : Ctx → Prog isa
  | .wide => .seq (copy (.slot .wide 18) (.slot .wide 5) (one .wide)) (mul .wide 4 5 3)
  | .half =>
    .seq (copy (.slot .wide 18) (.slot .half 5) (one .half)) <|
    .seq (copyHigh 18 6) <|
    .seq (mul .half 4 5 3) <| .seq (mul .half 4 4 3) <| .seq (mul .half 5 6 3) (addMod .half 4 4 5)

/-- `esi = 128 w_p + 8 Bc K` for the length of argument `i` and `K = chunks c`,
`ebx = 128 w`, compared. -/
def fixStart (i : Nat) (c : Ctx) : List Instr :=
  primeWords 0 i .esi .eax ++ shl .esi 7 ++ widthC 0 c .edx ++ shl .edx 3 ++
    List.replicate (chunks c) (.alu .add .esi (.reg .edx)) ++ widthB 0 .ebx ++ shl .ebx 4 ++
    [.alu .cmp .esi (.reg .ebx)]

/-- `esi` up by `8 Bc`, for one more reduction, compared with `ebx = 128 w`. -/
def fixStep (c : Ctx) : List Instr :=
  widthC 0 c .edx ++ shl .edx 3 ++ [.alu .add .esi (.reg .edx)] ++ widthB 0 .ebx ++ shl .ebx 4 ++
    [.alu .cmp .esi (.reg .ebx)]

/-- One more reduction, and `esi` up by `8 Bc`, compared with `ebx`. -/
def fixMore (c : Ctx) : Prog isa := .seq (mul c 4 4 3) (.block (fixStep c))

/-- From `x R⁻ᴷ mod M` in slot 4, `2^(128 w_p) mod M` there when `x ≡ 2^(128 w)
(mod M)`: while `128 w_p + 8 Bc K < 128 w` (at most twice), one more
reduction (a Montgomery multiplication by one, `K` up by one), then
`128 w_p + 8 Bc K - 128 w` doublings. Every count is the lengths'. -/
def r2Fix (i : Nat) (c : Ctx) : Prog isa :=
  .seq (.block (fixStart i c)) <|
  .seq (.ite .b (.seq (fixMore c) (.ite .b (fixMore c) (.block []))) (.block [])) <|
  .seq (.block (widthB 0 .ebx ++ shl .ebx 4 ++ [.alu .sub .esi (.reg .ebx)]))
    (.ite .e (.block []) (.loop (doubleStep c) .ne))

/-- The factor in the wide slot `f`, in the context `c`: made safe, with its
constants (`prepCore`), and its `R_p² mod p` (`Bc` bytes of the context)
from `x` in the wide slot 18 (`reduceX`, `r2Fix`) into the wide slot `o`. -/
def primeIn (f i o : Nat) (c : Ctx) : Prog isa :=
  .seq (copy (.slot .wide f) (.slot c 0) (one c)) <|
  .seq (prepCore c) <|
  .seq (reduceX c) <|
  .seq (r2Fix i c) (copy (.slot c 4) (.slot .wide o) (one c))

/-- The length of argument `i` compared with the half context's `Bc + 1`. -/
def factorTest (i : Nat) : List Instr :=
  [.mov .eax (.mem (argAt 0 i))] ++ widthC 0 .half .edx ++ [.alu .add .edx (.imm 1), .alu .cmp .eax (.reg .edx)]

/-- The factor in the wide slot `f`, whose length is the header word at
`lenOff`, at half the width if its length fits it (as `power`); its
`R_p² mod p` into the wide slot `o`. -/
def factor (f i o : Nat) : Prog isa :=
  .seq (.block (factorTest i)) <|
  .ite .b (primeIn f i o .half) (primeIn f i o .wide)

/-- `r = 4 ⌈L / 4⌉`, the bytes of the words of the length `L`, argument `i`. -/
def lenW (i : Nat) (r : Reg) : List Instr :=
  [.mov r (.mem (argAt 0 i)), .alu .add r (.imm 3), .shift .shr r 2, .alu .add r (.reg r), .alu .add r (.reg r)]

/-- `p q = n` for the factor `p` in the wide slot 10, `q` in 11 and `n` in 9 (`two .wide`
words): its mask at `accOff`. The product is of `p`'s `⌈p_len / 4⌉` words by
`q`'s `⌈q_len / 4⌉` (arguments 7 and 9), not of all `B` bytes of each. -/
def pqCheck : Prog isa :=
  .seq (copy (.slot .wide 10) mulA (one .wide)) <|
  .seq (productBy (lenW 9) (lenW 7 .eax) (.slot .wide 11)) <|
  .seq (equal prod (.slot .wide 9) (two .wide)) (.block [.store (sc accOff) .ecx])

/-- The components (as `vg_rsa_private_crt` loads them: `n` in the wide slot
9, `p` in 10 and `q` in 11), and the acceptance `p q = n`. -/
def check : Prog isa := .seq importComponents pqCheck

def primesBody : Prog isa :=
  .seq loadX <|
  .seq check <|
  .seq (factor 10 7 16) <|
  .seq (factor 11 9 17) (.block [.mov .eax (.mem (sc accOff)), .alu .and .eax (.imm 1)])

/-- The factors' values, with `vg_rsa_private_crt`'s arguments: the output
(`pre`, whose factors' values start `16 ⌈n_len / 8⌉` bytes in), its length (`n_len`), `n`, `n_len`, the input (unread) and its length, `p`,
`p_len`, `q`, `q_len`, `dP` to `qInv` (unread) and their lengths, and the
working space and its length; `eax` 1 if `p q = n`, else 0. -/
def primes : Prog isa := .seq (.block entry) (.seq primesBody (.block restore))

/-! ## `vg_rsa_private_precompute` -/

/-- The frame: the callees' arguments from `esp`, and the first callee's result at `statusOffset`. -/
def frameBytes : Nat := 96
def statusOffset : Nat := 80

def stackAt (d : Nat) : MemOp := ⟨.esp, d⟩
/-- The `i`-th argument, from inside the frame. -/
def incoming (i : Nat) : MemOp := stackAt (frameBytes + 4 + 4 * i)

def copyArgument (i j : Nat) : List Instr := [.mov .eax (.mem (incoming i)), .store (stackAt (4 * j)) .eax]

/-- Arguments `i` to the callee's arguments `j`, for the pairs `(i, j)`. -/
def copies (l : List (Nat × Nat)) : List Instr := l.flatMap fun p => copyArgument p.1 p.2

/-- `2 ⌈n_len / 8⌉`, from argument 3, to the callee's argument 1. -/
def preWords : List Instr :=
  [.mov .eax (.mem (incoming 3)), .alu .add .eax (.imm 7), .shift .shr .eax 3, .alu .add .eax (.reg .eax),
    .store (stackAt 4) .eax]

/-- `vg_rsa_public_precompute(pre, 2 w, n, n_len, scratch, scratch_len)`. -/
def publicArgs : List Instr :=
  copies [(0, 0)] ++ preWords ++ copies [(2, 2), (3, 3), (8, 4), (9, 5)]

/-- `primes`' arguments but the input, as pairs: `(pre, n_len, n, n_len, ·, n_len, p, p_len, q,
q_len, p, p_len, q, q_len, p, p_len, scratch, scratch_len)`. -/
def primesPairs : List (Nat × Nat) :=
  [(0, 0), (3, 1), (2, 2), (3, 3), (3, 5), (4, 6), (5, 7), (6, 8), (7, 9), (4, 10), (5, 11), (6, 12),
    (7, 13), (4, 14), (5, 15), (8, 16), (9, 17)]

/-- `primes`' input, `R² mod n` in `pre` (`pre + 8 ⌈n_len / 8⌉`), to its argument 4. -/
def inputArg : List Instr :=
  [.mov .eax (.mem (incoming 3)), .alu .add .eax (.imm 7), .shift .shr .eax 3] ++ shl .eax 3 ++
    [.alu .add .eax (.mem (incoming 0)), .store (stackAt 16) .eax]

/-- `primes`' arguments, after the first result is saved. -/
def primesArgs : List Instr := [.store (stackAt statusOffset) .eax] ++ copies primesPairs ++ inputArg

/-- The result, `1` if both are, into the frame. -/
def status : List Instr :=
  [.alu .and .eax (.mem (stackAt statusOffset)), .alu .and .eax (.imm 1), .store (stackAt statusOffset) .eax]

/-- Where `esi` and `ebp` are kept while the factors' values are copied. -/
def saveOffset : Nat := 88

/-- `esi` at the wide slot `j` of the working space (argument 8): `numBase`
and `j` strides of `16 ⌈n_len / 8⌉ + 32` bytes in; `ecx` changes. -/
def slotSrc (j : Nat) : List Instr :=
  [.mov .ecx (.mem (incoming 3)), .alu .add .ecx (.imm 7), .shift .shr .ecx 3] ++ shl .ecx 4 ++
    [.alu .add .ecx (.imm 32), .mov .esi (.mem (incoming 8)),
      .alu .add .esi (.imm (BitVec.ofNat 32 numBase))] ++ List.replicate j (.alu .add .esi (.reg .ecx))

/-- `ecx` words of 32 bits from `esi` to `ebp`, both advanced (as `PrecomputeFn.copyOut`). -/
def copyLoop : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
    .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 4)]) .ne

/-- `ebp` at `pre` (argument 0), after its `16 ⌈n_len / 8⌉` bytes of `n`'s
values, and the `8 w_p` bytes of the factor of argument `i` if `skip` is
`some i`; `eax` and `ecx` change. -/
def dstAt (skip : Option Nat) : List Instr :=
  [.mov .ebp (.mem (incoming 3)), .alu .add .ebp (.imm 7), .shift .shr .ebp 3] ++ shl .ebp 4 ++
    [.alu .add .ebp (.mem (incoming 0))] ++
    match skip with
    | none => []
    | some i => primeWords (frameBytes / 4) i .eax .ecx ++ shl .eax 3 ++ [.alu .add .ebp (.reg .eax)]

/-- The `8 w_p` bytes of the wide slot `j`, for the length of argument `i`, to
`pre` at `dstAt skip`. -/
def copyPrime (j i : Nat) (skip : Option Nat) : Prog isa :=
  .seq (.block (dstAt skip ++ slotSrc j ++ primeWords (frameBytes / 4) i .ecx .eax ++ shl .ecx 3)) copyLoop

/-- `R_p² mod p` (the wide slot 16) and `R_q² mod q` (17) to `pre`, after its
`16 ⌈n_len / 8⌉` bytes of `n`'s values; `esi` and `ebp` kept. -/
def copyPrimes : Prog isa :=
  .seq (.block [.store (stackAt saveOffset) .esi, .store (stackAt (saveOffset + 4)) .ebp]) <|
  .seq (copyPrime 16 5 none) <|
  .seq (copyPrime 17 7 (some 5))
    (.block [.mov .esi (.mem (stackAt saveOffset)), .mov .ebp (.mem (stackAt (saveOffset + 4)))])

/-- The mask, all ones if the result is 1, at `statusOffset + 4`; `edx` at
`pre` and `ecx` its `8 pre_len` bytes. -/
def maskArgs : List Instr :=
  [.mov .eax (.mem (stackAt statusOffset)), .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax), .store (stackAt (statusOffset + 4)) .ecx,
    .mov .edx (.mem (incoming 0)), .mov .ecx (.mem (incoming 1))] ++ shl .ecx 3

def maskStep : List Instr :=
  [.movzx8 .eax ⟨.edx, 0⟩, .alu .and .eax (.mem (stackAt (statusOffset + 4))), .store8 ⟨.edx, 0⟩ .al,
    .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1), .alu .cmp .ecx (.imm 0)]

def maskLoop : Prog isa := .loop (.block maskStep) .ne

def body (publicName : String) (publicCode : Prog isa) (primesName : String) (primesCode : Prog isa) : Prog isa :=
  .seq (.block publicArgs) <|
  .seq (.call publicName publicCode) <|
  .seq (.block primesArgs) <|
  .seq (.call primesName primesCode) <|
  .seq (.block status) <|
  .seq copyPrimes <|
  .seq (.block maskArgs) (.seq maskLoop (.block [.mov .eax (.mem (stackAt statusOffset))]))

def code (publicName : String) (publicCode : Prog isa) (primesName : String) (primesCode : Prog isa) :
    Prog isa :=
  .frame (.alloc frameBytes) (body publicName publicCode primesName primesCode) (.free frameBytes)

end VG.Impl.Bignum.X86.PrivPre
