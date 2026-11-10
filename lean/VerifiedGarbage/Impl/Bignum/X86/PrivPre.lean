module

public import VerifiedGarbage.Impl.Bignum.X86.CrtRt

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
  `vg_rsa_private_crt`'s arguments and working space (`CrtRt`), which loads
  `n`, `p` and `q`, accepts `p q = n` (as `CrtRt.validate` does, by
  `CrtRt.wideProduct`), and for each factor, in the context of its width
  (at half the modulus's if its length fits, as `CrtRt.power` chooses), the
  factor made safe and its constants (`CrtRt.prepBase`), then one doubled
  `128 w_p` times (`r2Prime`): `2^(128 w_p) mod p`, whose `8 w_p` bytes it
  copies to the output, little-endian, which is `w_p` words.
* The results and-ed together, and `pre` cleared unless it is 1.

Only the public lengths choose branches and loop counts: the factors' values
are computed whether or not `p q = n`, and cleared after.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.PrivPre
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-! ## The factors' values -/

/-- `r` shifted left by `k`, doubled `k` times: the model has no `shl`. -/
def shl (r : Reg) : Nat → List Instr
  | 0 => []
  | k + 1 => .alu .add r (.reg r) :: shl r k

/-- `r = w_p = max(2, ⌈len / 8⌉)` for the length at `lenOff`; `t` changes. -/
def primeWords (r t : Reg) : List Instr :=
  [.mov r (.mem (sc lenOff)), .alu .add r (.imm 7), .shift .shr r 3,
    .mov t (.reg r), .alu .sub t (.imm 2), .shift .shr t 31, .alu .add r (.reg t)]

/-- `2^(128 w_p) mod M` in slot 4: one, doubled `128 w_p` times. -/
def r2Prime (c : Ctx) : Prog isa :=
  .seq (setSmall (.slot c 4) (one c) 1) <|
  .seq (.block (primeWords .esi .eax ++ shl .esi 7)) (.loop (doubleStep c) .ne)

/-- The factor in the wide slot `f`, in the context `c`: made safe, with its
constants (`prepBase`), and its `R_p² mod p` (`Bc` bytes of the context)
into the wide slot `o`. -/
def primeIn (f o : Nat) (c : Ctx) : Prog isa :=
  .seq (copy (.slot .wide f) (.slot c 0) (one c)) <|
  .seq (prepBase c) <|
  .seq (r2Prime c) (copy (.slot c 4) (.slot .wide o) (one c))

/-- The factor in the wide slot `f`, whose length is the header word at
`lenOff`, at half the width if its length fits it (as `power`); its
`R_p² mod p` into the wide slot `o`. -/
def factor (f o : Nat) : Prog isa :=
  .seq (.block ([.mov .eax (.mem (sc lenOff))] ++ widthC 0 .half .edx ++
    [.alu .add .edx (.imm 1), .alu .cmp .eax (.reg .edx)])) <|
  .ite .b (primeIn f o .half) (primeIn f o .wide)

/-- Argument `i`, a factor's length, into the header word at `lenOff`. -/
def setLen (i : Nat) : List Instr := [.mov .eax (.mem (argAt 0 i)), .store (sc lenOff) .eax]

/-- `p q = n` for the factor `p` in the wide slot 10, `q` in 11 and `n` in 9 (`two .wide`
words): its mask at `accOff`. -/
def pqCheck : Prog isa :=
  .seq (copy (.slot .wide 10) mulA (one .wide)) <|
  .seq (wideProduct (.slot .wide 11)) <|
  .seq (equal prod (.slot .wide 9) (two .wide)) (.block [.store (sc accOff) .ecx])

/-- The components (as `vg_rsa_private_crt` loads them: `n` in the wide slot
9, `p` in 10 and `q` in 11), and the acceptance `p q = n`. -/
def check : Prog isa := .seq importComponents pqCheck

def primesBody : Prog isa :=
  .seq check <|
  .seq (.block (setLen 7)) <|
  .seq (factor 10 16) <|
  .seq (.block (setLen 9)) <|
  .seq (factor 11 17) (.block [.mov .eax (.mem (sc accOff)), .alu .and .eax (.imm 1)])

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

/-- `vg_rsa_public_precompute(pre, 2 w, n, n_len, scratch, scratch_len)`. -/
def publicArgs : List Instr :=
  copyArgument 0 0 ++
  [.mov .eax (.mem (incoming 3)), .alu .add .eax (.imm 7), .shift .shr .eax 3, .alu .add .eax (.reg .eax),
    .store (stackAt 4) .eax] ++
  copyArgument 2 2 ++ copyArgument 3 3 ++ copyArgument 8 4 ++ copyArgument 9 5

/-- `primes(pre, n_len, n, n_len, n, n_len, p, p_len, q, q_len, p, p_len, q, q_len, p, p_len,
scratch, scratch_len)`, after the first result is saved. -/
def primesArgs : List Instr :=
  [.store (stackAt statusOffset) .eax] ++ copyArgument 0 0 ++ copyArgument 3 1 ++ copyArgument 2 2 ++ copyArgument 3 3 ++ copyArgument 2 4 ++ copyArgument 3 5 ++
  copyArgument 4 6 ++ copyArgument 5 7 ++ copyArgument 6 8 ++ copyArgument 7 9 ++
  copyArgument 4 10 ++ copyArgument 5 11 ++ copyArgument 6 12 ++ copyArgument 7 13 ++
  copyArgument 4 14 ++ copyArgument 5 15 ++ copyArgument 8 16 ++ copyArgument 9 17

/-- The result, `1` if both are, into `eax` and the frame; the mask, all ones
if it is 1, at `statusOffset + 4`; `edx` at `pre` and `ecx` its `8 pre_len`
bytes. -/
def maskArgs : List Instr :=
  [.alu .and .eax (.mem (stackAt statusOffset)), .alu .and .eax (.imm 1), .store (stackAt statusOffset) .eax,
    .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax), .store (stackAt (statusOffset + 4)) .ecx,
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
  .seq (.block maskArgs) (.seq maskLoop (.block [.mov .eax (.mem (stackAt statusOffset))]))

def code (publicName : String) (publicCode : Prog isa) (primesName : String) (primesCode : Prog isa) :
    Prog isa :=
  .frame (.alloc frameBytes) (body publicName publicCode primesName primesCode) (.free frameBytes)

end VG.Impl.Bignum.X86.PrivPre
