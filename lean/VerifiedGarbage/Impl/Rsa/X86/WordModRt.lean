module

public import VerifiedGarbage.Impl.Rsa.X86.KeyRt

/-! # A remainder by word steps at a width read at run time (i686)

`[r] = [x] mod [m]` for the dividend `x`, an array of `w` words (`B` bytes,
`KeyRt`'s width), and the modulus `m` of `W' = ⌈m_len / 4⌉` words, `m_len`
an argument, with the top bit of its word `W' - 1` set (`orTop` sets it).
As `R2Words`' steps (Knuth, TAOCP vol. 2, §4.3.1, Algorithm D, with Möller
and Granlund's reciprocal and a 3-by-2 estimate), each with a word of the
dividend brought down: `r` starts as `x`'s top `W' - 1` words, below `m`,
then `r := (r 2^32 + xᵢ) mod m` for `x`'s words from `w - W'` down to 0.
The modulus is already normalized, so there is no shift: `m` may be secret.

The header words 60 to 92 hold the step's scalars: `d` and `d₁`, the top
two words of `m` (60, 88), the reciprocal `v` (64), the mask of `u₂ = d`
(68), the steps left (72), `q̂` (76), `u₀` and `u₂` (80, 84) and the digit
(92). Every branch and address depends only on `n_len` and `m_len`; the
steps' count is read back from the header.

The callers take this path only under a public guard (`balanced`): a
balanced key whose modulus fills its words and has its top bit set, where
the factors (and so `p - 1` and `q - 1` with their low bit cleared) have
their top bit set whenever `p q = n`.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.WordModRt
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt

def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

def oD : Nat := 60
def oV : Nat := 64
def oMask : Nat := 68
def oSteps : Nat := 72
def oQ : Nat := 76
def oU0 : Nat := 80
def oU2 : Nat := 84
def oD1 : Nat := 88
def oDig : Nat := 92

variable (L : Lay)

/-- `r = 4 W' = 4 ⌈m_len / 4⌉`, for `m_len` argument `ml`. -/
def width4 (ml : Nat) (r : Reg) : List Instr :=
  [.mov r (.mem (argOp ml)), .alu .add r (.imm 3), .shift .shr r 2, .alu .add r (.reg r), .alu .add r (.reg r)]

/-- `r` at word `W' - i` of array `j`, through `t`. -/
def topPtr (ml : Nat) (r : Reg) (j i : Nat) (t : Reg) : List Instr :=
  arrPtr L r j t ++ width4 ml t ++ [.alu .add r (.reg t), .alu .sub r (.imm (BitVec.ofNat 32 (4 * i)))]

/-! ## `d`, `d₁` and `v` -/

/-- The top bit of `m`'s word `W' - 1` set, and `d`, `d₁`, its top two words, into the header. -/
def orTop (ml m : Nat) : List Instr :=
  topPtr L ml .ebx m 2 .ecx ++
    [.mov .eax (.mem (at_ .ebx 4)), .alu .or .eax (.imm (BitVec.ofNat 32 0x80000000)), .store (at_ .ebx 4) .eax,
      .store (sc oD) .eax, .mov .eax (.mem (at_ .ebx 0)), .store (sc oD1) .eax]

def divBit : List Instr :=
  [.alu .add .edx (.reg .edx), .alu .sbb .ebp (.reg .ebp), .alu .add .edx (.imm 1),
    .mov .eax (.reg .edx), .alu .sub .eax (.reg .esi), .alu .sbb .ebx (.reg .ebx), .alu .xor .ebx (.imm (-1)),
    .alu .or .ebx (.reg .ebp), .mov .eax (.reg .esi), .alu .and .eax (.reg .ebx), .alu .sub .edx (.reg .eax),
    .alu .add .ecx (.reg .ecx), .alu .sub .ecx (.reg .ebx), .alu .sub .edi (.imm 1)]

def recip : Prog isa := seqs [
  .block [.mov .esi (.mem (sc oD)), .mov .edx (.reg .esi), .alu .xor .edx (.imm (-1)), .mov .ecx (.imm 0),
    .mov .edi (.imm 32)],
  .loop (.block divBit) .ne,
  .block (restoreEdi L ++ [.store (sc oV) .ecx])]

/-! ## A step: `r := (r 2^32 + digit) mod m` -/

/-- `u₀` and `u₂` into the header and `u₁` into `ebp`, `eax` = `u₂`: `r`'s words `W' - 3` to `W' - 1`, from `ebx` at word `W' - 3`. -/
def topWords : List Instr :=
  [.mov .eax (.mem (at_ .ebx 0)), .store (sc oU0) .eax, .mov .ebp (.mem (at_ .ebx 4)),
    .mov .eax (.mem (at_ .ebx 8)), .store (sc oU2) .eax]

def quot : List Instr :=
  [.mov .ecx (.mem (sc oD)), .alu .sub .ecx (.reg .eax), .alu .cmp .ecx (.imm 1), .alu .sbb .ecx (.reg .ecx),
    .store (sc oMask) .ecx, .alu .xor .ecx (.imm (-1)), .alu .and .eax (.reg .ecx),
    .mov .ecx (.reg .eax), .mov .eax (.mem (sc oV)), .mul .ecx, .alu .add .eax (.reg .ebp),
    .alu .adc .edx (.reg .ecx),
    .mov .ebx (.reg .edx), .alu .add .ebx (.imm 1), .mov .ecx (.reg .eax), .mov .eax (.reg .ebx),
    .mov .esi (.mem (sc oD)), .mul .esi, .mov .edx (.reg .ebp), .alu .sub .edx (.reg .eax),
    .alu .cmp .ecx (.reg .edx), .alu .sbb .eax (.reg .eax), .alu .add .ebx (.reg .eax),
    .alu .and .eax (.reg .esi), .alu .add .edx (.reg .eax),
    .mov .eax (.reg .esi), .alu .sub .eax (.imm 1), .alu .cmp .eax (.reg .edx), .alu .adc .ebx (.imm 0),
    .alu .or .ebx (.mem (sc oMask)), .store (sc oQ) .ebx]

def quot3 : List Instr :=
  [.mov .ecx (.mem (sc oQ)), .mov .eax (.mem (sc oD1)), .mul .ecx, .mov .ebx (.reg .eax), .mov .esi (.reg .edx),
    .mov .eax (.mem (sc oD)), .mul .ecx, .alu .add .eax (.reg .esi), .alu .adc .edx (.imm 0),
    .mov .esi (.mem (sc oU0)), .alu .sub .esi (.reg .ebx), .alu .sbb .ebp (.reg .eax),
    .mov .eax (.mem (sc oU2)), .alu .sbb .eax (.reg .edx)]

def fix3 : List Instr :=
  [.mov .edx (.reg .eax), .alu .add .edx (.reg .edx), .alu .sbb .edx (.reg .edx), .alu .add .ecx (.reg .edx),
    .mov .ebx (.reg .edx), .alu .and .ebx (.mem (sc oD1)), .alu .and .edx (.mem (sc oD)),
    .alu .add .esi (.reg .ebx), .alu .adc .ebp (.reg .edx), .alu .adc .eax (.imm 0)]

def refine3 : List Instr := quot3 ++ fix3 ++ fix3 ++ [.store (sc oQ) .ecx]

/-- `t = r 2^32 + digit - q̂ m` over `W' + 1` words: `ebx` at `m`, `esi` at `r`, `ebp` at `t`. -/
def subPtrs (r m t : Nat) : List Instr :=
  arrPtr L .ebx m .edx ++ arrPtr L .esi r .edx ++ arrPtr L .ebp t .edx ++ [.mov .ecx (.mem (sc oQ))]

def subHead (ml : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ebx 0)), .mul .ecx, .store (at_ .ebp 4) .edx, .mov .edx (.mem (sc oDig)),
    .alu .sub .edx (.reg .eax), .store (at_ .ebp 0) .edx, .alu .sbb .eax (.reg .eax), .mov .edx (.mem (at_ .ebp 4)),
    .alu .sub .edx (.reg .eax), .store (at_ .ebp 4) .edx] ++ width4 ml .edi ++
  [.alu .sub .edi (.imm 4), .alu .add .ebx (.imm 4), .alu .add .ebp (.imm 4)]

def subBody : List Instr :=
  [.mov .eax (.mem (at_ .ebx 0)), .mul .ecx, .alu .add .eax (.mem (at_ .ebp 0)), .alu .adc .edx (.imm 0),
    .store (at_ .ebp 4) .edx, .mov .edx (.mem (at_ .esi 0)), .alu .sub .edx (.reg .eax), .store (at_ .ebp 0) .edx,
    .alu .sbb .eax (.reg .eax), .mov .edx (.mem (at_ .ebp 4)), .alu .sub .edx (.reg .eax), .store (at_ .ebp 4) .edx,
    .alu .add .ebx (.imm 4), .alu .add .esi (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .edi (.imm 4)]

def subTop : List Instr :=
  [.mov .edx (.mem (at_ .esi 0)), .alu .sub .edx (.mem (at_ .ebp 0)), .store (at_ .ebp 0) .edx] ++ restoreEdi L

def mulSub (ml r m t : Nat) : Prog isa :=
  seqs [.block (subPtrs L r m t ++ subHead ml), .loop (.block subBody) .ne, .block (subTop L)]

def addHead (ml m t : Nat) : List Instr :=
  arrPtr L .ebx m .edx ++ arrPtr L .ebp t .edx ++ width4 ml .edi ++
  [.mov .eax (.reg .ebp), .alu .add .eax (.reg .edi), .mov .eax (.mem (at_ .eax 0)), .alu .add .eax (.reg .eax),
    .alu .sbb .ecx (.reg .ecx), .mov .esi (.imm 0)]

def addBody : List Instr :=
  [.mov .eax (.mem (at_ .ebx 0)), .alu .and .eax (.reg .ecx), .alu .add .esi (.reg .esi),
    .alu .adc .eax (.mem (at_ .ebp 0)), .store (at_ .ebp 0) .eax, .alu .sbb .esi (.reg .esi),
    .alu .add .ebx (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .edi (.imm 4)]

def addTop : List Instr :=
  [.mov .eax (.mem (at_ .ebp 0)), .alu .sub .eax (.reg .esi), .store (at_ .ebp 0) .eax] ++ restoreEdi L

def addBack (ml m t : Nat) : Prog isa := seqs [.block (addHead L ml m t), .loop (.block addBody) .ne, .block (addTop L)]

def copyBack (ml r t : Nat) : Prog isa := seqs [
  .block (arrPtr L .esi t .edx ++ arrPtr L .ebp r .edx ++ width4 ml .edi),
  .loop (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
    .alu .add .ebp (.imm 4), .alu .sub .edi (.imm 4)]) .ne,
  .block (restoreEdi L)]

def step (ml r m t : Nat) : Prog isa :=
  seqs [.block (topPtr L ml .ebx r 3 .ecx ++ topWords ++ quot ++ refine3), mulSub L ml r m t, addBack L ml m t,
    copyBack L ml r t]

/-! ## The remainder -/

/-- `r`, the dividend's bytes: `B` (one array), or `2 B` (`wide`, a product across two). -/
def xBytes (wide : Bool) (r : Reg) : List Instr := bytesB L r ++ (if wide then [.alu .add r (.reg r)] else [])

/-- `r` set to `x`'s top `W' - 1` words, its word `W' - 1` zero, and the steps' count
`X - W' + 1` into the header, for `X` the dividend's words. -/
def seed (ml x r : Nat) (wide : Bool) : Prog isa := seqs [
  zeroWide L r,
  .block (arrPtr L .esi x .edx ++ xBytes L wide .ecx ++ [.alu .add .esi (.reg .ecx)] ++ width4 ml .ecx ++
    [.alu .sub .ecx (.imm 4), .alu .sub .esi (.reg .ecx)] ++ arrPtr L .ebp r .edx ++
    width4 ml .edi ++ [.alu .sub .edi (.imm 4)]),
  .ite .e (.block []) (.loop (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
    .alu .add .ebp (.imm 4), .alu .sub .edi (.imm 4)]) .ne),
  .block (restoreEdi L ++ xBytes L wide .eax ++ [.shift .shr .eax 2] ++ width4 ml .ecx ++
    [.shift .shr .ecx 2, .alu .sub .eax (.reg .ecx), .alu .add .eax (.imm 1), .store (sc oSteps) .eax])]

/-- The digit `x[steps - 1]` into the header, then the step, then the count down. -/
def digitStep (ml x r m t : Nat) : Prog isa := seqs [
  .block (arrPtr L .ebx x .edx ++ [.mov .eax (.mem (sc oSteps)), .alu .sub .eax (.imm 1), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .ebx (.reg .eax), .mov .eax (.mem (at_ .ebx 0)), .store (sc oDig) .eax]),
  step L ml r m t,
  .block [.mov .eax (.mem (sc oSteps)), .alu .sub .eax (.imm 1), .store (sc oSteps) .eax]]

/-- `[r] = [x] mod [m]` (`W'` words of `r`; `t` its temporary of `W' + 1`). -/
def wordMod (ml x r m t : Nat) (wide : Bool := false) : Prog isa := seqs [.block (orTop L ml m), recip L, seed L ml x r wide,
  .loop (digitStep L ml x r m t) .ne]

/-! ## The guard -/

/-- The header word `sl` zero exactly where `n_len` (argument `nl`) is a multiple of 8 and at
least 128, `p_len` and `q_len` (arguments `pl`, `ql`) are `n_len / 2`, and `n`'s top bit, the
top bit of array `n`'s word `w - 1`, is set. All of these are public. -/
def balanced (nl pl ql n sl : Nat) : List Instr :=
  [.mov .eax (.mem (argOp nl)), .mov .ecx (.reg .eax), .alu .and .ecx (.imm 7),
    .mov .edx (.mem (argOp pl)), .alu .add .edx (.reg .edx), .alu .sub .edx (.reg .eax), .alu .or .ecx (.reg .edx),
    .mov .edx (.mem (argOp ql)), .alu .add .edx (.reg .edx), .alu .sub .edx (.reg .eax), .alu .or .ecx (.reg .edx),
    .alu .cmp .eax (.imm 128), .alu .sbb .edx (.reg .edx), .alu .or .ecx (.reg .edx)] ++
  arrPtr L .ebx n .edx ++ bytesB L .eax ++
  [.alu .add .ebx (.reg .eax), .alu .sub .ebx (.imm 4), .mov .eax (.mem (at_ .ebx 0)), .alu .xor .eax (.imm (-1)),
    .shift .shr .eax 31, .alu .or .ecx (.reg .eax), .store (sc sl) .ecx]

/-- `word` where the guard in header word `sl` held, else `other`: a branch on public values. -/
def ifBalanced (sl : Nat) (word other : Prog isa) : Prog isa :=
  .seq (.block [.mov .eax (.mem (sc sl)), .alu .cmp .eax (.imm 0)]) (.ite .e word other)

/-! ## The product of two numbers -/

/-- The header word counting the product's rows. -/
def oJ : Nat := 96

/-- Row `j` (header word 96): `[o] += [a] b_j 2^(32 j)` over `w + 1` words, `b_j` word `j` of `[b]`. -/
def mulRow (o a b : Nat) (rows : Option Nat := none) : Prog isa := seqs [
  .block (arrPtr L .ebx b .edx ++ [.mov .eax (.mem (sc oJ)), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .ebx (.reg .eax), .mov .ecx (.mem (at_ .ebx 0))] ++ arrPtr L .ebp o .edx ++
    [.alu .add .ebp (.reg .eax)] ++ arrPtr L .esi a .edx ++ bytesB L .edi ++ [.mov .ebx (.imm 0)]),
  .loop (.block [.mov .eax (.mem (at_ .esi 0)), .mul .ecx, .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
    .alu .add .eax (.mem (at_ .ebp 0)), .alu .adc .edx (.imm 0), .store (at_ .ebp 0) .eax, .mov .ebx (.reg .edx),
    .alu .add .esi (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .edi (.imm 4)]) .ne,
  .block ([.store (at_ .ebp 0) .ebx] ++ restoreEdi L ++
    [.mov .eax (.mem (sc oJ)), .alu .add .eax (.imm 1), .store (sc oJ) .eax] ++
    (match rows with
     | none => bytesB L .ecx ++ [.shift .shr .ecx 2, .alu .cmp .eax (.reg .ecx)]
     | some k => [.alu .cmp .eax (.imm (BitVec.ofNat 32 k))]))]

/-- `[o] = [a] [b]`, `2 w` words across arrays `o` and `o + 1`. -/
def mulWide (o a b : Nat) : Prog isa := seqs [zeroWide L o, zeroWide L (o + 1),
  .block [.mov .eax (.imm 0), .store (sc oJ) .eax], .loop (mulRow L o a b) .ne]

/-- `[o] = [a] (b mod 2^64)`, the low two words of `[b]` (`e`, of at most five bytes), across
arrays `o` and `o + 1`. -/
def mulShort (o a b : Nat) : Prog isa := seqs [zeroWide L o, zeroWide L (o + 1),
  .block [.mov .eax (.imm 0), .store (sc oJ) .eax], .loop (mulRow L o a b (some 2)) .ne]

/-- The header word `sl` one if the `2 w` words at `o` are `[n]`, else zero. -/
def eqWide (sl o n : Nat) : Prog isa := seqs [
  .block (arrPtr L .ebp o .edx ++ arrPtr L .ebx n .edx ++ bytesB L .edx ++ [.mov .ecx (.imm 0)]),
  eqLoop,
  .block (bytesB L .edx),
  .loop (.block [.alu .or .ecx (.mem (at_ .ebp 0)), .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne,
  .block [.mov .eax (.imm 0), .alu .sub .eax (.reg .ecx), .alu .or .eax (.reg .ecx), .shift .shr .eax 31,
    .alu .xor .eax (.imm 1), .store (sc sl) .eax]]

end VG.Impl.Rsa.X86.WordModRt
