import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Impl.Mont.Mod
import VerifiedGarbage.Impl.Mont.X86.Sparse

/-!
# Montgomery arithmetic modulo an odd multiword modulus, on x86 (32-bit)

Arithmetic modulo an odd `m < 2^(64 n)`, on numbers below `m` held in the
working space, whose base is in `edi`, as `N = 2n` little-endian 32-bit
words at a constant offset (the same bytes as the `n` 64-bit words of the
other targets, so the slots, the modulus `[M.mo]` and the temporary area
`[M.tmp]` are laid out as theirs). `-m⁻¹ mod 2³²` is the low word of
`M.minv`. With `R = 2^(32 N) = 2^(64 n)`:

* `mul acc o a b`: `[o] = [a] [b] R⁻¹ mod m`, by coarsely integrated operand
  scanning (CIOS) with the accumulator in memory: `2N + 1` words at
  `[acc]`, cleared, and a window of them at `[ebp + acc]`, `ebp` starting at
  `edi`. Each of the `N` iterations of the loop (`row`) adds `a_i [b]` to
  the window, then `u m` for `u = t₀ m' mod 2³²`, which clears the window's
  low word, and moves the window up a word (`ebp += 4`) instead of shifting
  the accumulator. Its last `N + 1` words are then below `2m` and reduced by
  `csub`.
* `add acc o a b`, `sub acc o a b`: `[a] ± [b] mod m`, through the
  accumulator, with a conditional subtraction (`csub`) or addition of `m`.
* `csub src o`: the number below `2m` at `[src]` (`N` words and a top word,
  0 or 1) reduced below `m` into `[o]`: its difference with `m` is computed
  into `[M.tmp]`, then selected with a mask if it did not borrow.

Every multiplication is `mul`, every selection a mask, and every address
`edi` or `ebp` (which is `edi` plus a multiple of 4 counted by the loop)
plus a constant: nothing but `edi` may affect timing. The operations use
`eax`, `ebx`, `ecx`, `edx` and `ebp`, and write only `[o]`, `[acc]` and
`[M.tmp]`.
-/

namespace VG.Impl.Mont.X86

open VG.X86

/-- `[r + d]`. -/
def at_ (r : Reg) (d : Nat) : MemOp := { base := r, disp := d }

/-- `[edi + d]`: byte `d` of the working space. -/
def sc (d : Nat) : MemOp := at_ .edi d

/-- The number of 32-bit words of a number. -/
def words (M : Mod) : Nat := 2 * M.n

/-- `-m⁻¹ mod 2³²`. -/
def minv32 (M : Mod) : BitVec 32 := M.minv.setWidth 32

/-- `[ebp + acc + 4j] += ecx · [edi + b + 4j] + ebx`, its carry word to
`ebx` (a multiply-accumulate step; it never overflows). -/
def mulStep (acc b j : Nat) : List Instr :=
  [.mov .eax (.mem (sc (b + 4 * j))), .mul .ecx, .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
    .alu .add .eax (.mem (at_ .ebp (acc + 4 * j))), .alu .adc .edx (.imm 0),
    .store (at_ .ebp (acc + 4 * j)) .eax, .mov .ebx (.reg .edx)]

/-- The carry word `ebx` added into the window's words `N` and `N + 1`. -/
def carryUp (acc N : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ebp (acc + 4 * N))), .alu .add .eax (.reg .ebx),
    .store (at_ .ebp (acc + 4 * N)) .eax, .mov .eax (.mem (at_ .ebp (acc + 4 * N + 4))),
    .alu .adc .eax (.imm 0), .store (at_ .ebp (acc + 4 * N + 4)) .eax]

/-- The window `+= ecx · [b]`, `N` words, with its carry. -/
def mulRow (acc b N : Nat) : List Instr :=
  .mov .ebx (.imm 0) :: (List.range N).flatMap (mulStep acc b) ++ carryUp acc N

/-- The reduction digit `q = t₀ m' mod 2³²`. A unit inverse, as in
P-256's field, needs only the load: its multiplication is the identity. -/
def redDigit (M : Mod) (acc : Nat) : List Instr :=
  if minv32 M = 1 then [.mov .ecx (.mem (at_ .ebp acc))]
  else [.mov .eax (.mem (at_ .ebp acc)), .mov .ecx (.imm (minv32 M)), .mul .ecx, .mov .ecx (.reg .eax)]

/-- Add the reduction multiple using P-256's sparse identity when certified. -/
def redRow (M : Mod) (acc : Nat) : List Instr :=
  if p256RedEnabled M then p256Red acc else mulRow acc M.mo (words M)

/-- An iteration of `mul`: the window `+= a_i [b]`, then `+= u m` with
`u = t₀ m' mod 2³²`, after which its low word is zero; then the window
moves up a word, and `ebp` is compared with `edi + 4N` (the end of the
loop). -/
def row (M : Mod) (acc a b : Nat) : List Instr :=
  let N := words M
  ([.mov .ecx (.mem (at_ .ebp a))] : List Instr) ++ mulRow acc b N ++
  redDigit M acc ++
    redRow M acc ++
  ([.alu .add .ebp (.imm 4), .mov .edx (.reg .edi), .alu .add .edx (.imm (BitVec.ofNat 32 (4 * N))),
    .alu .cmp .ebp (.reg .edx)] : List Instr)

/-- `[acc]`, `k` words, cleared (through `eax`). -/
def zeros (acc k : Nat) : List Instr :=
  .mov .eax (.imm 0) :: (List.range k).map fun j => .store (sc (acc + 4 * j)) .eax

/-- `[tmp] = [src] - [mo]`, `N` words, with `op` (`sub`, then `sbb`) on the
first word, through `eax`. -/
def diffs (M : Mod) (src : Nat) : List Instr :=
  (List.range (words M)).flatMap fun j =>
    [.mov .eax (.mem (sc (src + 4 * j))), .alu (if j = 0 then .sub else .sbb) .eax (.mem (sc (M.mo + 4 * j))),
      .store (sc (M.tmp + 4 * j)) .eax]

/-- `[o] = [tmp]` where the mask `eax` is all ones, else `[src]`, `N` words. -/
def selects (M : Mod) (src o : Nat) : List Instr :=
  (List.range (words M)).flatMap fun j =>
    [.mov .ebx (.mem (sc (src + 4 * j))), .mov .edx (.mem (sc (M.tmp + 4 * j))), .alu .xor .edx (.reg .ebx),
      .alu .and .edx (.reg .eax), .alu .xor .ebx (.reg .edx), .store (sc (o + 4 * j)) .ebx]

/-- The number at `[src]` (`N` words, then a top word 0 or 1), below `2m`,
reduced modulo `m` into `[o]`: the difference with `m` is computed into
`[tmp]`; `eax` is all ones if it did not borrow, and selects it. -/
def csub (M : Mod) (src o : Nat) : List Instr :=
  diffs M src ++
  ([.mov .eax (.mem (sc (src + 4 * words M))), .alu .sbb .eax (.imm 0), .alu .sbb .eax (.reg .eax),
    .alu .xor .eax (.imm (-1))] : List Instr) ++
  selects M src o

/-- `[o] = [a] [b] R⁻¹ mod m` (`o` may be `a` or `b`). -/
def mul (M : Mod) (acc o a b : Nat) : Prog isa :=
  .seq (.block (zeros acc (2 * words M + 1) ++ ([.mov .ebp (.reg .edi)] : List Instr))) <|
  .seq (.loop (.block (row M acc a b)) .ne) <|
    .block (csub M (acc + 4 * words M) o)

/-- `[acc] = [a] op [b]`, `N` words, with `op` on the first word and `op'`
on the others (`add` and `adc`, `sub` and `sbb`), through `eax`. -/
def chain (M : Mod) (op op' : AluOp) (acc a b : Nat) : List Instr :=
  (List.range (words M)).flatMap fun j =>
    [.mov .eax (.mem (sc (a + 4 * j))), .alu (if j = 0 then op else op') .eax (.mem (sc (b + 4 * j))),
      .store (sc (acc + 4 * j)) .eax]

/-- `[o] = [a] + [b] mod m`. -/
def add (M : Mod) (acc o a b : Nat) : List Instr :=
  chain M .add .adc acc a b ++
  ([.mov .eax (.imm 0), .alu .adc .eax (.imm 0), .store (sc (acc + 4 * words M)) .eax] : List Instr) ++
  csub M acc o

/-- `[tmp] = [mo]` masked with `eax`, `N` words. -/
def masked (M : Mod) : List Instr :=
  (List.range (words M)).flatMap fun j =>
    [.mov .edx (.mem (sc (M.mo + 4 * j))), .alu .and .edx (.reg .eax), .store (sc (M.tmp + 4 * j)) .edx]

/-- `[o] = [a] - [b] mod m`: the difference, and `m` added under the mask
`eax` of its borrow (through `[tmp]`). -/
def sub (M : Mod) (acc o a b : Nat) : List Instr :=
  chain M .sub .sbb acc a b ++ ([.alu .sbb .eax (.reg .eax)] : List Instr) ++ masked M ++
  chain M .add .adc o acc M.tmp

end VG.Impl.Mont.X86
