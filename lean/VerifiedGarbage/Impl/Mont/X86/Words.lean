module

public import VerifiedGarbage.Impl.Mont.X86

/-!
# Loops over the words of a runtime-modulus workspace, on 32-bit x86

DSA's numbers are up to 96 words, so its arithmetic loops over words where
the fixed-modulus code (`Impl/Mont/X86.lean`) unrolls them. `wordLoop k
body` runs `body` with `ebp = edi + 4 j` for `j < k` (`0 < k`): the body
addresses word `j` of an array at `d` as `[ebp + d]`, and must keep `ebp`,
`edi` and `esi`. The loop's own instructions write `ebp`, `edx` and the
flags, so a carry or borrow that a body passes to the next iteration is a
mask in `ecx` (zero, or all ones): `restore` sets the carry flag from it
(through `edx`) before the `adc` or `sbb`, and `sbb ecx, ecx` saves it.

Every address is a register that only moves by public steps (`edi`,
`ebp`, a caller's pointer) plus a constant, and every branch is on a word
count: no operand affects timing.
-/

@[expose] public section

namespace VG.Impl.Mont.X86.Dynamic

open VG.X86 VG.Impl.Mont VG.Impl.Mont.X86

/-- `body` for `j < k`, with `ebp = edi + 4 j`. -/
def wordLoop (k : Nat) (body : List Instr) : Prog isa :=
  .seq (.block [.mov .ebp (.reg .edi)])
    (.loop (.block (body ++ [.alu .add .ebp (.imm 4), .mov .edx (.reg .edi),
      .alu .add .edx (.imm (BitVec.ofNat 32 (4 * k))), .alu .cmp .ebp (.reg .edx)])) .ne)

/-- The carry flag from the mask `ecx` (`0 - ecx` borrows exactly when it
is nonzero). -/
def restore : List Instr := [.mov .edx (.imm 0), .alu .cmp .edx (.reg .ecx)]

/-- `[o] = 0`, `k` words. -/
def zerosW (o k : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm 0)]) (wordLoop k [.store (at_ .ebp o) .eax])

/-- `[o] = x`, `k` words: zeros, then `x`'s nonzero words. -/
def setConstW (k o x : Nat) : Prog isa :=
  .seq (zerosW o k) (.block ((List.range k).flatMap fun j =>
    if x >>> (32 * j) % 2 ^ 32 = 0 then []
    else [.mov .eax (.imm (BitVec.ofNat 32 (x >>> (32 * j)))), .store (sc (o + 4 * j)) .eax]))

/-- `[o] = [a] op [b]`, `k` words, with the carry (or borrow) of `op'`
(`adc` or `sbb`) left as a mask in `ecx`. -/
def chainW (op' : AluOp) (k o a b : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0)]) (wordLoop k ([.mov .eax (.mem (at_ .ebp a))] ++ restore ++
    [.alu op' .eax (.mem (at_ .ebp b)), .store (at_ .ebp o) .eax, .alu .sbb .ecx (.reg .ecx)]))

/-- `[o] = [tmp]` where the mask `ecx` is all ones, else `[src]`, `k` words. -/
def selectsW (k src tmp o : Nat) : Prog isa :=
  wordLoop k [.mov .eax (.mem (at_ .ebp src)), .mov .edx (.mem (at_ .ebp tmp)),
    .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx),
    .store (at_ .ebp o) .eax]

/-- The number at `[src]` (`N` words, then a top word 0 or 1), below `2m`,
reduced modulo `m` into `[o]`, through `[tmp]`. -/
def csubW (M : Mod) (src o : Nat) : Prog isa :=
  .seq (chainW .sbb (words M) M.tmp src M.mo) <|
  .seq (.block ([.mov .eax (.mem (sc (src + 4 * words M)))] ++ restore ++
    [.alu .sbb .eax (.imm 0), .alu .sbb .eax (.reg .eax), .alu .xor .eax (.imm (-1)), .mov .ecx (.reg .eax)]))
    (selectsW (words M) src M.tmp o)

/-- `[o] = [a] + [b] mod m`, through the accumulator `[acc]`. -/
def addW (M : Mod) (acc o a b : Nat) : Prog isa :=
  .seq (chainW .adc (words M) acc a b) <|
  .seq (.block [.mov .eax (.imm 0), .alu .sub .eax (.reg .ecx), .store (sc (acc + 4 * words M)) .eax])
    (csubW M acc o)

/-- `[o] = [a] - [b] mod m`, as `[a] + (m - [b])`, `m - [b]` in the temporary area. -/
def subW (M : Mod) (acc o a b : Nat) : Prog isa :=
  .seq (chainW .sbb (words M) M.tmp M.mo b) (addW M acc o a M.tmp)

end VG.Impl.Mont.X86.Dynamic
