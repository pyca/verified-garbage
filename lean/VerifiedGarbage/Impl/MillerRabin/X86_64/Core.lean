module

public import VerifiedGarbage.Impl.MillerRabin.X86_64.Layout
public import VerifiedGarbage.Impl.Rsa.X86_64.Crt

/-! # Shared fixed-window Miller–Rabin computation

Witness sampling and round counts belong to the callers. The namespace is
retained for compatibility with the existing RSA proofs. -/

@[expose] public section

namespace VG.Impl.RsaKeyGen.X86_64.Candidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64

/-! ## Miller–Rabin's exponent

For `c − 1 = m 2^a` (`m` odd), the exponentiation is by `E = (c − 1) / 2^σ`
for `σ ∈ [1, 4]`, `σ ≡ a (mod 4)`: `E = m 2^(a − σ)` has its lowest set bit
at a multiple of 4, where a window of 4 bits ends. `σ` is secret: `E` is
`c / 2` halved under the masks of `σ > 1`, `σ > 2` and `σ > 3`, which
come from the lowest set bit `l = 2^(a mod 64)` of the lowest nonzero word
of `c − 1` (`l & K ≠ 0` for the constants `K` of `sigK`). -/

/-- `rbp := ` the lowest nonzero word of `c − 1` (`c`'s words, bit 0 of the
first cleared): `rbp |= word & mask (rbp = 0)` from the bottom. -/
def lowWord : List (Prog isa) := [
  .block [.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN))), .mov .rbp (.mem (at0 .r8)),
    .alu .and .rbp (.imm (BitVec.ofInt 32 (-2)))],
  wordLoop 1 [.mov .rax (.mem (ix .r8 .r14)), .alu .cmp .rbp (.imm 1), .alu .sbb .rdx (.reg .rdx),
    .alu .and .rax (.reg .rdx), .alu .or .rbp (.reg .rax)]]

/-- The masks of `σ > j` (`j = 1, 2, 3`) are those of `l & sigK j ≠ 0`: the
bits whose position mod 4 is 0, 2 or 3; 0 or 3; 0. -/
def sigK : Nat → BitVec 64
  | 1 => 0xDDDDDDDDDDDDDDDD
  | 2 => 0x9999999999999999
  | _ => 0x1111111111111111

/-- `[rbx] := r15 ? [rsi] / 2 : [rsi]` over `w` words (`r12`), in place
when `rbx = rsi`: the word below is written once the next is read, the word
in `rbp`. -/
def halfPass : List (Prog isa) := [
  .block [.mov .rbp (.mem (at0 .rsi))],
  wordLoop 1 [.mov .rax (.mem (ix .rsi .r14)), .mov .rdx (.reg .rax), .shift .shl .rdx 63, .mov .rcx (.reg .rbp),
    .shift .shr .rcx 1, .alu .or .rcx (.reg .rdx), .alu .xor .rcx (.reg .rbp), .alu .and .rcx (.reg .r15),
    .alu .xor .rcx (.reg .rbp), .store (ix .rbx .r14 (-8)) .rcx, .mov .rbp (.reg .rax)],
  .block [.mov .rcx (.reg .rbp), .shift .shr .rcx 1, .alu .xor .rcx (.reg .rbp), .alu .and .rcx (.reg .r15),
    .alu .xor .rcx (.reg .rbp), .store (ix .rbx .r12 (-8)) .rcx]]

/-- `[aE] := [aE] / 2` under the mask of `σ > j`, `aE`'s base in `rbx` and `w`
in `r12`. -/
def halfCond (j : Nat) : List (Prog isa) :=
  .block [.mov .rsi (.reg .rbx), .movImm64 .r15 (sigK j), .alu .and .r15 (.mem (ix .rbx .r12)),
    .alu .cmp .r15 (.imm 1), .alu .sbb .r15 (.reg .r15), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))] :: halfPass

/-- `l` after the `w` words of `aE`, then `[aE] := E`. The header is read
before anything is stored: the halvings keep `aE`'s base in `rbx` and `w` in
`r12`. -/
def expSetup : List (Prog isa) :=
  lowWord ++ [
  .block (extBase aE .rbx ++ ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN))),
    .mov .r15 (.imm (BitVec.ofInt 32 (-1))), .mov32 .rax (.imm 0), .alu .sub .rax (.reg .rbp),
    .alu .and .rax (.reg .rbp), .store (ix .rbx .r12) .rax] : List Instr))] ++
  halfPass ++ halfCond 1 ++ halfCond 2 ++ halfCond 3

/-! ## Miller–Rabin -/

/-- The mask of `[aY] = [j]` over `w` words into `rbp` (`j` an extra array,
its base into `r10`). -/
def eqMask (j : Nat) : List (Prog isa) := [
  .block (([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] : List Instr) ++ extBase j .r10 ++
    ([.mov32 .rbp (.imm 0)] : List Instr)),
  wordLoop 0 [.mov .rax (.mem (ix .rbx .r14)), .alu .xor .rax (.mem (ix .r10 .r14)), .alu .or .rbp (.reg .rax)],
  .block [.alu .cmp .rbp (.imm 1), .alu .sbb .rbp (.reg .rbp)]]

/-- `y := y²`, the flag or'ed with `y = −1`. -/
def mrSq (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [mul aY aY aY] ++ eqMask aRm1 ++
  [.block [.mov .rax (.mem (hdr kFlag)), .alu .or .rax (.reg .rbp), .store (hdr kFlag) .rax]]

/-- The first selection pass's registers (`Impl/Rsa/X86_64/Crt.lean`):
`r15 = 0`, `r11 = 8 (w + 2)`, `r13 = 2 ⌈w / 2⌉`, `rbx = aXm` and `rcx` the
entry 0. -/
def selRegs : List Instr :=
  ([.mov32 .r15 (.imm 0), .mov .r12 (.mem (hdr sW)), .mov .r11 (.reg .r12),
    .alu .add .r11 (.imm 2), .alu .add .r11 (.reg .r11), .alu .add .r11 (.reg .r11), .alu .add .r11 (.reg .r11),
    .mov .r13 (.reg .r12), .alu .add .r13 (.imm 1), .shift .shr .r13 1, .alu .add .r13 (.reg .r13),
    .mov .rbx (.mem (hdr (sArr aXm)))] : List Instr) ++ extBase aT0 .rcx

/-- The second pass's: `r15 = 8` and `rcx` the entry 8, from the first's;
the header is not read again once `aXm` has been written. -/
def selNext : List Instr :=
  [.mov32 .r15 (.imm 8), .mov .rax (.reg .r11), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .alu .add .rcx (.reg .rax)]

/-- A pass's masks of `r15 + j = d` (`d` in `kG`) in `xmm(8 + j)`, that of
`r15 = 8` in `xmm7`, and the bases of its eight entries. -/
def selMasks : List (Prog isa) :=
  [.block (Crt.selMask 0 (.mem (hdr kG)) .xmm8), .block (Crt.selMask 1 (.mem (hdr kG)) .xmm9),
    .block (Crt.selMask 2 (.mem (hdr kG)) .xmm10), .block (Crt.selMask 3 (.mem (hdr kG)) .xmm11),
    .block (Crt.selMask 4 (.mem (hdr kG)) .xmm12), .block (Crt.selMask 5 (.mem (hdr kG)) .xmm13),
    .block (Crt.selMask 6 (.mem (hdr kG)) .xmm14), .block (Crt.selMask 7 (.mem (hdr kG)) .xmm15),
    .block (Crt.selMask 0 (.imm 8) .xmm7),
    .block Crt.gatherBases]

/-- The selection of `T_d` (`d` in `kG`) into `aXm` in two passes, over the
entries 0 to 7 and 8 to 15, as `Crt.gatherPass`: each pair of words of
`aXm` becomes `(aXm & xmm7) | OR_j (T_(8p+j) & xmm(8+j))`. -/
def mrSel : List (Prog isa) :=
  [seqs (.block selRegs :: selMasks), .loop (seqs Crt.gatherBody) .ne,
    seqs (.block selNext :: selMasks), .loop (seqs Crt.gatherBody) .ne]

/-- One window, the digit `d` at the top of `kV`: four squarings, `T_d` into
`aXm` by masks, `y := y T_d`; the flag `P := d ≠ 0 ? (y = 1 ∨ y = −1) : P`;
then `kV := kV << 4` and `kBits := kBits − 1` (ZF set when it is 0). -/
def mrWin (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  mrSq mul ++ mrSq mul ++ mrSq mul ++ mrSq mul ++
  [.block [.mov .rax (.mem (hdr kV)), .shift .shr .rax 60, .store (hdr kG) .rax]] ++ mrSel ++
  [mul aY aY aXm] ++ eqMask aRm1 ++ [.block [.store (hdr kG) .rbp]] ++ eqMask aR1 ++
  [.block [.mov .rax (.mem (hdr kV)), .shift .shr .rax 60, .alu .cmp .rax (.imm 1), .alu .sbb .r15 (.reg .r15),
    .mov .rdx (.mem (hdr kG)), .alu .or .rbp (.reg .rdx), .mov .rax (.mem (hdr kFlag)), .alu .and .rax (.reg .r15),
    .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1))), .alu .and .rbp (.reg .r15), .alu .or .rax (.reg .rbp),
    .store (hdr kFlag) .rax,
    .mov .rax (.mem (hdr kV)), .shift .shl .rax 4, .store (hdr kV) .rax,
    .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]]

/-- A squaring after the windows: `y := y²`, the flag or'ed with `y = −1`
under the mask of `σ > j` (from `l`). -/
def mrLast (mul : Nat → Nat → Nat → Prog isa) (j : Nat) : List (Prog isa) :=
  [mul aY aY aY] ++ eqMask aRm1 ++
  [.block (extBase aE .rbx ++ ([.mov .r12 (.mem (hdr sW)), .movImm64 .rdx (sigK j),
    .alu .and .rdx (.mem (ix .rbx .r12)), .alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx),
    .alu .xor .rdx (.imm (BitVec.ofInt 32 (-1))), .alu .and .rbp (.reg .rdx), .mov .rax (.mem (hdr kFlag)),
    .alu .or .rax (.reg .rbp), .store (hdr kFlag) .rax] : List Instr))]

/-- The flag over the windows of `E`, its words from the top, 16 windows
each, then three more squarings: `mrIteration`'s result. -/
def mrExpLoop (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  .block [.mov .rax (.mem (hdr sW)), .store (hdr kWords) .rax, .mov32 .rax (.imm 0), .store (hdr kFlag) .rax],
  .loop (seqs [
    .block (([.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1), .store (hdr kWords) .rax] : List Instr) ++
      extBase aE .rdx ++ ([.mov .rax (.mem (hdr kWords)), .mov .rcx (.mem (ix .rdx .rax)), .store (hdr kV) .rcx,
      .mov32 .rcx (.imm 16), .store (hdr kBits) .rcx] : List Instr)),
    .loop (seqs (mrWin mul)) .ne,
    .block [.mov .rax (.mem (hdr kWords)), .alu .test .rax (.reg .rax)]]) .ne] ++
  mrLast mul 1 ++ mrLast mul 2 ++ mrLast mul 3

/-- The table's start: the bases, read from the header before anything is
stored (`aXm` in `r8`, `aB` in `r9`, `aY` in `r10`, `aR1` in `r11`, `aT0` in
`r13`), the base of entry 2 into `kV` and the count 14 into `kBits`; then
`T_1 := b R mod c` (from `aXm`), `y := T_1` and `T_0 := R mod c`. -/
def tabHead : List (Prog isa) := [
  .block (([.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aXm))), .mov .r10 (.mem (hdr (sArr aY)))] :
    List Instr) ++ extBase aB .r9 ++ extBase aR1 .r11 ++ extBase aT0 .r13 ++ extBase (aT0 + 2) .rcx ++
    ([.store (hdr kV) .rcx, .mov32 .rax (.imm 14), .store (hdr kBits) .rax] : List Instr)),
  seqs [.block [.mov .rsi (.reg .r8), .mov .rbx (.reg .r9)], copyWords],
  seqs [.block [.mov .rsi (.reg .r8), .mov .rbx (.reg .r10)], copyWords],
  seqs [.block [.mov .rsi (.reg .r11), .mov .rbx (.reg .r13)], copyWords]]

/-- The table, from `b R mod c` in `aXm`: `tabHead`, then `y := y T_1` into
each entry from 2 to 15 (the entry's base in `kV`, the count in `kBits`);
then `y := 1`. -/
def tabBuild (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  seqs tabHead,
  .loop (seqs [mul aY aY aXm,
    .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY))), .mov .rbx (.mem (hdr kV))], copyWords,
    .block [.mov .rax (.mem (hdr kV)), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2), .alu .add .rdx (.reg .rdx),
      .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx), .store (hdr kV) .rax,
      .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]]) .ne,
  .block (([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] : List Instr) ++ extBase aR1 .rsi), copyWords]

/-- One round from a prepared Montgomery witness: table and fixed windows. -/
def preparedRound (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  tabBuild mul ++ mrExpLoop mul

end VG.Impl.RsaKeyGen.X86_64.Candidate
