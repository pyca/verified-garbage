module

public import VerifiedGarbage.TCB.X86.Isa

/-!
# ChaCha20 block function: x86 (32-bit) implementation

`vg_chacha20_block(state, buf)`, cdecl: the arguments are at `[esp + 4]` and
`[esp + 8]`.

With only seven usable registers, the state lives in memory:
* `buf[0..64)` is the working state: the input state is copied there, each
  quarter round loads its four words into `eax, ebx, ecx, edx` and stores them
  back, and finally the input state (re-read from `state`) is added in place,
  leaving the result.
* `esi` points to `buf` and `edi` to `state`; both are loaded from their
  argument slots, and `buf[64..76)` holds the saved `ebx, esi, edi`.
* Every address is `esp`, `esi`, `edi` or `eax` (while it holds `buf`) plus a
  constant, and there are no branches, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- The quarter round (RFC 8439 §2.1) on `eax, ebx, ecx, edx`. A rotation left
by `k` is a rotation right by `32 - k`. -/
def qr : List Instr := [
  .alu .add .eax (.reg .ebx), .alu .xor .edx (.reg .eax), .shift .ror .edx 16,
  .alu .add .ecx (.reg .edx), .alu .xor .ebx (.reg .ecx), .shift .ror .ebx 20,
  .alu .add .eax (.reg .ebx), .alu .xor .edx (.reg .eax), .shift .ror .edx 24,
  .alu .add .ecx (.reg .edx), .alu .xor .ebx (.reg .ecx), .shift .ror .ebx 25]

/-- `QUARTERROUND(x, y, z, w)` (RFC 8439 §2.2) on the words in `buf`. -/
def quarter (x y z w : Nat) : Prog isa := .block (
  ([.mov .eax (.mem (at_ .esi (4 * x))), .mov .ebx (.mem (at_ .esi (4 * y))),
   .mov .ecx (.mem (at_ .esi (4 * z))), .mov .edx (.mem (at_ .esi (4 * w)))] : List Instr) ++ qr ++
  ([.store (at_ .esi (4 * x)) .eax, .store (at_ .esi (4 * y)) .ebx,
   .store (at_ .esi (4 * z)) .ecx, .store (at_ .esi (4 * w)) .edx] : List Instr))

/-- `inner_block` (RFC 8439 §2.3.1): a column round and a diagonal round. -/
def doubleRound : Prog isa :=
  .seq (quarter 0 4 8 12) <| .seq (quarter 1 5 9 13) <| .seq (quarter 2 6 10 14) <|
  .seq (quarter 3 7 11 15) <| .seq (quarter 0 5 10 15) <| .seq (quarter 1 6 11 12) <|
  .seq (quarter 2 7 8 13) (quarter 3 4 9 14)

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) doubleRound

/-- Load the pointers (into `eax` and `ecx`), save `ebx, esi, edi` in `buf`,
and move the pointers to `esi` and `edi`. -/
def save : List Instr := [
  .mov .eax (.mem (at_ .esp 8)), .mov .ecx (.mem (at_ .esp 4)), .store (at_ .eax 64) .ebx,
  .store (at_ .eax 68) .esi, .store (at_ .eax 72) .edi, .mov .esi (.reg .eax),
  .mov .edi (.reg .ecx)]

/-- Copy word `k` of the input state to `buf`. -/
def copyWord (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi (4 * k))), .store (at_ .esi (4 * k)) .eax]

def copy : List Instr := (List.range 16).flatMap copyWord

/-- Add word `k` of the input state into `buf`. -/
def addWord (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esi (4 * k))), .alu .add .eax (.mem (at_ .edi (4 * k))),
   .store (at_ .esi (4 * k)) .eax]

def finish : List Instr := (List.range 16).flatMap addWord

/-- Restore `ebx, esi, edi` (via `eax`). -/
def restore : List Instr := [
  .mov .eax (.reg .esi), .mov .ebx (.mem (at_ .eax 64)), .mov .esi (.mem (at_ .eax 68)),
  .mov .edi (.mem (at_ .eax 72))]

def block : Prog isa :=
  .seq (.block (save ++ copy)) (.seq (rounds 10) (.block (finish ++ restore)))

/-! ## SSE2: the quarter round on four blocks at once, for `vg_chacha20_xor` -/

/-- `op dst, src` on XMM registers. -/
def xb (op : XBinOp) (d r : XReg) : Instr := .xop (.bin op d r)

/-- `x` rotated left by `k` (`0 < k < 32`) in each doubleword, through `xmm7`. -/
def vrot (x : XReg) (k : Nat) : List Instr :=
  [xb .movdqa .xmm7 x, .xop (.shift .pslld x (BitVec.ofNat 8 k)),
   .xop (.shift .psrld .xmm7 (BitVec.ofNat 8 (32 - k))), xb .por x .xmm7]

/-- The quarter round (RFC 8439 §2.1) on each doubleword of `a, b, c, d`,
with `xmm7` as scratch (for the four-block code of `vg_chacha20_xor`): a
rotation by 16 swaps the words of each doubleword (`pshuflw`, `pshufhw`), the
others are two shifts and an `or`. -/
def vqr (a b c d : XReg) : List Instr :=
  [xb .paddd a b, xb .pxor d a, .xop (.pshuflw d d 0xb1), .xop (.pshufhw d d 0xb1),
   xb .paddd c d, xb .pxor b c] ++ vrot b 12 ++
  [xb .paddd a b, xb .pxor d a] ++ vrot d 8 ++
  [xb .paddd c d, xb .pxor b c] ++ vrot b 7

/-- Where `vqr3` finds its `pshufb` controls in `buf` (through `edi`). -/
def rot16Off : Nat := 288
def rot8Off : Nat := 304

/-- The `pshufb` controls that rotate each doubleword left by 16 and by 8
bits (byte `j` of a doubleword from byte `(j + 2) % 4`, resp. `(j + 3) % 4`),
as the words stored at `buf + rot16Off` and `buf + rot8Off`, and where. -/
def maskWords : List (BitVec 32 × Nat) :=
  [(0x01000302, 288), (0x05040706, 292), (0x09080b0a, 296), (0x0d0c0f0e, 300),
   (0x02010003, 304), (0x06050407, 308), (0x0a09080b, 312), (0x0e0d0c0f, 316)]

/-- The quarter round (RFC 8439 §2.1) on each doubleword of `a, b, c, d`
with SSSE3, with `xmm7` as scratch: the rotations by 16 and 8 are `pshufb`
with the controls at `buf + rot16Off` and `buf + rot8Off`, loaded into
`xmm7`; the others are two shifts and an `or`. -/
def vqr3 (a b c d : XReg) : List Instr :=
  [xb .paddd a b, xb .pxor d a, .movdquLoad .xmm7 (at_ .edi rot16Off), xb .pshufb d .xmm7,
   xb .paddd c d, xb .pxor b c] ++ vrot b 12 ++
  [xb .paddd a b, xb .pxor d a, .movdquLoad .xmm7 (at_ .edi rot8Off), xb .pshufb d .xmm7,
   xb .paddd c d, xb .pxor b c] ++ vrot b 7

/-- Stores the controls of `vqr3` in `buf` (`edi`), through `eax`. -/
def masks : List Instr := maskWords.flatMap fun p => [.mov .eax (.imm p.1), .store (at_ .edi p.2) .eax]

end VG.Impl.ChaCha20.X86
