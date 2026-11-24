module

public import VerifiedGarbage.Impl.Aes.X86.Ctr32

/-!
# AES without AES-NI in SSE2 registers, eight blocks a pass, on x86 (32-bit)

`vg_aes_encrypt_blocks(schedule, rounds, data, n, scratch)`,
`vg_aes_decrypt_blocks` with the same arguments, and
`vg_aes_ctr32_to(schedule, rounds, counter, src, n, scratch, dst)`
(`Spec/Aes/Contract.lean`), cdecl: the arguments are at `[esp + 4]` and on.
SSE2 is this target's baseline. Constant-time AES, bitsliced as Käsper and Schwabe do ("Faster and
Timing-Attack Resistant AES-GCM", CHES 2009): the state of eight blocks is
eight 128-bit words, word `j` holding bit `j` of their 128 bytes, in slots
`0 … 7` (of 16 bytes) of the scratch buffer at `edi`. The bit of byte
`r + 4c` (row `r`, column `c`) of block `b` is bit `b` of byte `c` of dword
`2 (r mod 2) + ⌊r / 2⌋` (rows 0, 2, 1, 3, so that the odd rows are the high
quadword). So, without SSSE3's `pshufb`:

* ShiftRows (`shiftRows`) rotates the dwords of rows 1 and 3 by a byte, with
  `pshufd` (each of them twice in a quadword) and `psrlq`, and puts them
  back with `pshufd` and `punpcklqdq`; then those of rows 2 and 3 by two
  bytes, with `pshuflw` and `pshufhw`;
* MixColumns takes each word's rows one and two down with a `pshufd`;
* the S-box is `Circuit.sbox`, scheduled for eight registers and nine more
  slots, without the circuit's four complements (so it computes `sbox` XOR
  `{63}`, `Proof/Aes/X86/Sse`): they commute with ShiftRows and MixColumns
  (`{02}x + {03}x + x + x = x`), and the round keys are complemented instead.

The inverse cipher is FIPS 197's §5.3, on the round keys of the forward
cipher from the last down: InvShiftRows is ShiftRows' code rotating by three
bytes, the inverse S-box (`InvCircuit.lean`'s) leaves out a `{63}` before it
rather than after, and InvMixColumns is MixColumns of each column plus `{04}`
times itself XORed with itself two rows down.

`toBs` and `fromBs` transpose the bits of eight blocks (BearSSL's
`br_aes_ct64_ortho`, Thomas Pornin, MIT licence) and the bytes of each, by
columns in memory and by rows here. The first and the last round key are
XORed into the blocks themselves, so only the `rounds - 1` others are
bitsliced (`bsKey`): AES-256's fit in the scratch buffer, whose bytes are
laid out as:

* `[0, 272)`: the state and the S-box's spill slots;
* `[272, 288)`: the saved `ebx`, `esi`, `edi` and `ebp`;
* `[288, 304)`: the counter block: bytes 0–11 as three words, and the 32-bit
  counter as an integer;
* `[384, 2048)`: the bitsliced round keys, 128 bytes each, round key `j`
  (`1 ≤ j < rounds`) at `384 + 128 (j - 1)`.

A pass takes as many of the blocks left as it can, eight or fewer, and
computes eight either way. `esi` points to the round keys and `eax` counts
the rounds; `ecx` points to the round keys of the schedule. `ebx` (and `edx`,
in counter mode) point to the data, and `ebp` is the number of blocks left:
a pass changes them only to step to the next.

Every address is `esp` or a pointer plus a constant, or computed from the
pointers and `rounds`, and every branch depends only on those and `n`, so
only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.Aes.X86.Sse

open VG.X86 VG.Impl.Aes.X86

def X : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3 | 4 => .xmm4 | 5 => .xmm5 | 6 => .xmm6 | _ => .xmm7

/-! Short forms of the instructions, on register `n` and slot `k`. -/

def bin (op : XBinOp) (d s : Nat) : Instr := .xop (.bin op (X d) (X s))
def cp (d s : Nat) : Instr := bin .movdqa d s
def xr (d s : Nat) : Instr := bin .pxor d s
def an (d s : Nat) : Instr := bin .pand d s
def shq (op : XShiftOp) (d n : Nat) : Instr := .xop (.shift op (X d) (BitVec.ofNat 8 n))
def shd (d s n : Nat) : Instr := .xop (.pshufd (X d) (X s) (BitVec.ofNat 8 n))
def shl (d s n : Nat) : Instr := .xop (.pshuflw (X d) (X s) (BitVec.ofNat 8 n))
def shh (d s n : Nat) : Instr := .xop (.pshufhw (X d) (X s) (BitVec.ofNat 8 n))
def ldm (d : Nat) (b : Reg) (o : Nat) : Instr := .movdquLoad (X d) (at_ b o)
def stm (b : Reg) (o : Nat) (s : Nat) : Instr := .movdquStore (at_ b o) (X s)
def ld (d k : Nat) : Instr := ldm d sb (16 * k)
def st (k s : Nat) : Instr := stm sb (16 * k) s

/-- `d :=` the dword `v`, four times. -/
def mk32 (d : Nat) (v : BitVec 32) : List Instr := [movI .eax v, .xop (.movd (X d) .eax), shd d d 0]

/-! ## The S-box -/

/-- The slots of the state and the S-box. -/
def slots : Nat := 17

/-- `Circuit.sbox` without the complements, on the state in slots `0 … 7`
(`xᵢ`, `sᵢ` are bit `7 - i`), in place: gates and registers ordered to load
and store little. -/
def sboxCode : List Instr := [
  ld 7 2, ld 6 4, xr 6 7, ld 5 7, xr 5 7, ld 4 1, ld 3 7, xr 3 4, cp 2 3, xr 2 6, ld 1 3, xr 1 2, xr
  7 1, ld 0 6, xr 1 0, st 2 6, ld 6 0, xr 6 7, st 3 6, ld 6 5, xr 0 6, ld 6 4, st 5 5, ld 5 7, xr 5
  6, st 6 3, ld 3 0, xr 3 0, xr 4 3, st 1 2, ld 2 7, xr 2 3, xr 6 3, st 4 2, ld 2 0, an 2 6, st 8 6,
  cp 6 1, xr 6 5, st 9 1, cp 1 4, an 1 3, st 10 3, cp 3 7, xr 3 0, st 11 4, cp 4 5, an 4 6, xr 0 6,
  st 12 5, ld 5 0, xr 5 6, st 13 6, ld 6 1, an 6 7, st 14 7, ld 7 4, an 7 5, st 15 5, ld 5 6, an 5
  0, xr 7 5, xr 1 5, ld 5 5, an 5 3, xr 5 4, xr 7 5, xr 2 6, xr 2 5, ld 5 5, xr 5 3, xr 2 5, ld 5
  13, xr 5 3, st 16 3, ld 3 7, xr 3 0, xr 7 3, ld 3 2, an 3 5, xr 3 4, ld 4 5, st 7 5, ld 5 11, xr 5
  4, ld 4 3, an 4 5, xr 4 6, xr 1 3, ld 6 6, xr 6 0, xr 4 3, xr 1 6, cp 6 1, xr 6 7, ld 3 9, xr 4 3,
  cp 3 4, an 3 1, st 9 0, cp 0 2, xr 0 3, xr 3 7, an 0 6, xr 0 7, xr 4 2, cp 6 3, xr 6 0, an 7 6, xr
  1 0, xr 1 7, xr 7 3, an 3 4, xr 3 2, an 7 3, an 5 1, ld 2 15, an 2 3, xr 4 7, ld 7 8, an 7 0, ld 6
  3, an 6 1, st 3 6, ld 6 11, an 6 4, xr 7 5, xr 6 2, st 11 7, cp 7 4, xr 7 1, st 8 6, ld 6 10, an 6
  4, xr 4 3, xr 1 0, st 10 6, ld 6 0, an 6 0, xr 2 6, xr 0 3, st 0 2, ld 2 6, an 2 4, xr 6 2, st 6
  2, ld 2 9, an 4 2, ld 2 1, an 2 1, xr 2 5, ld 5 14, an 1 5, ld 5 12, an 5 0, st 12 2, ld 2 13, an
  2 0, xr 1 4, xr 0 7, xr 6 1, st 13 1, ld 1 7, an 1 0, xr 2 1, xr 4 2, ld 2 16, an 2 7, xr 1 2, ld
  2 2, an 0 2, ld 2 4, an 3 2, ld 2 5, an 7 2, xr 5 0, ld 2 10, xr 2 5, xr 3 6, xr 1 2, xr 3 1, xr 5
  6, xr 0 7, ld 7 8, ld 6 6, xr 6 7, xr 7 5, xr 6 1, ld 1 11, xr 1 3, ld 5 12, xr 5 2, ld 2 10, xr 2
  4, xr 3 2, xr 0 3, xr 4 5, ld 3 3, xr 3 5, ld 5 0, xr 5 3, st 0 7, ld 7 13, xr 7 3, xr 2 7, st 7
  4, st 6 2, st 5 0, st 4 7, st 3 5, st 2 1, st 1 6]

/-- The inverse S-box's circuit (`InvCircuit.lean`) without the complements,
as `sboxCode`: of the state XOR `{63}`. -/
def invSboxCode : List Instr := [
  ld 7 3, ld 6 4, xr 6 7, ld 5 4, ld 4 7, xr 4 5, ld 3 6, xr 3 4, ld 2 0, xr 2 7, xr 7 3, cp 1 5, xr
  1 2, ld 0 1, xr 0 1, xr 5 3, st 4 3, cp 3 4, xr 3 5, st 1 1, cp 1 3, xr 1 0, st 3 1, ld 1 2, st 0
  3, ld 3 7, xr 3 1, cp 1 7, xr 1 0, st 2 0, cp 0 4, xr 0 1, st 7 4, cp 4 5, xr 4 2, st 6 2, ld 2 5,
  xr 2 6, st 5 1, ld 1 1, st 8 7, ld 7 0, an 7 1, xr 3 0, st 9 0, cp 0 5, an 0 4, st 10 5, cp 5 6,
  an 5 3, st 11 6, cp 6 4, xr 6 3, xr 0 5, st 12 4, ld 4 3, xr 4 2, st 13 3, ld 3 8, an 3 6, xr 1 4,
  st 14 6, ld 6 2, an 6 1, xr 3 5, ld 5 3, an 5 4, xr 5 6, xr 7 6, xr 7 3, ld 6 2, xr 6 1, xr 5 0,
  xr 5 2, xr 7 6, ld 6 14, xr 6 1, ld 2 5, an 2 6, st 15 1, ld 1 4, st 16 6, ld 6 7, an 6 1, xr 6 2,
  xr 6 3, ld 3 13, ld 1 11, xr 1 3, xr 3 4, xr 6 1, ld 1 9, an 1 3, xr 1 2, xr 1 0, ld 0 6, xr 1 0,
  cp 0 6, an 0 7, cp 2 1, xr 2 0, xr 6 1, st 6 4, cp 4 7, xr 4 5, xr 0 5, an 2 4, xr 2 5, cp 4 0, xr
  4 2, an 5 4, xr 7 2, xr 7 5, ld 4 7, an 4 7, xr 5 0, an 0 6, an 3 2, xr 0 1, an 5 0, ld 1 4, an 1
  7, xr 4 3, xr 6 5, cp 5 2, xr 5 7, st 4 3, ld 3 9, an 3 2, xr 7 6, st 9 1, ld 1 16, an 1 5, st 16
  1, ld 1 6, an 1 0, st 6 1, ld 1 5, an 5 1, ld 1 10, an 1 7, xr 1 5, xr 5 4, st 10 5, ld 5 3, an 5
  0, xr 2 0, st 3 5, ld 5 13, an 5 2, st 13 4, ld 4 11, an 4 2, xr 1 3, xr 5 4, xr 0 6, st 11 3, ld
  3 0, an 3 6, xr 4 1, xr 2 7, st 0 4, ld 4 2, an 4 0, xr 5 4, st 2 4, ld 4 12, an 7 4, xr 5 3, ld 4
  15, an 0 4, ld 4 8, an 4 2, xr 5 4, xr 5 7, xr 4 1, ld 1 14, an 2 1, ld 1 1, an 6 1, xr 0 5, xr 6
  0, ld 1 16, xr 1 5, xr 2 6, xr 7 2, ld 2 9, xr 2 6, ld 6 13, xr 6 2, ld 5 3, xr 5 6, ld 6 11, xr 6
  5, ld 5 4, xr 5 1, st 4 5, ld 5 6, xr 5 0, ld 0 2, xr 0 6, xr 0 4, xr 3 6, xr 1 5, xr 4 7, xr 2 1,
  xr 1 4, ld 4 10, xr 4 1, st 7 5, st 6 0, st 5 3, st 3 4, st 2 2, st 1 7]

/-! ## ShiftRows -/

/-- The odd rows of the word in register `x` rotate by `n` bits (register `t`
is clobbered), then rows 2 and 3 by two bytes. -/
def rotRows (n x t : Nat) : List Instr :=
  [shd t x 0xFA, shq .psrlq t n, shd t t 0x88, bin .punpcklqdq x t, shl x x 0xB4, shh x x 0xB4]

/-- ShiftRows: the odd rows by a byte. -/
def shiftRows : Nat → Nat → List Instr := rotRows 8

/-- InvShiftRows: the odd rows by three bytes. -/
def invShiftRows : Nat → Nat → List Instr := rotRows 24

/-! ## Between blocks and the bitsliced state -/

/-- A delta swap between registers `a` and `b` (`t` is clobbered): exchanges
the bits of `b` in the mask `m` with the bits of `a` `s` places above them. -/
def swapN (a b s m t : Nat) : List Instr :=
  [cp t a, shq .psrlq t s, xr t b, an t m, xr b t, shq .psllq t s, xr a t]

/-- The mask of `byteSwap`: bytes 1 and 3 of each quadword. -/
def mkBytes (d : Nat) : List Instr := [movI .eax 0xFF00FF00, .xop (.movd (X d) .eax), bin .punpcklqdq d d]

/-- Exchanges bytes 1 and 4, and 3 and 6, of each quadword. -/
def byteSwap (x m t : Nat) : List Instr :=
  [cp t x, shq .psrlq t 24, xr t x, an t m, xr x t, shq .psllq t 24, xr x t]

/-- The bytes of the block in `x`, from columns to rows (0, 2, 1, 3). -/
def toRows (x m t : Nat) : List Instr := byteSwap x m t ++ [shd x x 0xD8, shl x x 0xD8, shh x x 0xD8]

/-- The inverse of `toRows`. -/
def toCols (x m t : Nat) : List Instr := [shl x x 0xD8, shh x x 0xD8, shd x x 0xD8] ++ byteSwap x m t

/-- The bits of slots `0 … 7` transposed, in two halves, each loaded by
`load` into registers `0 … 3`. -/
def ortho (load : Nat → List Instr) : List Instr :=
  let half (h : Nat) : List Instr := load h ++
    mk32 6 0x55555555 ++ swapN 0 1 1 6 7 ++ swapN 2 3 1 6 7 ++
    mk32 6 0x33333333 ++ swapN 0 2 2 6 7 ++ swapN 1 3 2 6 7
  half 4 ++ (List.range 4).map (fun k => st (4 + k) k) ++ half 0 ++ mk32 6 0x0F0F0F0F ++
    (List.range 4).flatMap fun k => [ld 4 (4 + k)] ++ swapN k 4 4 6 7 ++ [st k k, st (4 + k) 4]

/-- AddRoundKey of the round key at `ecx`, changed by `c` in register 5, to
the eight blocks in slots `0 … 7`, bitsliced. -/
def toBsWith (c : List Instr) : List Instr :=
  ortho fun h => [ldm 5 .ecx 0] ++ c ++ mkBytes 6 ++
    (List.range 4).flatMap fun k => [ld k (h + k), xr k 5] ++ toRows k 6 7

/-- The rows of eight blocks moved by `rows`, and AddRoundKey of the round
key at `ecx`, changed by `c` in register 5; the blocks in slots `0 … 7`. -/
def fromBsWith (rows : Nat → Nat → List Instr) (c : List Instr) : List Instr :=
  ortho (fun h => (List.range 4).flatMap fun k => [ld k (h + k)] ++ rows k 7) ++
  [ldm 5 .ecx 0] ++ c ++ mkBytes 6 ++
  (List.range 8).flatMap fun k => [ld 0 k] ++ toCols 0 6 7 ++ [xr 0 5, st k 0]

/-- `{63}` XORed into each byte of register 5. -/
def xor63 : List Instr := mk32 7 0x63636363 ++ [xr 5 7]

/-- AddRoundKey of the first round key. -/
def toBs : List Instr := toBsWith []

/-- The last round, from the S-box: ShiftRows and AddRoundKey, XORed with the
`{63}` in each byte that the S-box leaves out. -/
def fromBs : List Instr := fromBsWith shiftRows xor63

/-- AddRoundKey of the last round key, XORed with the `{63}` that the inverse
S-box leaves out. -/
def invToBs : List Instr := toBsWith xor63

/-- The inverse cipher's last round, from the inverse S-box. -/
def invFromBs : List Instr := fromBsWith invShiftRows []

/-! ## The rounds -/

/-- The register pointing to the bitsliced round keys. -/
def kp : Reg := .esi

/-- ShiftRows of word `j` in `x`, and MixColumns' terms of it alone: `x`
holds `uⱼ = aⱼ ⊕ a'ⱼ` (`a'` one row down), and `r` holds `a'ⱼ` XOR `uⱼ` two
rows down. -/
def mcPlane (j x r : Nat) : List Instr :=
  [ld x j] ++ shiftRows x 3 ++ [shd r x 0x1E, xr x r, shd 3 x 0xB1, xr r 3]

/-- The rest of a middle round, from the S-box: ShiftRows, MixColumns (word
`j` is `uⱼ₋₁ ⊕ [j ∈ {0, 1, 3, 4}] u₇` XOR what `mcPlane` leaves) and
AddRoundKey with the bitsliced round key at `kp`. -/
def linear : List Instr :=
  [ld 6 7] ++ shiftRows 6 5 ++ [shd 7 6 0x1E, xr 6 7, shd 5 6 0xB1, xr 7 5] ++
  ((List.range 7).flatMap fun j =>
    let x := j % 2
    mcPlane j x 2 ++ (if j = 0 then [] else [xr 2 (1 - x)]) ++
      (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then [xr 2 6] else []) ++
      [ldm 3 kp (16 * j), xr 2 3, st j 2]) ++
  [xr 7 0, ldm 3 kp 112, xr 7 3, st 7 7]

/-- Word `j` of the state after InvShiftRows and AddRoundKey with the
bitsliced round key at `kp`, in slot `j`, and XOR itself two rows down (`vⱼ`)
in register `v`. -/
def invPlane (j v : Nat) : List Instr :=
  [ld 0 j] ++ invShiftRows 0 1 ++ [ldm 1 kp (16 * j), xr 0 1, st j 0, shd v 0 0xB1, xr v 0]

/-- The words `vᵢ` of `{04}` times the state XOR itself two rows down. -/
def invWords : Nat → List Nat
  | 0 => [6] | 1 => [6, 7] | 2 => [0, 7] | 3 => [1, 6] | 4 => [2, 6, 7] | 5 => [3, 7] | 6 => [4] | _ => [5]

/-- Word `j` with `{04}` times the state XOR itself two rows down added: InvMixColumns
is that, and MixColumns. -/
def invPre (j x t : Nat) : List Instr :=
  [ld x j] ++ (invWords j).flatMap fun i => if i < 6 then [ld t (8 + i), xr x t] else [xr x i]

/-- `mcPlane`, of `invPre`'s word. -/
def invMcPlane (j x r : Nat) : List Instr :=
  invPre j x 3 ++ [shd r x 0x1E, xr x r, shd 3 x 0xB1, xr r 3]

/-- The rest of a middle round of the inverse cipher, from the inverse S-box:
InvShiftRows, AddRoundKey with the bitsliced round key at `kp` and
InvMixColumns. -/
def invLinear : List Instr :=
  ((List.range 6).flatMap fun j => invPlane j 2 ++ [st (8 + j) 2]) ++ invPlane 6 6 ++ invPlane 7 7 ++
  invPre 7 5 3 ++ [shd 4 5 0x1E, xr 5 4, shd 3 5 0xB1, xr 4 3] ++
  ((List.range 7).flatMap fun j =>
    let x := j % 2
    invMcPlane j x 2 ++ (if j = 0 then [] else [xr 2 (1 - x)]) ++
      (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then [xr 2 5] else []) ++ [st j 2]) ++
  [xr 4 0, st 7 4]

/-- The offset of the bitsliced round keys in the scratch buffer. -/
def keysOff : Nat := 384

/-- A middle round, with `kp` at its round key; `eax` counts the rounds left. -/
def roundBody : List Instr := sboxCode ++ linear ++ [addI kp 128, subI .eax 1]

/-- `kp :=` the first bitsliced round key, and `eax :=` how many there are. -/
def roundsStart : List Instr :=
  [movR kp sb, addI kp (BitVec.ofNat 32 keysOff), .mov .eax (.mem (argOp 1)), subI .eax 1]

/-- `ecx :=` the last round key of the schedule, from the first. -/
def lastKeyPtr : List Instr := [.mov .eax (.mem (argOp 1))] ++ dbl .eax 4 ++ [addR .ecx .eax]

/-- Encrypt the eight blocks in slots `0 … 7`. -/
def encrypt8 : Prog isa :=
  .seq (.block ([.mov .ecx (.mem (argOp 0))] ++ toBs ++ roundsStart))
    (.seq (.loop (.block roundBody) .ne) (.block (sboxCode ++ lastKeyPtr ++ fromBs)))

/-! ## The inverse cipher -/

/-- A middle round of the inverse cipher, with `kp` at the round key after
its own; `eax` counts the rounds left. -/
def invRoundBody : List Instr := [subI kp 128] ++ invSboxCode ++ invLinear ++ [subI .eax 1]

/-- `kp :=` the end of the bitsliced round keys, and `eax :=` how many there are. -/
def invRoundsStart : List Instr :=
  [.mov kp (.mem (argOp 1)), .mov .eax (.mem (argOp 1))] ++ dbl kp 7 ++
    [addR kp sb, addI kp (BitVec.ofNat 32 (keysOff - 128)), subI .eax 1]

/-- Decrypt the eight blocks in slots `0 … 7`. -/
def decrypt8 : Prog isa :=
  .seq (.block ([.mov .ecx (.mem (argOp 0))] ++ lastKeyPtr ++ invToBs ++ invRoundsStart))
    (.seq (.loop (.block invRoundBody) .ne)
      (.block (invSboxCode ++ [.mov .ecx (.mem (argOp 0))] ++ invFromBs)))

/-! ## The round keys -/

/-- The bits of register `x`, the same in `x` and the new register `b`,
exchanged as `swapN` would: the even words of the transposition in `x`, the
odd in `b`. -/
def split (x b s m : Nat) : List Instr :=
  [cp 7 x, shq .psrlq 7 s, xr 7 x, an 7 m, cp b x, xr b 7, shq .psllq 7 s, xr x 7]

/-- The round key at `ecx`, as eight identical blocks bitsliced, XORed with
`{63}` in each byte, to the 128 bytes at `kp`. -/
def bsKey : List Instr :=
  [ldm 0 .ecx 0] ++ mk32 7 0x63636363 ++ [xr 0 7] ++ mkBytes 6 ++ toRows 0 6 7 ++
  mk32 4 0x55555555 ++ mk32 5 0x33333333 ++ mk32 6 0x0F0F0F0F ++ split 0 1 1 4 ++
  [1, 0].flatMap fun w => split w 2 2 5 ++
    split 2 3 4 6 ++ [stm kp (16 * (w + 2)) 2, stm kp (16 * (w + 6)) 3] ++
    split w 3 4 6 ++ [stm kp (16 * w) w, stm kp (16 * (w + 4)) 3]

/-- `ecx :=` round key 1 of the schedule, `edx :=` how many to bitslice, `kp :=` where to. -/
def keySetup : List Instr :=
  [.mov .ecx (.mem (argOp 0)), addI .ecx 16, .mov .edx (.mem (argOp 1)), subI .edx 1,
    movR kp sb, addI kp (BitVec.ofNat 32 keysOff)]

/-- Bitslice a round key, and on to the next (ZF is set after the last). -/
def keyBody : List Instr := bsKey ++ [addI .ecx 16, addI kp 128, subI .edx 1]

/-- Bitslice round keys `1 … rounds - 1`. -/
def keys : Prog isa := .seq (.block keySetup) (.loop (.block keyBody) .ne)

/-! ## Entry and exit -/

/-- The callee-saved registers, and their offsets in the scratch buffer. -/
def savedRegs : List (Reg × Nat) := [(.ebx, 272), (.esi, 276), (.edi, 280), (.ebp, 284)]

/-- Load the scratch pointer (argument `k`) into `edi`, saving the registers. -/
def saveRegs (k : Nat) : List Instr :=
  ([.mov .eax (.mem (argOp k))] : List Instr) ++ savedRegs.map (fun (r, d) => .store (at_ .eax d) r) ++
    [movR .edi .eax]

/-- Restore the registers (`edi`, the base, last). -/
def restoreRegs : List Instr :=
  [.mov .ebx (.mem (at_ .edi 272)), .mov .esi (.mem (at_ .edi 276)), .mov .ebp (.mem (at_ .edi 284)),
   .mov .edi (.mem (at_ .edi 280))]

/-- The offsets of the counter block's words, and of the counter as an integer. -/
def cwOff (w : Nat) : Nat := 288 + 4 * w
def cNum : Nat := 300

/-- `ecx :=` how many of the `ebp` blocks left this pass takes. -/
def takeCount : Prog isa :=
  .seq (.block [.alu .cmp .ebp (.imm 8)]) (.ite .ae (.block [movI .ecx 8]) (.block [movR .ecx .ebp]))

/-- Copy a block from `src` to `dst`, and on to the next (ZF is set after the last of `ecx`). -/
def copyBody (src dst : Reg) : List Instr :=
  [ldm 0 src 0, stm dst 0 0, addI src 16, addI dst 16, subI .ecx 1]

/-! ## Whole blocks -/

/-- `ebx :=` the data pointer, and `ebp :=` the count (ZF is set if it is zero). -/
def blocksSetup : List Instr :=
  [.mov .ebx (.mem (argOp 2)), .mov .ebp (.mem (argOp 3)), .alu .test .ebp (.reg .ebp)]

/-- Copy the blocks of a pass from the data to the slots. -/
def copyIn : Prog isa :=
  .seq (.block [movR .esi .ebx, movR .edx .edi]) (.seq takeCount (.loop (.block (copyBody .esi .edx)) .ne))

/-- Copy the blocks of a pass back, and on to the next ones (ZF is set when none are left). -/
def copyOut : Prog isa :=
  .seq (.block [movR .edx .edi]) (.seq takeCount
    (.seq (.block [subR .ebp .ecx]) (.seq (.loop (.block (copyBody .edx .ebx)) .ne)
      (.block [.alu .test .ebp (.reg .ebp)]))))

/-- A pass of eight blocks or fewer, through `crypt8`. -/
def blockGroup (crypt8 : Prog isa) : Prog isa := .seq copyIn (.seq crypt8 copyOut)

/-- The whole function, around `crypt8`. -/
def blocks (crypt8 : Prog isa) : Prog isa :=
  .seq (.block (saveRegs 4))
    (.seq keys
      (.seq (.block blocksSetup)
        (.seq (.ite .e (.block []) (.loop (blockGroup crypt8) .ne)) (.block restoreRegs))))

/-- `vg_aes_encrypt_blocks`. -/
def encryptBlocks : Prog isa := blocks encrypt8

/-- `vg_aes_decrypt_blocks`. -/
def decryptBlocks : Prog isa := blocks decrypt8

/-! ## Counter mode -/

/-- Copy the counter block (`counter`) to its words, and write the final
counter `(c + n) mod 2³²` back. -/
def ctrSetup : List Instr :=
  [.mov .ecx (.mem (argOp 2)),
   .mov .eax (.mem (at_ .ecx 0)), .store (at_ .edi (cwOff 0)) .eax,
   .mov .eax (.mem (at_ .ecx 4)), .store (at_ .edi (cwOff 1)) .eax,
   .mov .eax (.mem (at_ .ecx 8)), .store (at_ .edi (cwOff 2)) .eax,
   .mov .eax (.mem (at_ .ecx 12)), .bswap .eax, .store (at_ .edi cNum) .eax,
   .alu .add .eax (.mem (argOp 4)), .bswap .eax, .store (at_ .ecx 12) .eax]

/-- `edx :=` the data pointer, `ebx :=` the destination's, and `ebp :=` the
count (ZF is set if it is zero). -/
def ctrPtrs : List Instr :=
  [.mov .edx (.mem (argOp 3)), .mov .ebx (.mem (argOp 6)), .mov .ebp (.mem (argOp 4)),
    .alu .test .ebp (.reg .ebp)]

/-- `xmm1 :=` bytes 0–11 of the counter block, and zeros; `esi :=` the counter `c`. -/
def ctrLoad : List Instr :=
  [ldm 1 .edi (cwOff 0), shq .pslldq 1 4, shq .psrldq 1 4, .mov .esi (.mem (at_ .edi cNum))]

/-- Counter block `c + b` to slot `b`. -/
def ctrBlock (b : Nat) : List Instr :=
  [movR .eax .esi, addI .eax (BitVec.ofNat 32 b), .bswap .eax, .xop (.movd (X 0) .eax), shq .pslldq 0 12,
    bin .por 0 1, st b 0]

/-- Counter blocks `c … c + 7` to the slots, and `c := c + 8`. -/
def ctrBlocks : List Instr :=
  ctrLoad ++ (List.range 8).flatMap ctrBlock ++ [addI .esi 8, .store (at_ .edi cNum) .esi]

/-- XOR a slot (`esi`) with its block of the data (`edx`) to the destination
(`ebx`), and on to the next (ZF is set after the last of `ecx`). -/
def xorBody : List Instr :=
  [ldm 0 .esi 0, ldm 1 .edx 0, xr 0 1, stm .ebx 0 0, addI .esi 16, addI .edx 16, addI .ebx 16, subI .ecx 1]

/-- XOR the keystream into the blocks of a pass, and on to the next ones (ZF
is set when none are left). -/
def xorOut : Prog isa :=
  .seq (.block [movR .esi .edi]) (.seq takeCount
    (.seq (.block [subR .ebp .ecx]) (.seq (.loop (.block xorBody) .ne) (.block [.alu .test .ebp (.reg .ebp)]))))

/-- A pass of eight blocks or fewer. -/
def group : Prog isa := .seq (.block ctrBlocks) (.seq encrypt8 xorOut)

/-- `vg_aes_ctr32_to`. -/
def ctr32To : Prog isa :=
  .seq (.block (saveRegs 5 ++ ctrSetup))
    (.seq keys
      (.seq (.block ctrPtrs)
        (.seq (.ite .e (.block []) (.loop group .ne)) (.block restoreRegs))))

end VG.Impl.Aes.X86.Sse
