module

public import VerifiedGarbage.Impl.Cast5.X86.Ssse3Wide

/-!
# CAST5's key expansion on x86 (32-bit) with its S-box look-ups by `pshufb`

Key expansion (RFC 2144 §2.4) makes 320 look-ups in S5 to S8: each of its 64
lines, which give a quadruple of `x` or `z` or a subkey, is the exclusive or
of five. The baseline (`Impl/Cast5/X86.lean`) makes them four at a time by a
scan of the static table `VG_CAST5_S5678_STEPS`, 80 scans a key.

A look-up by `pshufb` reads a plane's sixteen rows for the sixteen bytes of
a register at once (`Ssse3.lean`), and the sixteen bytes of `x`, or of `z`,
are one register. `lookup`, the internal function
`vg_cast5_key_lookup_ssse3`, gives S5 to S8 at all sixteen bytes of its
index vector: 64 doublewords, to the working space (`enAt`). It makes the
sixteen index vectors once, as the one-block look-ups do (`Ssse3.index`),
and each S-box is then a pass over its four planes' rows (`Ssse3.scan`, on
the planes of S5 to S8, which follow the constants in `VG_CAST5_SSSE3`) and
the planes' bytes to doublewords, as for sixteen blocks
(`Ssse3.Wide.entries`).

A line is then five loads (`lineE`). The lines that compute an array need
the bytes of the array itself as it grows, a quadruple a line, so each is
after a look-up of the array as it then is (`words`); the first of them,
and the four lines of the subkeys that follow an array, need only the bytes
of the array before, whole, so the look-up after an array's last line
serves the four subkeys and the first line of the next array: 33 look-ups a
key. An array's lines after the first also take one entry each of the array
before, which the look-ups of the growing array overwrite: those three are
saved first (`saveExtra`), where the baseline keeps a group's extra
look-ups.

The working space is the baseline's in its first 80 bytes (`x` at 16, `z` at
32, the three saved entries from 52, the saved registers from 64), the index
vectors where the one-block look-ups have them (272 to 527) and the entries
from 592 to 847. The look-ups' function keeps `ebx`, `ebp`, `esi`, `edi` and
`esp`, changes `eax`, `ecx`, `edx`, the flags and the XMM registers, and
uses eight bytes of stack with its call. No address and no branch depends
on the key.

`Fn.expandKey`: the function as emitted, with the working space, 848 bytes,
in a frame of its own of 880 bytes that it zeroes on return, so that the
working space is at a multiple of sixteen when `esp` was one at the call.
It does not use the `scratch` that its `Api` gives it, which is too small.
-/

@[expose] public section

namespace VG.Impl.Cast5.X86.Ssse3.Key

open VG.X86
open VG.Impl.Cast5
open VG.Impl.Cast5.X86
open VG.Impl.Cast5.X86.Ssse3 (tb x ld stx tbr tableName oM index scan)

/-- The internal function's name. -/
def lookName : String := "vg_cast5_key_lookup_ssse3"

/-- Where the look-ups leave `S_e` (`e` from 5 to 8) at byte `i` of their
index vector, in the working space. -/
def enAt (e i : Nat) : Nat := 592 + 64 * (e - 5) + 4 * i

/-! ## The look-ups -/

/-- The high nibbles of the bytes of `xmm0` to `xmm1`, the low ones to `xmm0`. -/
def nibbles : List Instr :=
  [tb .xmm2 oM, x .movdqa .xmm1 .xmm0, .xop (.shift .psrld .xmm1 4), x .pand .xmm1 .xmm2, x .pand .xmm0 .xmm2]

/-- `S_{5+j}` at the sixteen bytes, to the working space. -/
def sbox (j : Nat) : List Instr := scan (4 + j) ++ Wide.entries j

/-- `vg_cast5_key_lookup_ssse3`: for sixteen bytes in `xmm0`, S5 to S8 at
each of them, 64 doublewords in the working space at `esi` (`enAt`). -/
def lookup : Prog isa :=
  .seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1))
    (.block (([.mov tbr (.reg .eax)] : List Instr) ++ nibbles ++ (List.range 16).flatMap index ++ sbox 0 ++
      sbox 1 ++ sbox 2 ++ sbox 3))

/-! ## The lines -/

/-- The look-ups `lk` of the array `a` as it is. -/
def look (lk : Prog isa) (a : Arr) : Prog isa := .seq (.block [ld .xmm0 .esi (off a)]) lk

/-- `S8[d] ^ S7[c] ^ S6[b] ^ S5[a]` of a line's main bytes, from the
entries, into `eax`. -/
def mains (l : Line) : List Instr :=
  [.mov .eax (.mem (at_ .esi (enAt 8 l.main.2.2.2.2))), .alu .xor .eax (.mem (at_ .esi (enAt 7 l.main.2.2.1.2))),
   .alu .xor .eax (.mem (at_ .esi (enAt 6 l.main.2.1.2))), .alu .xor .eax (.mem (at_ .esi (enAt 5 l.main.1.2)))]

/-- A line's quadruple, big-endian, XORed in, if it has one. -/
def lineWord (l : Line) : List Instr :=
  match l.word with
  | some (a, q) => [.mov .ecx (.mem (at_ .esi (off a + 4 * q))), .bswap .ecx, .alu .xor .eax (.reg .ecx)]
  | none => []

/-- A line, into `eax`, with its extra look-up at the offset `xo` of the
working space. -/
def lineAt (l : Line) (xo : Nat) : List Instr :=
  mains l ++ ([.alu .xor .eax (.mem (at_ .esi xo))] : List Instr) ++ lineWord l

/-- A line whose extra look-up is among the entries. -/
def lineE (l : Line) : List Instr := lineAt l (enAt l.extra.1 l.extra.2.2)

/-- Line `k` of an array, whose extra look-up was saved. -/
def lineS (l : Line) (k : Nat) : List Instr := lineAt l (extraOff + 4 * k)

/-- The extra look-up of line `k` of `ls`, from the entries to its place. -/
def saveExtra (ls : List Line) (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esi (enAt (ls.getD k default).extra.1 (ls.getD k default).extra.2.2))),
   .store (at_ .esi (extraOff + 4 * k)) .eax]

/-- The four lines `ls` of the array `a`, after the look-ups of the other
array, whole; then the look-ups of `a`, whole. -/
def words (lk : Prog isa) (a : Arr) (ls : List Line) : Prog isa :=
  .seq (.block (saveExtra ls 1 ++ saveExtra ls 2 ++ saveExtra ls 3 ++ lineE (ls.getD 0 default) ++ storeQuad a 0))
    (.seq (look lk a) (.seq (.block (lineS (ls.getD 1 default) 1 ++ storeQuad a 1))
      (.seq (look lk a) (.seq (.block (lineS (ls.getD 2 default) 2 ++ storeQuad a 2))
        (.seq (look lk a) (.seq (.block (lineS (ls.getD 3 default) 3 ++ storeQuad a 3)) (look lk a)))))))

/-- The four subkeys of the lines `ls`, from `k0` on at `edi`. -/
def keys (ls : List Line) (k0 : Nat) : List Instr :=
  (List.range 4).flatMap fun k => lineE (ls.getD k default) ++ storeKey (k0 + k)

/-- One half of §2.4 (`Spec.Cast5.half`), after the look-ups of `x`, with
sixteen subkeys to `edi`, then `edi` on 64 bytes and the count of halves
left (`ebx`) down; it ends after the look-ups of the new `x`. -/
def half (lk : Prog isa) : Prog isa :=
  .seq (words lk .z zLines) (.seq (.block (keys aLines 0)) (.seq (words lk .x xLines)
    (.seq (.block (keys bLines 4)) (.seq (words lk .z zLines) (.seq (.block (keys cLines 8))
      (.seq (words lk .x xLines)
        (.block (keys dLines 12 ++ ([.alu .add .edi (imm 64), .alu .sub .ebx (imm 1)] : List Instr)))))))))

/-- Key expansion over the look-ups `lk`, with the baseline's arguments
(`key`, `key_len`, `schedule` and the working space, all on the stack), entry
and exit: `x` := the key padded with zeros (§2.5), its look-ups, then both
halves. -/
def expandKeyWith (lk : Prog isa) : Prog isa :=
  .seq (.block (([.mov .eax (.mem (at_ .esp 16))] : List Instr) ++ keySave ++ keySetup))
    (.seq (.loop (.block copyStep) .ne)
      (.seq (.block [.mov .edi (.reg .edx), .mov .ebx (imm 2)]) (.seq (look lk .x)
        (.seq (.loop (half lk) .ne) (.block keyRestore)))))

/-- Key expansion, with its working space of 848 bytes as the fourth
argument. -/
def expandKey : Prog isa := expandKeyWith (.call lookName lookup)

/-! ## The function as emitted -/

namespace Fn

/-- The doublewords of the 888 bytes of stack below `esp` that the residue
analysis finds the function may leave different in two runs: the look-ups'
call and its table's address, the frame's header, and the twelve bytes at
the frame's top that the working space does not reach. -/
def words : List Nat := [1, 2, 3, 4, 5, 6, 219, 220, 221]

/-- `Spec.Cast5.expandKeyApi`'s function as emitted: the working space is
its own, in a frame, and the caller's `scratch`, the fourth argument, is not
used. -/
def expandKey : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 888 words (Impl.StackScratch.X86.withStackScratchWiped 880 3 212 Key.expandKey)

end Fn

end VG.Impl.Cast5.X86.Ssse3.Key
