import VerifiedGarbage.Impl.Cast5.Tables
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Impl.Cast5.Lines

/-!
# CAST5 on baseline 32-bit x86

As on x86-64 (`Impl/Cast5/X86_64.lean`), a lookup in an S-box never uses a
secret as an address: the four lookups of a round function are made at once by
a *scan* of the static table `VG_CAST5_S1234` (or `VG_CAST5_S5678` in key
expansion), 256 entries of 16 bytes, in SSE2 registers: the indices are the
four dword lanes of `xmm0`, and every entry is loaded, in order, ANDed with a
mask that is all ones in the lanes whose index it is and ORed into the result,
`xmm1`. The model's SSE2 has no `pcmpeqd`, so the mask of entry `j` is built
from `d = idx ^ j`, which is below 256: `d - 1` shifted right by 8 is
`0x00FFFFFF` if `d = 0` and `0` otherwise, and ORed with itself shifted left
by 8 it is all ones or nothing.

The rotation by the secret amount `Kr` (§2.2) is five rotations by 1, 2, 4, 8
and 16, each kept or not by a mask made from a bit of `Kr` (`rotate`).

With seven registers, the working space (`esi`) holds the public state: the
subkeys' pointer, the counts, the arguments. The scan obtains its table's
address itself, in a four-byte `symPush` frame.
-/

namespace VG.Impl.Cast5.X86

open VG.X86

/-- `[base + offset]`. -/
def at_ (base : Reg) (offset : Nat) : MemOp := { base, disp := offset }

/-- An immediate. -/
def imm (n : Nat) : Src := .imm (BitVec.ofNat 32 n)

/-! ## The scan -/

/-- Entry `e` of the four at `ecx`: its mask, from the indices in `xmm0`, the
entry's number in every lane of `xmm2` and all ones in `xmm6`, ANDed with it
and ORed into `xmm1`; then the next number (`xmm3` is one in every lane). -/
def scanEntry (e : Nat) : List Instr :=
  [.xop (.bin .movdqa .xmm4 .xmm0), .xop (.bin .pxor .xmm4 .xmm2), .xop (.bin .paddd .xmm4 .xmm6),
   .xop (.shift .psrld .xmm4 8), .xop (.bin .movdqa .xmm7 .xmm4), .xop (.shift .pslld .xmm7 8),
   .xop (.bin .por .xmm4 .xmm7),
   .movdquLoad .xmm5 (at_ .ecx (16 * e)), .xop (.bin .pand .xmm5 .xmm4),
   .xop (.bin .por .xmm1 .xmm5), .xop (.bin .paddd .xmm2 .xmm3)]

/-- Four entries, then on to the next four (ZF is set after the last). -/
def scanBody : List Instr :=
  (List.range 4).flatMap scanEntry ++ ([.alu .add .ecx (imm 64), .alu .sub .edx (imm 1)] : List Instr)

/-- The setup of a scan, the table's address in `eax`: the table in `ecx`, 64
groups of four entries to go in `edx`, nothing found yet, entry 0 next, one
and all ones in every lane of `xmm3` and `xmm6`. -/
def scanStart : List Instr :=
  [.mov .ecx (.reg .eax), .mov .edx (imm 64), .xop (.bin .pxor .xmm1 .xmm1),
   .xop (.bin .pxor .xmm2 .xmm2), .mov .eax (imm 1), .xop (.movd .xmm3 .eax),
   .xop (.pshufd .xmm3 .xmm3 0), .mov .eax (imm 0xFFFFFFFF), .xop (.movd .xmm6 .eax),
   .xop (.pshufd .xmm6 .xmm6 0)]

/-- The table `sym` at the indices in the lanes of `xmm0` (each less than
256), into the lanes of `xmm1`. Clobbers `eax`, `ecx`, `edx`, `xmm1`–`xmm7`
but `xmm0`, the flags, and the word below `esp`. -/
def scan (sym : String) : Prog isa :=
  .seq (.frame (.symPush .eax sym) (.block []) (.pop .ecx 1))
    (.seq (.block scanStart) (.loop (.block scanBody) .ne))

/-- `xmm0` := the dwords `a, b, c, d` of four registers. Clobbers `xmm4` and
`xmm5`. -/
def lanes (a b c d : Reg) : List Instr :=
  [.xop (.movd .xmm0 a), .xop (.movd .xmm4 b), .xop (.bin .punpckldq .xmm0 .xmm4),
   .xop (.movd .xmm4 c), .xop (.movd .xmm5 d), .xop (.bin .punpckldq .xmm4 .xmm5),
   .xop (.bin .punpcklqdq .xmm0 .xmm4)]

/-! ## Encryption and decryption

The working space (`esi`): the scan's result at 0–15, the callee-saved
registers at `savedOff`, and the public slots below. -/

def schedOff : Nat := 48
def roundsOff : Nat := 52
def dataOff : Nat := 56
def nOff : Nat := 60
/-- The subkeys of the next round, `Kmᵢ` (`Krᵢ` is 64 bytes on). -/
def kpOff : Nat := 64
/-- The count of groups of three rounds left. -/
def gcOff : Nat := 68
def savedOff : Nat := 32

/-- One of the five steps of the rotation of `eax` left by the low 5 bits of
`ecx` (shifted right by `b` so far): rotate by `2 ^ b` if bit 0 of `ecx` is
set. `edx` := 0 if it is, all ones if not; the rotation is in `edi`. -/
def rotateStep (b : Nat) : List Instr :=
  ([.mov .edx (.reg .ecx), .alu .and .edx (imm 1), .alu .sub .edx (imm 1),
   .mov .edi (.reg .eax), .shift .ror .edi (32 - 2 ^ b),
   .alu .xor .eax (.reg .edi), .alu .and .eax (.reg .edx), .alu .xor .eax (.reg .edi)] : List Instr) ++
  (if b < 4 then [.shift .shr .ecx 1] else [])

/-- `eax` rotated left by the low 5 bits of `ecx`. Clobbers `ecx`, `edx`, `edi`. -/
def rotate : List Instr := (List.range 5).flatMap rotateStep

/-- The bytes `Id, Ic, Ib, Ia` of `I` in `eax` into the lanes of `xmm0`.
Clobbers `eax`, `ecx`, `edx`, `edi`, `xmm4` and `xmm5`. -/
def spread : List Instr :=
  [.mov .ecx (.reg .eax), .alu .and .ecx (imm 255),
   .mov .edx (.reg .eax), .shift .shr .edx 8, .alu .and .edx (imm 255),
   .mov .edi (.reg .eax), .shift .shr .edi 16, .alu .and .edi (imm 255),
   .shift .shr .eax 24] ++ lanes .ecx .edx .edi .eax

/-- The round function's first step, `I` (before the rotation) in `eax`, for
`Kmᵢ` at the subkeys' pointer and `D` in `ebp`: `Kmᵢ + D`, `Kmᵢ ^ D` or
`Kmᵢ - D` for Type 1, 2 or 3; and `Krᵢ` in `ecx`. -/
def mask (t : Nat) : List Instr :=
  [.mov .edx (.mem (at_ .esi kpOff)), .mov .eax (.mem (at_ .edx 0)),
   match t with
   | 1 => .alu .add .eax (.reg .ebp)
   | 2 => .alu .xor .eax (.reg .ebp)
   | _ => .alu .sub .eax (.reg .ebp),
   .mov .ecx (.mem (at_ .edx 64))]

/-- `f` from `S4[Id], S3[Ic], S2[Ib], S1[Ia]` at `esi + 0, 4, 8, 12`, into `eax`. -/
def combine : Nat → List Instr
  | 1 => [.mov .eax (.mem (at_ .esi 12)), .alu .xor .eax (.mem (at_ .esi 8)),
          .alu .sub .eax (.mem (at_ .esi 4)), .alu .add .eax (.mem (at_ .esi 0))]
  | 2 => [.mov .eax (.mem (at_ .esi 12)), .alu .sub .eax (.mem (at_ .esi 8)),
          .alu .add .eax (.mem (at_ .esi 4)), .alu .xor .eax (.mem (at_ .esi 0))]
  | _ => [.mov .eax (.mem (at_ .esi 12)), .alu .add .eax (.mem (at_ .esi 8)),
          .alu .xor .eax (.mem (at_ .esi 4)), .alu .sub .eax (.mem (at_ .esi 0))]

/-- `(L, R)` in `(ebx, ebp)` := `(R, L ^ f)`, then the subkeys' pointer to
the next round's: up for encryption, down for decryption. -/
def feistel (up : Bool) : List Instr :=
  [.alu .xor .eax (.reg .ebx), .mov .ebx (.reg .ebp), .mov .ebp (.reg .eax),
   .mov .edx (.mem (at_ .esi kpOff)), if up then .alu .add .edx (imm 4) else .alu .sub .edx (imm 4),
   .store (at_ .esi kpOff) .edx]

/-- A round of Type `t` (1, 2 or 3). -/
def round (t : Nat) (up : Bool) : Prog isa :=
  .seq (.block (mask t ++ rotate ++ spread))
    (.seq (scan s1234Sym)
      (.block (([.movdquStore (at_ .esi 0) .xmm1] : List Instr) ++ combine t ++ feistel up)))

/-- Three rounds, of Types 1, 2 and 3 (encryption) or 3, 2 and 1
(decryption), then the count of groups left down (ZF set at 0). -/
def group (up : Bool) : Prog isa :=
  .seq (round (if up then 1 else 3) up) (.seq (round 2 up)
    (.seq (round (if up then 3 else 1) up)
      (.block [.mov .edx (.mem (at_ .esi gcOff)), .alu .sub .edx (imm 1), .store (at_ .esi gcOff) .edx])))

/-- The count of groups, `rounds / 4 + 1`: 4 for 12 rounds, 5 for 16; ZF set
if `rounds` is 16. -/
def groups : List Instr :=
  [.mov .ecx (.mem (at_ .esi roundsOff)), .shift .shr .ecx 2, .alu .add .ecx (imm 1),
   .store (at_ .esi gcOff) .ecx, .mov .ecx (.mem (at_ .esi roundsOff)), .alu .cmp .ecx (imm 16)]

/-- Encrypting the block `(L₀, R₀)` in `(ebx, ebp)`, with the subkeys and
the number of rounds in the working space: rounds 1–15 in groups of three,
then round 16 if there are 16. -/
def encryptBlock : Prog isa :=
  .seq (.block (([.mov .edx (.mem (at_ .esi schedOff)), .store (at_ .esi kpOff) .edx] : List Instr) ++
      groups))
    (.seq (.loop (group true) .ne)
      (.seq (.block [.mov .ecx (.mem (at_ .esi roundsOff)), .alu .cmp .ecx (imm 16)])
        (.ite .e (round 1 true) (.block []))))

/-- Decrypting the block in `(ebx, ebp)`: round 16 if there are 16, then the
rest in groups of three, down from the last; the subkeys' pointer starts at
`Kmₙ`, `schedule + 4 (rounds - 1)`. -/
def decryptBlock : Prog isa :=
  .seq (.block (([.mov .edx (.mem (at_ .esi roundsOff)), .alu .add .edx (.reg .edx),
      .alu .add .edx (.reg .edx), .mov .ecx (.mem (at_ .esi schedOff)), .alu .add .edx (.reg .ecx),
      .alu .sub .edx (imm 4),
      .store (at_ .esi kpOff) .edx] : List Instr) ++ groups))
    (.seq (.ite .e (round 1 false) (.block []))
      (.loop (group false) .ne))

/-- The block at the data slot into `(ebx, ebp)` = `(L₀, R₀)`. -/
def load : List Instr :=
  [.mov .edx (.mem (at_ .esi dataOff)), .mov .ebx (.mem (at_ .edx 0)), .bswap .ebx,
   .mov .ebp (.mem (at_ .edx 4)), .bswap .ebp]

/-- `(Rₙ, Lₙ)` to the block at the data slot. The public slots are read
before and written again after (with what they held), so that the analysis
of constant time, which forgets them at a store of a secret it cannot place,
knows them again. -/
def store : List Instr :=
  [.mov .edx (.mem (at_ .esi dataOff)), .mov .eax (.mem (at_ .esi schedOff)),
   .mov .ecx (.mem (at_ .esi roundsOff)), .mov .edi (.mem (at_ .esi nOff)),
   .bswap .ebp, .store (at_ .edx 0) .ebp, .bswap .ebx, .store (at_ .edx 4) .ebx,
   .store (at_ .esi dataOff) .edx, .store (at_ .esi schedOff) .eax,
   .store (at_ .esi roundsOff) .ecx, .store (at_ .esi nOff) .edi]

/-- The block at the data slot, encrypted or decrypted in place. -/
def crypt (up : Bool) : Prog isa :=
  .seq (.block load) (.seq (if up then encryptBlock else decryptBlock) (.block store))

/-- On to the next block (ZF set when none are left). -/
def advance : List Instr :=
  [.mov .edx (.mem (at_ .esi dataOff)), .alu .add .edx (imm 8), .store (at_ .esi dataOff) .edx,
   .mov .edx (.mem (at_ .esi nOff)), .alu .sub .edx (imm 1), .store (at_ .esi nOff) .edx]

/-- The registers saved in the working space, and where; `esi`, the base,
is restored last. -/
def saved : List (Reg × Nat) :=
  [(.ebx, savedOff), (.edi, savedOff + 8), (.ebp, savedOff + 12), (.esi, savedOff + 4)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .eax d) r
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .esi d))

/-- The working space to `esi`, the arguments to their slots, and ZF set if
there are no blocks. -/
def setup : List Instr :=
  [.mov .esi (.reg .eax), .mov .ecx (.mem (at_ .esp 4)), .mov .edx (.mem (at_ .esp 8)),
   .mov .edi (.mem (at_ .esp 12)), .mov .ebx (.mem (at_ .esp 16)), .store (at_ .esi schedOff) .ecx,
   .store (at_ .esi roundsOff) .edx, .store (at_ .esi dataOff) .edi, .store (at_ .esi nOff) .ebx,
   .alu .cmp .ebx (imm 0)]

/-- `vg_cast5_ecb_encrypt(schedule, rounds, data, n, scratch)` (all on the
stack), or decrypt: the arguments to the working space, then each block in
turn. -/
def ecb (up : Bool) : Prog isa :=
  .seq (.block (([.mov .eax (.mem (at_ .esp 20))] : List Instr) ++ save ++ setup))
    (.seq (.ite .e (.block []) (.loop (.seq (crypt up) (.block advance)) .ne)) (.block restore))

def ecbEncrypt : Prog isa := ecb true
def ecbDecrypt : Prog isa := ecb false

/-! ## Key expansion

`x0 … xF` and `z0 … zF` are kept in the working space (`esi`) at 16 and 32,
a byte each, in order; the subkeys are written to `edi`, which moves on 64
bytes after each half, `ebx` counting the halves left. -/

/-- Where the four extra lookups of a group of lines are kept. -/
def extraOff : Nat := 48

/-- Where key expansion saves the callee-saved registers. -/
def keySavedOff : Nat := 64

/-- The lanes `S8[d], S7[c], S6[b], S5[a]` of a scan of `VG_CAST5_S5678`, for
the bytes `a, b, c, d`. Clobbers `eax`, `ecx`, `edx`, `ebp`, `xmm4`, `xmm5`. -/
def gather (a b c d : Pos) : List Instr :=
  [.movzx8 .ecx (at_ .esi (srcOff d)), .movzx8 .edx (at_ .esi (srcOff c)),
   .movzx8 .eax (at_ .esi (srcOff b)), .movzx8 .ebp (at_ .esi (srcOff a))] ++ lanes .ecx .edx .eax .ebp

/-- What a line does with its lookups: `S5[a] ^ S6[b] ^ S7[c] ^ S8[d] ^ Sₑ[f]
^ w`, into `eax`, `Sₑ[f]` from the group's extra lookups (lane `8 - e` of
those at `esi + 48`), `w` the quadruple of an array, big-endian, if any. -/
def lineTail (l : Line) : List Instr :=
  ([.movdquStore (at_ .esi 0) .xmm1, .mov .eax (.mem (at_ .esi 0)),
    .alu .xor .eax (.mem (at_ .esi 4)), .alu .xor .eax (.mem (at_ .esi 8)),
    .alu .xor .eax (.mem (at_ .esi 12)),
    .alu .xor .eax (.mem (at_ .esi (extraOff + 4 * (8 - l.extra.1))))] : List Instr) ++
  (match l.word with
    | some (a, q) => [.mov .ecx (.mem (at_ .esi (off a + 4 * q))), .bswap .ecx, .alu .xor .eax (.reg .ecx)]
    | none => [])

/-- A line, into `eax`. -/
def line (l : Line) : Prog isa :=
  .seq (.block (gather l.main.1 l.main.2.1 l.main.2.2.1 l.main.2.2.2)) (.seq (scan s5678Sym)
    (.block (lineTail l)))

/-- The extra lookups of a group: `S5[a], S6[b], S7[c], S8[d]`, to the lanes
3, 2, 1, 0 at `esi + 48`. -/
def extras (a b c d : Pos) : Prog isa :=
  .seq (.block (gather a b c d)) (.seq (scan s5678Sym)
    (.block [.movdquStore (at_ .esi extraOff) .xmm1]))

/-- Four lines, after their extra lookups, each followed by its store `st k`. -/
def lines4 (ls : List Line) (st : Nat → List Instr) : Prog isa :=
  .seq (extras (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8))
    ((List.range 4).foldr (fun k rest =>
      .seq (line (ls.getD k default))
        (.seq (.block (st k)) rest)) (.block []))

/-- Store `eax` as quadruple `q` of the array `a`, big-endian. -/
def storeQuad (a : Arr) (q : Nat) : List Instr := [.bswap .eax, .store (at_ .esi (off a + 4 * q)) .eax]

/-- Store `eax` as subkey `k` at `edi`. -/
def storeKey (k : Nat) : List Instr := [.store (at_ .edi (4 * k)) .eax]

/-- One half of §2.4 (`Spec.Cast5.half`), with sixteen subkeys to `edi`, then
`edi` on 64 bytes and the count of halves left (`ebx`) down. -/
def half : Prog isa :=
  .seq (lines4 zLines (storeQuad .z)) (.seq (lines4 aLines storeKey)
    (.seq (lines4 xLines (storeQuad .x))
      (.seq (lines4 bLines fun k => storeKey (4 + k))
        (.seq (lines4 zLines (storeQuad .z)) (.seq (lines4 cLines fun k => storeKey (8 + k))
          (.seq (lines4 xLines (storeQuad .x))
            (.seq (lines4 dLines fun k => storeKey (12 + k))
              (.block [.alu .add .edi (imm 64), .alu .sub .ebx (imm 1)]))))))))

/-- Copy a key byte to `x`: `edi` at the next key byte, `eax` at its place in
`x`, `ebx` the count left. -/
def copyStep : List Instr :=
  [.movzx8 .ecx (at_ .edi 0), .store8 (at_ .eax 0) .cl, .alu .add .edi (imm 1),
   .alu .add .eax (imm 1), .alu .sub .ebx (imm 1)]

/-- The registers key expansion saves, and where; `esi` is restored last. -/
def keySaved : List (Reg × Nat) :=
  [(.ebx, keySavedOff), (.edi, keySavedOff + 8), (.ebp, keySavedOff + 12), (.esi, keySavedOff + 4)]

def keySave : List Instr := keySaved.map fun (r, d) => .store (at_ .eax d) r
def keyRestore : List Instr := keySaved.map fun (r, d) => .mov r (.mem (at_ .esi d))

/-- The working space to `esi`, the key's address, its length and the
schedule's address to `edi`, `ebx` and `edx`, and `x` := zeros; `eax` at `x`. -/
def keySetup : List Instr :=
  [.mov .esi (.reg .eax), .mov .edi (.mem (at_ .esp 4)), .mov .ebx (.mem (at_ .esp 8)),
   .mov .edx (.mem (at_ .esp 12)), .mov .ecx (imm 0), .store (at_ .esi xOff) .ecx,
   .store (at_ .esi (xOff + 4)) .ecx, .store (at_ .esi (xOff + 8)) .ecx, .store (at_ .esi (xOff + 12)) .ecx,
   .alu .add .eax (imm xOff)]

/-- `vg_cast5_expand_key(key, key_len, schedule, scratch)` (all on the stack):
`x` := the key padded with zeros (§2.5), then both halves. -/
def expandKey : Prog isa :=
  .seq (.block (([.mov .eax (.mem (at_ .esp 16))] : List Instr) ++ keySave ++ keySetup))
    (.seq (.loop (.block copyStep) .ne)
      (.seq (.block [.mov .edi (.reg .edx), .mov .ebx (imm 2)]) (.seq (.loop half .ne)
        (.block keyRestore))))

end VG.Impl.Cast5.X86
