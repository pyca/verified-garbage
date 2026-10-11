module

public import VerifiedGarbage.Impl.Cast5.Tables
public import VerifiedGarbage.Impl.Cast5.Lines
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# CAST5 on baseline AArch64

As on x86-64 (`Impl/Cast5/X86_64.lean`), a lookup in an S-box never uses a
secret as an address: the four lookups a round function makes, `S1[Ia]`,
`S2[Ib]`, `S3[Ic]` and `S4[Id]`, are made at once by a *scan* of a table of
256 entries of 16 bytes, entry `i` the four words `S4[i], S3[i], S2[i], S1[i]`
(`VG_CAST5_S1234`), in AdvSIMD registers: the indices are the four lanes of
`v0`, `cmeq` with the entry's number in every lane (`v2`) gives a mask that is
all ones in the lanes whose index it is, and the entry is ANDed with it and
ORed into the result, `v1`; every entry is loaded, in order. Key expansion
scans `VG_CAST5_S5678` the same way, entry `i` the words `S8[i], S7[i], S6[i],
S5[i]`.

The rotation by the secret amount `Kr` (§2.2) is five rotations by 1, 2, 4, 8
and 16, each selected or not (`csel`) by a bit of `Kr` (`rotate`).

Only the caller-saved registers `x0`–`x15` and `v0`–`v6` are used (the
round function's `I` in `w4`, whose argument, `scratch`, ECB does not use). Registers
of the scan: the table in `x10`, the count of groups of four entries left in
`x11`, `v0`–`v5`.
-/

@[expose] public section

namespace VG.Impl.Cast5.AArch64

open VG.AArch64

/-! ## The scan -/

/-- Entry `e` of the four at `x10`: its mask, from the indices in `v0` and the
entry's number in every lane of `v2`, ANDed with it and ORed into `v1`; then
the next number. -/
def scanEntry (e : Nat) : List Instr :=
  [.vop (.cmeq .s4 .v4 .v0 .v2), .ldrq .v5 .x10 (16 * e), .vop (.logic .and .v5 .v5 .v4),
   .vop (.logic .orr .v1 .v1 .v5), .vop (.add .s4 .v2 .v2 .v3)]

/-- Four entries, then on to the next four. -/
def scanBody : List Instr :=
  (List.range 4).flatMap scanEntry ++ ([.addImm .x .x10 .x10 64, .subImm .x .x11 .x11 1] : List Instr)

/-- The table `sym` at the indices in the lanes of `v0` (each less than 256),
into the lanes of `v1`. Clobbers `x10`, `x11` and `v1`–`v5`. -/
def scan (sym : String) : Prog isa :=
  .seq (.block [.adrSym .x10 sym, .movz .x .x11 64 0, .vop (.movi0 .v1), .vop (.movi0 .v2),
      .vop (.cmeq .s4 .v3 .v3 .v3), .vop (.shift .ushr .s4 .v3 .v3 31)])
    (.loop (.block scanBody) (.nonzero .x .x11))

/-! ## Encryption and decryption -/

/-- One of the five steps of the rotation of `w4` left by the low 5 bits of
`w13` (shifted right by `b` so far): rotate by `2 ^ b` if bit 0 of `w13` is
set. Clobbers `w14`, `w15`. -/
def rotateStep (b : Nat) : List Instr :=
  ([.movz .w .x14 1 0, .tst .w .x13 .x14, .ror .w .x15 .x4 (32 - 2 ^ b), .cselc .w .x4 .x15 .x4 .ne] : List Instr) ++
  (if b < 4 then [.lsr .w .x13 .x13 1] else [])

/-- `w4` rotated left by the low 5 bits of `w13`. Clobbers `w13`. -/
def rotate : List Instr := (List.range 5).flatMap rotateStep

/-- The bytes `Id, Ic, Ib, Ia` of `I` in `w4` into the lanes of `v0`.
Clobbers `w14`. -/
def spread : List Instr :=
  [.lsl .w .x14 .x4 24, .lsr .w .x14 .x14 24, .vop (.ins .s4 .v0 0 .x14),
   .lsl .w .x14 .x4 16, .lsr .w .x14 .x14 24, .vop (.ins .s4 .v0 1 .x14),
   .lsl .w .x14 .x4 8, .lsr .w .x14 .x14 24, .vop (.ins .s4 .v0 2 .x14),
   .lsr .w .x14 .x4 24, .vop (.ins .s4 .v0 3 .x14)]

/-- The round function's first step, `I` (before the rotation) in `w4`, for
`Kmᵢ` at `x12` and `D` in `w6`: `Kmᵢ + D`, `Kmᵢ ^ D` or `Kmᵢ - D` for Type 1,
2 or 3; then `Krᵢ` into `w13`. -/
def mask : Nat → List Instr
  | 1 => [.ldr .w .x9 .x12 0, .add .w .x4 .x9 .x6, .ldr .w .x13 .x12 64]
  | 2 => [.ldr .w .x9 .x12 0, .logic .eor .w .x4 .x9 .x6, .ldr .w .x13 .x12 64]
  | _ => [.ldr .w .x9 .x12 0, .sub .w .x4 .x9 .x6, .ldr .w .x13 .x12 64]

/-- `f` from `S1[Ia], S2[Ib], S3[Ic], S4[Id]` in the lanes 3, 2, 1, 0 of `v1`,
into `w4`. -/
def combine : Nat → List Instr
  | 1 => [.umov .w .x9 .v1 3, .umov .w .x14 .v1 2, .umov .w .x15 .v1 1, .umov .w .x10 .v1 0,
          .logic .eor .w .x4 .x9 .x14, .sub .w .x4 .x4 .x15, .add .w .x4 .x4 .x10]
  | 2 => [.umov .w .x9 .v1 3, .umov .w .x14 .v1 2, .umov .w .x15 .v1 1, .umov .w .x10 .v1 0,
          .sub .w .x4 .x9 .x14, .add .w .x4 .x4 .x15, .logic .eor .w .x4 .x4 .x10]
  | _ => [.umov .w .x9 .v1 3, .umov .w .x14 .v1 2, .umov .w .x15 .v1 1, .umov .w .x10 .v1 0,
          .add .w .x4 .x9 .x14, .logic .eor .w .x4 .x4 .x15, .sub .w .x4 .x4 .x10]

/-- `(L, R)` in `(w5, w6)` := `(R, L ^ f)`, then `x12` to the next round's
subkeys: up for encryption, down for decryption. -/
def feistel (up : Bool) : List Instr :=
  [.logic .eor .w .x4 .x4 .x5, .logic .orr .w .x5 .x6 .x6, .logic .orr .w .x6 .x4 .x4,
   if up then .addImm .x .x12 .x12 4 else .subImm .x .x12 .x12 4]

/-- A round of Type `t` (1, 2 or 3) with the subkeys `Kmᵢ` at `x12` and `Krᵢ`
at `x12 + 64`. -/
def round (t : Nat) (up : Bool) : Prog isa :=
  .seq (.block (mask t ++ rotate ++ spread))
    (.seq (scan s1234Sym) (.block (combine t ++ feistel up)))

/-- Three rounds, of Types 1, 2 and 3 (encryption) or 3, 2 and 1
(decryption), then the count of groups left (`x7`) down. -/
def group (up : Bool) : Prog isa :=
  .seq (round (if up then 1 else 3) up) (.seq (round 2 up)
    (.seq (round (if up then 3 else 1) up) (.block [.subImm .x .x7 .x7 1])))

/-- `x7` := `rounds / 4 + 1`: 4 groups for 12 rounds, 5 for 16; `x8` :=
`rounds - 16`, zero if there are 16. -/
def groups : List Instr :=
  [.lsr .x .x7 .x1 2, .addImm .x .x7 .x7 1, .subImm .x .x8 .x1 16]

/-- The block at `x2` into `(w5, w6)` = `(L₀, R₀)`. -/
def load : List Instr :=
  [.ldr .w .x5 .x2 0, .rev32 .x5 .x5, .ldr .w .x6 .x2 4, .rev32 .x6 .x6]

/-- `(Rₙ, Lₙ)` to the block at `x2`, then on to the next block. -/
def store : List Instr :=
  [.rev32 .x6 .x6, .str .w .x6 .x2 0, .rev32 .x5 .x5, .str .w .x5 .x2 4,
   .addImm .x .x2 .x2 8, .subImm .x .x3 .x3 1]

/-- Encrypting a block: rounds 1–15 in groups of three, then round 16 if
there are 16. -/
def encryptBlock : Prog isa :=
  .seq (.block (load ++ ([.addImm .x .x12 .x0 0] : List Instr) ++ groups))
    (.seq (.loop (group true) (.nonzero .x .x7))
      (.seq (.ite (.zero .x .x8) (round 1 true) (.block [])) (.block store)))

/-- Decrypting a block: round 16 if there are 16, then the rest in groups of
three, down from the last; `x12` starts at `Kmₙ`, `x0 + 4 (rounds - 1)`. -/
def decryptBlock : Prog isa :=
  .seq (.block (load ++ ([.lsl .x .x12 .x1 2, .add .x .x12 .x12 .x0, .subImm .x .x12 .x12 4] :
      List Instr) ++ groups))
    (.seq (.ite (.zero .x .x8) (round 1 false) (.block []))
      (.seq (.loop (group false) (.nonzero .x .x7)) (.block store)))

/-- `vg_cast5_ecb_encrypt(schedule = x0, rounds = x1, data = x2, n = x3,
scratch = x4)`, or decrypt: each block in turn. -/
def ecb (block : Prog isa) : Prog isa :=
  .ite (.zero .x .x3) (.block []) (.loop block (.nonzero .x .x3))

def ecbEncrypt : Prog isa := ecb encryptBlock
def ecbDecrypt : Prog isa := ecb decryptBlock

/-! ## Key expansion

`x0 … xF` and `z0 … zF` are kept in the working space at `x3 + 16` and
`x3 + 32` (`Impl.Cast5.off`), a byte each, in order; a group's extra lookups
in `v6`; the subkeys are written to `x2`, which moves on 64 bytes after each
half. -/

/-- The lanes `S8[d], S7[c], S6[b], S5[a]` of a scan of `VG_CAST5_S5678`, for
the bytes `a, b, c, d`, into `v0`. Clobbers `x9`. -/
def gather (a b c d : Pos) : List Instr :=
  [.ldrb .x9 .x3 (srcOff d), .vop (.ins .s4 .v0 0 .x9), .ldrb .x9 .x3 (srcOff c), .vop (.ins .s4 .v0 1 .x9),
   .ldrb .x9 .x3 (srcOff b), .vop (.ins .s4 .v0 2 .x9), .ldrb .x9 .x3 (srcOff a), .vop (.ins .s4 .v0 3 .x9)]

/-- A line `S5[a] ^ S6[b] ^ S7[c] ^ S8[d] ^ Sₑ[f] ^ w`, into `w0`: `Sₑ[f]` from
the group's extra lookups (lane `8 - e` of `v6`), `w` the quadruple of an
array, big-endian, if any. -/
def line (l : Line) : Prog isa :=
  .seq (.block (gather l.main.1 l.main.2.1 l.main.2.2.1 l.main.2.2.2)) (.seq (scan s5678Sym)
    (.block (([.umov .w .x0 .v1 0, .umov .w .x9 .v1 1, .logic .eor .w .x0 .x0 .x9, .umov .w .x9 .v1 2,
      .logic .eor .w .x0 .x0 .x9, .umov .w .x9 .v1 3, .logic .eor .w .x0 .x0 .x9,
      .umov .w .x9 .v6 (8 - l.extra.1), .logic .eor .w .x0 .x0 .x9] : List Instr) ++
      (match l.word with
        | some (a, q) => [.ldr .w .x9 .x3 (off a + 4 * q), .rev32 .x9 .x9, .logic .eor .w .x0 .x0 .x9]
        | none => []))))

/-- The extra lookups of a group: `S5[a], S6[b], S7[c], S8[d]`, to the lanes
3, 2, 1, 0 of `v6`. -/
def extras (a b c d : Pos) : Prog isa :=
  .seq (.block (gather a b c d)) (.seq (scan s5678Sym) (.block [.vop (.mov .v6 .v1)]))

/-- Four lines, after their extra lookups, each followed by its store `st k`. -/
def lines4 (ls : List Line) (st : Nat → List Instr) : Prog isa :=
  .seq (extras (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8))
    ((List.range 4).foldr (fun k rest =>
      .seq (line (ls.getD k default))
        (.seq (.block (st k)) rest)) (.block []))

/-- Store `w0` as quadruple `q` of the array `a`, big-endian. -/
def storeQuad (a : Arr) (q : Nat) : List Instr := [.rev32 .x9 .x0, .str .w .x9 .x3 (off a + 4 * q)]

/-- Store `w0` as subkey `k` at `x2`. -/
def storeKey (k : Nat) : List Instr := [.str .w .x0 .x2 (4 * k)]

/-- One half of §2.4 (`Spec.Cast5.half`), with sixteen subkeys to `x2`, then
`x2` on 64 bytes and the count of halves left (`x1`) down. -/
def half : Prog isa :=
  .seq (lines4 zLines (storeQuad .z)) (.seq (lines4 aLines storeKey)
    (.seq (lines4 xLines (storeQuad .x))
      (.seq (lines4 bLines fun k => storeKey (4 + k))
        (.seq (lines4 zLines (storeQuad .z)) (.seq (lines4 cLines fun k => storeKey (8 + k))
          (.seq (lines4 xLines (storeQuad .x))
            (.seq (lines4 dLines fun k => storeKey (12 + k))
              (.block [.addImm .x .x2 .x2 64, .subImm .x .x1 .x1 1]))))))))

/-- Copy a key byte to `x`: `x0` at the next key byte, `x4` at its place in
`x`, `x1` the count left. -/
def copyStep : List Instr :=
  [.ldrb .x9 .x0 0, .strb .x9 .x4 0, .addImm .x .x0 .x0 1, .addImm .x .x4 .x4 1, .subImm .x .x1 .x1 1]

/-- `vg_cast5_expand_key(key = x0, key_len = x1, schedule = x2, scratch =
x3)`: `x` := the key padded with zeros (§2.5), then both halves. -/
def expandKey : Prog isa :=
  .seq (.block [.movz .x .x9 0 0, .str .x .x9 .x3 xOff, .str .x .x9 .x3 (xOff + 8),
      .addImm .x .x4 .x3 xOff])
    (.seq (.loop (.block copyStep) (.nonzero .x .x1))
      (.seq (.block [.movz .x .x1 2 0]) (.loop half (.nonzero .x .x1))))

end VG.Impl.Cast5.AArch64
