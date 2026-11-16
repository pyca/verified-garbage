module

public import VerifiedGarbage.Impl.Cast5.Tables
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# CAST5 on baseline AArch64: one block at a time

The block code of the modes that encipher one block at a time
(`Impl/Cast5/AArch64/Modes.lean`); the ECB functions, CBC and CFB64
decryption work on sixteen blocks at once (`Impl/Cast5/AArch64/Tbl.lean`),
and key expansion looks its S-boxes up as they do (`AArch64/TblKey.lean`).

As on x86-64 (`Impl/Cast5/X86_64.lean`), a lookup in an S-box never uses a
secret as an address: the four lookups a round function makes, `S1[Ia]`,
`S2[Ib]`, `S3[Ic]` and `S4[Id]`, are made at once by a *scan* of a table of
256 entries of 16 bytes, entry `i` the four words `S4[i], S3[i], S2[i], S1[i]`
(`VG_CAST5_S1234`), in AdvSIMD registers. The indices are the four lanes of
`v0`. Their low two bits select within four adjacent entries with BIT;
`cmeq` compares their remaining bits with the public group number, and the
selected words are ANDed with that mask and ORed into `v1`. Every entry is
loaded, in order.

The rotation by the secret amount `Kr` (§2.2) is five rotations by 1, 2, 4, 8
and 16, each selected or not (`csel`) by a bit of `Kr` (`rotate`).

Only the caller-saved registers `x0`–`x15`, `v0`–`v6` and `v16`–`v19` are used (the
round function's `I` in `w4`). Registers
of the scan: the table in `x10`, the count of groups of four entries left in
`x11`, `v0`–`v5` and `v16`–`v19`.
-/

@[expose] public section

namespace VG.Impl.Cast5.AArch64

open VG.AArch64

/-! ## The scan -/

/-- Four fixed-address loads; select their low index bits with BIT. -/
def scanTile : List Instr :=
  [.ldrq .v4 .x10 0, .ldrq .v5 .x10 16,
   .vop (.bsel .bit .v4 .v5 .v16),
   .ldrq .v19 .x10 32, .ldrq .v5 .x10 48,
   .vop (.bsel .bit .v19 .v5 .v16), .vop (.bsel .bit .v4 .v19 .v17),
   .vop (.cmeq .s4 .v5 .v18 .v2), .vop (.logic .and .v4 .v4 .v5),
   .vop (.logic .orr .v1 .v1 .v4), .vop (.add .s4 .v2 .v2 .v3)]

def scanStart (sym : String) : List Instr :=
  [.adrSym .x10 sym, .movz .x .x11 64 0,
    .vop (.movi0 .v1), .vop (.movi0 .v2),
    .vop (.cmeq .s4 .v3 .v3 .v3), .vop (.shift .ushr .s4 .v3 .v3 31),
    .vop (.logic .and .v4 .v0 .v3), .vop (.movi0 .v16),
    .vop (.sub .s4 .v16 .v16 .v4),
    .vop (.shift .ushr .s4 .v4 .v0 1), .vop (.logic .and .v4 .v4 .v3),
    .vop (.movi0 .v17), .vop (.sub .s4 .v17 .v17 .v4),
    .vop (.shift .ushr .s4 .v18 .v0 2)]

/-- One four-entry group, then advance the public pointer and counter. -/
def scanBody : List Instr :=
  scanTile ++ [.addImm .x .x10 .x10 64, .subImm .x .x11 .x11 1]

/-- Select four words by scanning every table entry at fixed addresses.
Clobbers x10, x11, v1–v5 and caller-saved v16–v19. -/
def scan (sym : String) : Prog isa :=
  .seq (.block (scanStart sym)) (.loop (.block scanBody) (.nonzero .x .x11))

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

end VG.Impl.Cast5.AArch64
