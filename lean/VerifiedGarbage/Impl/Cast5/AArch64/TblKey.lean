module

public import VerifiedGarbage.Impl.Cast5.AArch64.Tbl
public import VerifiedGarbage.Impl.Cast5.Lines
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub

/-!
# CAST5 key expansion on AArch64, S-boxes by `tbl`

`vg_cast5_expand_key(key = x0, key_len = x1, schedule = x2, scratch = x3)`.
As the scan's code did, it keeps `x0 … xF` and `z0 … zF` in the working
space at `x3 + 16` and `x3 + 32` (`Impl.Cast5.off`), a byte each, and
computes the lines of RFC 2144 §2.4 (`Impl/Cast5/Lines.lean`); no S-box
lookup reads memory at a secret address.

The lookups are those of the rounds (`Tbl.lookup`), in `S5`–`S8`, which
follow `S1`–`S4` in the table the code carries: `sboxes`, an internal
function, looks up each of `S5`–`S8` at the sixteen bytes of its index
register (`idxReg`, `v16`–`v19`), so one call (a *pass*) serves every lookup
whose index is known, each in a byte lane of its S-box's register:

* lanes 0–3: the main bytes of the four lines of a group of subkeys, which
  are independent, and lane 8 the group's extra byte for that S-box (line
  `k`'s extra S-box is `S_{5+k}`); the four subkeys are `v4 ^ v6`;
* lane 4: the main bytes of one line computing a quadruple of `x` or `z`,
  which depend on the line before, so there is one such line a pass; its
  value is word 0 of `v5`;
* lane 5: the extra byte, for that S-box, of the group of four such lines
  (they are of the other array, which the group does not write), looked up
  in the group's first pass and kept in the working space, at `x3 + 48`.

A half of §2.4 is seventeen passes: four for each group computing `z` or
`x`, the first of which also serves the subkeys computed from the array the
group before it wrote, and one for the half's last four subkeys.

Timing depends only on the pointers and `key_len`: every byte of the key,
`x` and `z` is loaded from an address that does not depend on it, into a
lane, and `tbl` and `tbx` take a time independent of their data. The return
address is kept in `x15` across the calls; `sboxes` sets the table's address
itself, in `x9`.
-/

@[expose] public section

namespace VG.Impl.Cast5.AArch64.Tbl

open VG.AArch64 VG.Impl.Cast5
open VG.Impl.Blowfish.AArch64 (idxReg veor words wordReg constants)

/-! ## The lookups -/

/-- After the lookup of `S_{5+j}`: the XOR of the S-boxes so far, of the
subkeys' main bytes in `v4` and of a line's in word 0 of `v5`; the extra
lookups of a group of lines in word `j` of `v7`, and of a group of subkeys in
word `j` of `v6`. -/
def gatherOut (j : Nat) : List Instr :=
  (if j = 0 then [.vop (.mov .v4 (wordReg 0)), .vop (.mov .v5 (wordReg 1))]
   else [veor .v4 .v4 (wordReg 0), veor .v5 .v5 (wordReg 1)]) ++
  [.vop (.insE .s4 .v7 j (wordReg 1) 1), .vop (.insE .s4 .v6 j (wordReg 2) 0)]

/-- `vg_cast5_key_sboxes`: `S5`–`S8` at the bytes of `idxReg`, with 64 and
128 in every byte of `c64` and `c128`; the table's address to `x9`. -/
def sboxes5678 : Prog isa :=
  .block (([.adrSym .x9 planesSym] : List Instr) ++
    (List.range 4).flatMap fun j => lookup (4 + j) j ++ words ++ gatherOut j)

def sboxesName : String := "vg_cast5_key_sboxes"

/-- A pass. -/
def pass : Prog isa := .call sboxesName sboxes5678

/-! ## The lines -/

/-- Where a group's extra lookups are kept in the working space. -/
def extraOff : Nat := 48

/-- The byte at `p` into lane `lane` of the index of `S_{5+j}`. -/
def gatherByte (lane j : Nat) (p : Pos) : List Instr :=
  [.ldrb .x10 .x3 (srcOff p), .vop (.ins .b16 (idxReg j) lane .x10)]

/-- A line's main bytes into lane `lane`. -/
def gatherMain (lane : Nat) (l : Line) : List Instr :=
  gatherByte lane 0 l.main.1 ++ gatherByte lane 1 l.main.2.1 ++ gatherByte lane 2 l.main.2.2.1 ++
    gatherByte lane 3 l.main.2.2.2

/-- A group's extra bytes into lane `lane`. -/
def gatherExtras (lane : Nat) (ls : List Line) : List Instr :=
  (List.range 4).flatMap fun j => gatherByte lane j (extraOf ls (5 + j))

/-- The bytes of a group of subkeys: lanes 0–3 and 8. -/
def gatherKeys (ls : List Line) : List Instr :=
  (List.range 4).flatMap (fun k => gatherMain k (ls.getD k default)) ++ gatherExtras 8 ls

/-- The four subkeys of a group, after its pass, to `x2 + o`. -/
def storeKeys (o : Nat) : List Instr := [veor .v4 .v4 .v6, .strq .v4 .x2 o]

/-- A line's value after its pass, `S5[a] ^ S6[b] ^ S7[c] ^ S8[d] ^ Sₑ[f] ^ w`
(`Sₑ[f]` from the working space, `w` the line's quadruple), stored as
quadruple `k` of `tgt`, big-endian. -/
def storeLine (l : Line) (k : Nat) (tgt : Arr) : List Instr :=
  ([.umov .w .x0 .v5 0, .ldr .w .x10 .x3 (extraOff + 4 * (l.extra.1 - 5)),
    .logic .eor .w .x0 .x0 .x10] : List Instr) ++
  (match l.word with
    | some (a, q) => [.ldr .w .x10 .x3 (off a + 4 * q), .rev32 .x10 .x10, .logic .eor .w .x0 .x0 .x10]
    | none => []) ++
  ([.rev32 .x10 .x0, .str .w .x10 .x3 (off tgt + 4 * k)] : List Instr)

/-- Line `k` of a group after the first, storing into `tgt`. -/
def lineNext (ls : List Line) (tgt : Arr) (k : Nat) : Prog isa :=
  .seq (.block (gatherMain 4 (ls.getD k default)))
    (.seq pass (.block (storeLine (ls.getD k default) k tgt)))

/-- A group of four lines storing into `tgt`; its first pass also serves the
subkeys of `kl`, if any, stored at `x2 + ko`. -/
def group4 (ls : List Line) (tgt : Arr) (kl : List Line) (ko : Nat) (keys : Bool) : Prog isa :=
  .seq (.block (gatherMain 4 (ls.getD 0 default) ++ gatherExtras 5 ls ++ (if keys then gatherKeys kl else [])))
    (.seq pass
      (.seq (.block (([.strq .v7 .x3 extraOff] : List Instr) ++ (if keys then storeKeys ko else []) ++
          storeLine (ls.getD 0 default) 0 tgt))
        (.seq (lineNext ls tgt 1) (.seq (lineNext ls tgt 2) (lineNext ls tgt 3)))))

/-- One half of §2.4 (`Spec.Cast5.half`), with sixteen subkeys to `x2`, then
`x2` on 64 bytes and the count of halves left (`x1`) down. -/
def halfTbl : Prog isa :=
  .seq (group4 zLines .z [] 0 false) (.seq (group4 xLines .x aLines 0 true)
    (.seq (group4 zLines .z bLines 16 true) (.seq (group4 xLines .x cLines 32 true)
      (.seq (.block (gatherKeys dLines)) (.seq pass
        (.block (storeKeys 48 ++ ([.addImm .x .x2 .x2 64, .subImm .x .x1 .x1 1] : List Instr))))))))

/-- Copy a key byte to `x`: `x0` at the next key byte, `x4` at its place in
`x`, `x1` the count left. -/
def copyStep : List Instr :=
  [.ldrb .x9 .x0 0, .strb .x9 .x4 0, .addImm .x .x0 .x0 1, .addImm .x .x4 .x4 1, .subImm .x .x1 .x1 1]

/-- `vg_cast5_expand_key`: `x` := the key padded with zeros (§2.5), then both
halves. -/
def expandKey : Prog isa :=
  .seq (.block [.movz .x .x9 0 0, .str .x .x9 .x3 xOff, .str .x .x9 .x3 (xOff + 8),
      .addImm .x .x4 .x3 xOff])
    (.seq (.loop (.block copyStep) (.nonzero .x .x1))
      (.seq (.block (([.movz .x .x1 2 0, .addImm .x .x15 .x30 0] : List Instr) ++ constants))
        (.seq (.loop halfTbl (.nonzero .x .x1)) (.block [.addImm .x .x30 .x15 0]))))

namespace Fn

/-- `vg_cast5_expand_key` as emitted: `expandKey`, then its cleanup, which
clears the registers it writes that the calling convention does not preserve
(`Impl.Residue.AArch64.scrubAll`; it has no result and uses no stack), so
that it returns without secret residue. -/
def expandKey : Prog isa :=
  Residue.AArch64.scrubAll 0 0
    ⟨[.x1, .x2, .x4, .x6, .x9, .x10, .x15, .x16, .x17],
     [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23,
      .v24, .v25, .v26, .v28, .v29, .v30, .v31],
     []⟩
    Tbl.expandKey

end Fn

end VG.Impl.Cast5.AArch64.Tbl
