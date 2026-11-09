module

public import VerifiedGarbage.Impl.RsaOaep.AArch64.Mgf1
public import VerifiedGarbage.Impl.ICall

/-!
# MGF1 on AArch64 with the hash function of a table

`mgfXor` of `Impl/RsaOaep/AArch64/Mgf1.lean` for the hash function of a
table of the interface `Hash` (`Spec/HashTable.lean`) rather than a fixed
one, as on x86-64 (`Impl/Mgf1/X86_64/Table.lean`): the table's address is
the word at `[sp + sArg]` (the caller's argument), which MGF1 copies to the
slot `sTab`, and the table's digest length (its word 4) to the slot `sD`.
The hash function's `init`, `update` and `finalize` are the table's
functions 0, 1 and 2, which it calls indirectly (`tcall`: their address, the
table's word `j`, into `x16`, then `blr x16`, of whichever of the functions
`Fns` lists is at that address); the digest length is read from `sD` rather
than being an immediate. Everything else is `Impl/RsaOaep/AArch64/Mgf1.lean`'s.
-/

@[expose] public section

namespace VG.Impl.RsaOaep.AArch64.Mgf1.Table

open VG VG.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs Layout scr initArgs updSrcArgs updCtrArgs finArgs xorBody)

/-- The functions an indirect call of each of a table's functions may
reach: for each of `init`, `update` and `finalize`, that function of every
table of the interface, by name. -/
structure Fns where
  init : List (String × Prog isa)
  upd : List (String × Prog isa)
  fin : List (String × Prog isa)

variable (L : Layout) (sArg sTab sD : Nat) (f : Fns)

/-- The call of the table's function `j`, among `ts`: its address (the
table's word `j`) into `x16`, then `blr x16`. -/
def tcall (j : Nat) (ts : List (String × Prog isa)) : Prog isa :=
  .seq (.block [.ldrSp .x16 sTab, .ldr .x .x16 .x16 (8 * j)]) (Code.icalls (.blr .x16) ts)

/-- `xorHead`, with the digest length read from `sD`. -/
def xorHead : List Instr :=
  scr L .x11 L.oDig ++ [.ldrSp .x10 L.sDone, .ldrSp .x12 L.sDst, .add .x .x12 .x12 .x10,
    .ldrSp .x13 L.sDstLen, .sub .x .x13 .x13 .x10, .ldrSp .x14 sD,
    .subs .x .x15 .x13 .x14, .csel .x .x14 .x14 .x13]

/-- `xorOut`, with the digest length read from `sD`. -/
def xorOut : Prog isa := .seq (.block (xorHead L sD)) (.loop (.block xorBody) (.nonzero .x .x14))

/-- `nextCtr`, with the digest length read from `sD`. -/
def nextCtr : List Instr :=
  [.addSp .x9 0, .ldrSp .x10 L.sCtr, .addImm .x .x10 .x10 1, .str .x .x10 .x9 L.sCtr, .ldrSp .x10 L.sDone,
    .ldrSp .x13 sD, .add .x .x10 .x10 .x13, .str .x .x10 .x9 L.sDone, .ldrSp .x11 L.sDstLen,
    .subs .x .x12 .x10 .x11, .sbc .x .x12 .x12 .x12]

/-- One block: the digest of `src ‖ I2OSP(c, 4)`, XORed into `dst`. -/
def round : Prog isa :=
  seqs [.block (initArgs L), tcall sTab 0 f.init, .block (updSrcArgs L), tcall sTab 1 f.upd,
    .block (updCtrArgs L), tcall sTab 1 f.upd, .block (finArgs L), tcall sTab 2 f.fin, xorOut L sD,
    .block (nextCtr L sD)]

/-- The table's address to `sTab`, and in `x10`. -/
def tabArg : List Instr := [.ldrSp .x10 sArg, .addSp .x9 0, .str .x .x10 .x9 sTab]

/-- The table's digest length (from the table at `x10`, as `tabArg` leaves
it) to `sD`, and the counter and `done` set to 0. -/
def tabHead : List Instr :=
  [.ldr .x .x10 .x10 32, .addSp .x9 0, .str .x .x10 .x9 sD,
    .movz .x .x10 0 0, .str .x .x10 .x9 L.sCtr, .str .x .x10 .x9 L.sDone]

/-- `dst ⊕= MGF1(src, dstLen)`, for `dstLen > 0`, with the hash function of
the table at `[sp + sArg]`. -/
def mgfXor : Prog isa :=
  seqs [.block (tabArg sArg sTab), .block (tabHead L sD), .loop (round L sTab sD f) (.nonzero .x .x12)]

end VG.Impl.RsaOaep.AArch64.Mgf1.Table
