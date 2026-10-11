module

public import VerifiedGarbage.Impl.Pbkdf2.Md.AArch64

/-!
# MGF1 (RFC 8017 Appendix B.2.1) for RSAES-OAEP on AArch64

`mgfXor`: `dst ⊕= MGF1(src, dstLen)` with a Merkle–Damgård hash function's
streaming functions (`init`, `update`, `finalize` of an
`Impl.Pbkdf2.Md.AArch64.Hash`), for a caller with a frame, as on x86-64
(`Impl/Mgf1/X86_64.lean`): the addresses and lengths are in the caller's
frame slots, and the hash function's state, the counter, the digest and the
working space of `update` and `finalize` in its working space (`scratch`,
whose address is in a slot), at the offsets of a `Layout`. Every length is
public.

For each counter `c` from 0, while `done = c hLen` is below `dstLen`: the
state is set by `init`, `update` absorbs `src` (`srcLen` bytes) and
`I2OSP(c, 4)` (written big-endian to `scratch + oCtr`), `finalize` writes
the digest to `scratch + oDig`, and its first `min(hLen, dstLen - done)`
bytes (selected with `csel`) are XORed into `dst + done`.

Only caller-saved registers are used, and nothing is kept in them across
a call: the slots `sCtr` and `sDone` hold the counter and `done`.
-/

@[expose] public section

namespace VG.Impl.RsaOaep.AArch64.Mgf1

open VG VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- `c₁; c₂; …`. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- Where the caller keeps what `mgfXor` uses: the frame slots (offsets
from `sp`) of `scratch`, `src`, `srcLen`, `dst`, `dstLen`, the counter and
`done`; and the offsets in `scratch` (each below 4096) of the hash
function's streaming state, the counter's four bytes, the digest, and the
working space of `update` and `finalize`. -/
structure Layout where
  sScr : Nat
  sSrc : Nat
  sSrcLen : Nat
  sDst : Nat
  sDstLen : Nat
  sCtr : Nat
  sDone : Nat
  oSt : Nat
  oCtr : Nat
  oDig : Nat
  oW : Nat

variable (L : Layout) (G : Hash)

/-- `d ← scratch + o`. -/
def scr (d : Reg) (o : Nat) : List Instr := [.ldrSp d L.sScr, .addImm .x d d o]

/-! ## One block of the mask -/

/-- `init(state)`. -/
def initArgs : List Instr := scr L .x0 L.oSt

/-- `update(state, 0, src, srcLen, work)`. -/
def updSrcArgs : List Instr :=
  scr L .x0 L.oSt ++ [.movz .x .x1 0 0, .ldrSp .x2 L.sSrc, .ldrSp .x3 L.sSrcLen] ++ scr L .x4 L.oW

/-- The counter, big-endian, to `scratch + oCtr`; then
`update(state, srcLen, scratch + oCtr, 4, work)`. -/
def updCtrArgs : List Instr :=
  scr L .x2 L.oCtr ++ [.ldrSp .x10 L.sCtr, .strb .x10 .x2 3, .lsr .x .x10 .x10 8, .strb .x10 .x2 2,
    .lsr .x .x10 .x10 8, .strb .x10 .x2 1, .lsr .x .x10 .x10 8, .strb .x10 .x2 0] ++
    scr L .x0 L.oSt ++ [.ldrSp .x1 L.sSrcLen, .movz .x .x3 4 0] ++ scr L .x4 L.oW

/-- `finalize(state, srcLen + 4, scratch + oDig, work)`. -/
def finArgs : List Instr :=
  scr L .x0 L.oSt ++ [.ldrSp .x1 L.sSrcLen, .addImm .x .x1 .x1 4] ++ scr L .x2 L.oDig ++ scr L .x3 L.oW

/-- The digest in `x11`, `dst + done` in `x12`, and in `x14`
`min(hLen, dstLen - done)`: `hLen` if the subtraction `dstLen - done - hLen`
does not borrow. -/
def xorHead : List Instr :=
  scr L .x11 L.oDig ++ [.ldrSp .x10 L.sDone, .ldrSp .x12 L.sDst, .add .x .x12 .x12 .x10,
    .ldrSp .x13 L.sDstLen, .sub .x .x13 .x13 .x10, .movz .x .x14 (BitVec.ofNat 16 G.D) 0,
    .subs .x .x15 .x13 .x14, .csel .x .x14 .x14 .x13]

/-- A byte of the digest XORed into `dst`. -/
def xorBody : List Instr :=
  [.ldrb .x10 .x11 0, .ldrb .x15 .x12 0, .logic .eor .x .x15 .x15 .x10, .strb .x15 .x12 0,
    .addImm .x .x11 .x11 1, .addImm .x .x12 .x12 1, .subImm .x .x14 .x14 1]

/-- The first `min(hLen, dstLen - done)` bytes of the digest XORed into
`dst + done`. -/
def xorOut : Prog isa := .seq (.block (xorHead L G)) (.loop (.block xorBody) (.nonzero .x .x14))

/-- The next counter and `done`, and in `x12` all ones while `done < dstLen`
(the borrow of `done - dstLen`), zero after. -/
def nextCtr : List Instr :=
  [.addSp .x9 0, .ldrSp .x10 L.sCtr, .addImm .x .x10 .x10 1, .str .x .x10 .x9 L.sCtr, .ldrSp .x10 L.sDone,
    .addImm .x .x10 .x10 G.D, .str .x .x10 .x9 L.sDone, .ldrSp .x11 L.sDstLen, .subs .x .x12 .x10 .x11,
    .sbc .x .x12 .x12 .x12]

/-- One block: the digest of `src ‖ I2OSP(c, 4)`, XORed into `dst`. -/
def round : Prog isa :=
  seqs [.block (initArgs L), .call G.initN G.initC, .block (updSrcArgs L), .call G.updN G.updC,
    .block (updCtrArgs L), .call G.updN G.updC, .block (finArgs L), .call G.finN G.finC, xorOut L G,
    .block (nextCtr L G)]

/-- `dst ⊕= MGF1(src, dstLen)`, for `dstLen > 0`. -/
def mgfXor : Prog isa :=
  .seq (.block [.addSp .x9 0, .movz .x .x10 0 0, .str .x .x10 .x9 L.sCtr, .str .x .x10 .x9 L.sDone])
    (.loop (round L G) (.nonzero .x .x12))

end VG.Impl.RsaOaep.AArch64.Mgf1
