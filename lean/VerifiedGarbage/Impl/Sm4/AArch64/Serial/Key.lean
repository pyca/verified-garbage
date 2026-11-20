module

public import VerifiedGarbage.Impl.Sm4.AArch64.Serial.Core
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub

/-!
# The SM4 key schedule on AArch64, one word at a time

`expandKey(key = x0, schedule = x1)`: `vg_sm4_expand_key`. The key schedule
is one chain of 32 rounds, each of which needs the one before, so nothing is
gained by running sixteen copies of it bitsliced, as the ECB code runs
sixteen blocks: this is the single-block core's round
(`Impl/Sm4/AArch64/Serial/Core.lean`), with `L'` for `L` and `CK` for the
round keys, on `MK ⊕ FK` in `x6`–`x9`.

The S-box is in the table registers `v16`–`v31`, loaded by immediates
(`Impl.Tbl.AArch64.loadTable`), and the four bytes of a round's word select
from it with `tbl` (`substitute`), whose time does not depend on its data: no
secret is an address or a branch condition. Each round's word is stored to
the schedule as it is computed. Only `x6`–`x11`, `x15`, `v0`–`v6` and
`v16`–`v31` are written, and no memory but the schedule: there is no working
space.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64.Serial

open VG VG.AArch64

/-- `x10 := v`, a 32-bit constant. -/
def const32 (v : BitVec 32) : List Instr :=
  [.movz .w .x10 (v.extractLsb' 0 16) 0, .movk .w .x10 (v.extractLsb' 16 16) 1]

/-- Word `i` of the key, big-endian, XOR `FK`'s, into its register. -/
def loadKeyWord (i : Nat) : List Instr :=
  [.ldr .w (wordReg i) .x0 (4 * i), .rev32 (wordReg i) (wordReg i)] ++
    const32 (Spec.Sm4.fk.getD i 0) ++ [.logic .eor .w (wordReg i) (wordReg i) .x10]

/-- `x10 := CK_i ⊕ b ⊕ c ⊕ d`. -/
def keyInput (i : Nat) : List Instr :=
  const32 (Spec.Sm4.ck i) ++
    [.logic .eor .w .x10 .x10 (wordReg ((i + 1) % 4)), .logic .eor .w .x10 .x10 (wordReg ((i + 2) % 4)),
     .logic .eor .w .x10 .x10 (wordReg ((i + 3) % 4))]

/-- `x11 := L'(x10)`. -/
def keyLinear : List Instr :=
  [.logicRor .eor .w .x11 .x10 .x10 19, .logicRor .eor .w .x11 .x11 .x10 9]

/-- Round `i` of the key schedule, and its round key to the schedule. -/
def keyRound (i : Nat) : List Instr :=
  keyInput i ++ substitute ++ keyLinear ++ roundOutput i ++ [.str .w (wordReg (i % 4)) .x1 (4 * i)]

/-- `vg_sm4_expand_key`. -/
def expandKey : Prog isa :=
  .block (Impl.Tbl.AArch64.loadTable (fun k => Spec.Sm4.sbox.getD k 0) ++ quarterConstants ++
    (List.range 4).flatMap loadKeyWord ++ (List.range 32).flatMap keyRound)

namespace Fn

/-- `vg_sm4_expand_key` as emitted: `expandKey`, then its cleanup, which
clears the registers it writes that the calling convention does not preserve
(`Impl.Residue.AArch64.scrubAll`; it has no result and uses no stack), so
that it returns without secret residue. -/
def expandKey : Prog isa :=
  Residue.AArch64.scrubAll 0 0
    ⟨[.x6, .x7, .x8, .x9, .x10, .x11, .x15],
     [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24,
      .v25, .v26, .v27, .v28, .v29, .v30, .v31],
     []⟩
    Serial.expandKey

end Fn

end VG.Impl.Sm4.AArch64.Serial
