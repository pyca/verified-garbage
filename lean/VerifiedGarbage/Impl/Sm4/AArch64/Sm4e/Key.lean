module

public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Spec.Sm4

/-!
# The SM4 key schedule with the Armv8 SM4 instructions

`expandKey(key = x0, schedule = x1)`: `vg_sm4_expand_key_sm4`, with the
contract of `vg_sm4_expand_key` (`Spec/Sm4/Contract.lean`), for CPUs with
FEAT_SM4.

`sm4ekey vd, vn, vm` is four rounds of the key schedule on the state `vn`
with the four constants `CK` of `vm`, each word in a 32-bit lane: its result
is the four round keys of those rounds, and the state of the next four.

* The key is loaded into `v0`, its words made big-endian (`rev32 .16b`), and
  XORed with `FK`: `MK ⊕ FK`.
* Eight times: four words of `CK` into `v1`, `sm4ekey v0, v0, v1`, and `v0`,
  the round keys `rk₄ᵢ … rk₄ᵢ₊₃`, stored to the schedule at `16 i`.

`FK` and `CK` are a table of constants, eighteen doublewords, whose address
is in `x9` (`adrSym`) and which each `ldr q` carries (`ldrqTbl`: the emitter
writes it as a `static`).

`x0`, `x1` and `x9` hold public values; every address depends only on them,
and there is no branch. It uses no stack, writes no callee-saved register,
and no memory but the schedule.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64.Sm4e

open VG.AArch64

/-- The name of the table of the key schedule's constants. -/
def keyName : String := "VG_SM4_FK_CK"

/-- Word `i` of the constants: `FK`'s four, then `CK`'s thirty-two. -/
def keyWord (i : Nat) : BitVec 32 := if i < 4 then Spec.Sm4.fk.getD i 0 else Spec.Sm4.ck (i - 4)

/-- The table of constants: two words to a doubleword, the first in its low
half, so that words `4 i … 4 i + 3` are the lanes of the sixteen bytes at
`16 i`. -/
def keyTable : List (BitVec 64) := (List.range 18).map fun j => keyWord (2 * j + 1) ++ keyWord (2 * j)

/-- Words `4 i … 4 i + 3` of the constants, from the table at `x9`, into `v1`. -/
def kld (i : Nat) : Instr := .ldrqTbl .v1 .x9 (16 * i) keyName keyTable

/-- `MK ⊕ FK` in `v0`, and the table's address in `x9`. -/
def keyStart : List Instr :=
  [.ldrq .v0 .x0 0, .vop (.rev .rev32b .v0 .v0), .adrSym .x9 keyName, kld 0, .vop (.logic .eor .v0 .v0 .v1)]

/-- Rounds `4 i … 4 i + 3` of the key schedule, and their round keys to the
schedule. -/
def keyGroup (i : Nat) : List Instr := [kld (i + 1), .vop (.sm4ekey .v0 .v0 .v1), .strq .v0 .x1 (16 * i)]

/-- `vg_sm4_expand_key_sm4`. -/
def expandKey : Prog isa := .block (keyStart ++ (List.range 8).flatMap keyGroup)

end VG.Impl.Sm4.AArch64.Sm4e
