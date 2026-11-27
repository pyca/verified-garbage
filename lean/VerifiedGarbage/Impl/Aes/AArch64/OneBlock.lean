module

public import VerifiedGarbage.Impl.Tbl.AArch64

/-!
# The AES S-box in the table registers, on AArch64

`setup` loads the S-box into the table registers `v16`–`v31` from a static
the code carries (`ldrqTbl`, `tabWords`: twenty loads, where immediates took
some 170 instructions on every call), for the key expansion
(`ExpandKey.lean`), whose bytes select from it with `tbl`, whose time does
not depend on its data (`Impl.Tbl.AArch64.select`): no secret is an address
or a branch condition. With it come ShiftRows' indices in `v4`
(`shiftIdx`) and the bytes `0x80`, `0x40` and `0x1b` in every byte of `v5`,
`v6` and `v7`: `select` takes the index XORed with 64, 128 and 192.

One block is encrypted by vector permutations (`Vperm.lean`).
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64.OneBlock

open VG.AArch64 VG.Impl.Tbl.AArch64

/-- ShiftRows as the indices of a `tbl`: byte `t` of the result is byte
`t mod 4 + 4 ((t / 4 + t mod 4) mod 4)` of the state. -/
def shiftIdx : BitVec 128 := ofVBytes fun t => BitVec.ofNat 8 (t % 4 + 4 * ((t / 4 + t % 4) % 4))

/-- The static that holds the tables and constants. -/
def tabName : String := "VG_AES_SBOX"

/-- Its vectors: the S-box, sixteen bytes each, then ShiftRows' indices and
the bytes `0x80`, `0x40` and `0x1b` in every byte. -/
def tabVec (j : Nat) : BitVec 128 :=
  if j < 16 then ofVBytes fun e => aesSbox (BitVec.ofNat 8 (16 * j + e))
  else if j = 16 then shiftIdx
  else if j = 17 then ofVBytes fun _ => 0x80
  else if j = 18 then ofVBytes fun _ => 0x40
  else ofVBytes fun _ => 0x1b

/-- The static's words: vector `j` at bytes `16 j` to `16 j + 15`. -/
def tabWords : List (BitVec 64) :=
  (List.range 40).map fun i => (tabVec (i / 2)).extractLsb' (64 * (i % 2)) 64

/-- Vector `j` of the static, at `x6`, into `r`. -/
def tld (r : VReg) (j : Nat) : Instr := .ldrqTbl r .x6 (16 * j) tabName tabWords

/-- The S-box into `v16`–`v31`, ShiftRows' indices into `v4`, and the bytes
`0x80`, `0x40` and `0x1b` into every byte of `v5`, `v6` and `v7`, loaded
from the static, whose address is in `x6`. -/
def setup : List Instr :=
  ([.adrSym .x6 tabName] : List Instr) ++ (((List.range 16).map fun r => tld (treg r) r) ++
    ([tld .v4 16, tld .v5 17, tld .v6 18, tld .v7 19] : List Instr))

end VG.Impl.Aes.AArch64.OneBlock
