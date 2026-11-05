module

public import VerifiedGarbage.Impl.Bignum.X86.PublicRt

/-! # Starting the RSA prime search on i686

`vg_rsa_prime_search_init(state, prime_len, e, e_len)`
(`VG.Spec.RsaKeyGen.primeInit`), as on AArch64
(`Impl/RsaKeyGen/AArch64/SearchInit.lean`): for a width `prime_len` a
multiple of 8 in 32..=512 and an exponent of 1 to 8 octets, the counted
candidates allowed (`40 prime_len`, or `64 prime_len` for an exponent of 3,
with any leading zeros), `prime_len`, the entropy budget `32769 prime_len`
and the first request `32 prime_len`, and 1 returned; otherwise four zeros
and 0 returned. Each `u64` word is two 32-bit stores, its high half zero:
every value is below `2 ^ 32`.

The checks of the width and of `e_len`, public arguments, branch, with
`eax`, `ecx` and `edx`. A valid start saves `ebx`, which it needs for the
octets of `e`, in the first word (the contract leaves it no stack to push
it to) and writes the others. The OR of `e`'s leading octets and of its last
octet XOR 3 is 0 exactly when `e` is 3; from it the first word is chosen
without a branch, and written once `ebx` is restored from it. The products
come from `mul`, which the baseline ISA has.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.X86.SearchInit

open VG VG.X86
open VG.Impl.Mont.X86 (at_)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- `[edx + 4 j] := r`: word `j` of the state, 32 bits of it. -/
def st (j : Nat) (r : Reg) : Instr := .store (at_ .edx (4 * j)) r

/-- Argument `i` (`state, prime_len, e, e_len`). -/
def param (i : Nat) : MemOp := argAt 0 i

/-- Zeros to the four words, and 0 returned. -/
def clear : List Instr :=
  [.mov .edx (.mem (param 0)), .mov .eax (.imm 0), st 0 .eax, st 1 .eax, st 2 .eax, st 3 .eax,
    st 4 .eax, st 5 .eax, st 6 .eax, st 7 .eax]

/-- `check`, then zeros if `cond` holds, and `rest` otherwise. -/
def guard (check : List Instr) (cond : Cond) (rest : Prog isa) : Prog isa :=
  .seq (.block check) (.ite cond (.block clear) rest)

/-- `CF` iff `prime_len < 32`. -/
def checkLow : List Instr := [.mov .ecx (.mem (param 1)), .alu .cmp .ecx (.imm 32)]
/-- `CF` clear iff `512 < prime_len`. -/
def checkHigh : List Instr := [.alu .cmp .ecx (.imm 513)]
/-- `ZF` iff `prime_len` is a multiple of 8. -/
def checkMod : List Instr := [.alu .test .ecx (.imm 7)]
/-- `CF` iff `e_len = 0`. -/
def checkEmpty : List Instr := [.mov .edx (.mem (param 3)), .alu .cmp .edx (.imm 1)]
/-- `CF` clear iff `8 < e_len`. -/
def checkLong : List Instr := [.alu .cmp .edx (.imm 9)]

/-- `[ebx + 4 j] := r`. -/
def stB (j : Nat) (r : Reg) : Instr := .store (at_ .ebx (4 * j)) r

/-- `ebx` saved in the first word, then the state's pointer; the high
halves, and the words but the first: `prime_len`, the budget
`32769 prime_len` and the request `32 prime_len` (`ecx` is `prime_len`). -/
def words : List Instr :=
  [.mov .edx (.mem (param 0)), st 0 .ebx, .mov .ebx (.reg .edx), .mov .eax (.imm 0), stB 1 .eax,
    stB 3 .eax, stB 5 .eax, stB 7 .eax, stB 2 .ecx, .mov .eax (.imm 32769), .mul .ecx, stB 4 .eax,
    .mov .eax (.imm 32), .mul .ecx, stB 6 .eax]

/-- One of `e`'s leading octets ORed into `eax`. -/
def leadStep : List Instr :=
  [.movzx8 .ebx (at_ .ecx 0), .alu .or .eax (.reg .ebx), .alu .add .ecx (.imm 1), .alu .sub .edx (.imm 1)]

/-- `eax` is 0 exactly when `e` (`e_len` octets) is 3: the OR of its leading
octets and of its last octet XOR 3. -/
def isThree : Prog isa :=
  .seq (.block [.mov .ecx (.mem (param 2)), .mov .edx (.mem (param 3)), .mov .eax (.imm 0),
      .alu .sub .edx (.imm 1)])
    (.seq (.ite .e (.block []) (.loop (.block leadStep) .ne))
      (.block [.movzx8 .ebx (at_ .ecx 0), .alu .xor .ebx (.imm 3), .alu .or .eax (.reg .ebx)]))

/-- `eax := 40 prime_len + (24 prime_len if e is 3)`, `ecx` then `prime_len`:
`ebx`, all ones when `eax` was 0, masks `24 prime_len`. -/
def limit : List Instr :=
  [.alu .cmp .eax (.imm 1), .alu .sbb .ebx (.reg .ebx), .mov .ecx (.mem (param 1)),
    .mov .eax (.imm 24), .mul .ecx, .alu .and .ebx (.reg .eax),
    .mov .eax (.imm 40), .mul .ecx, .alu .add .eax (.reg .ebx)]

/-- `ebx` restored from word 0, the first word, and 1 returned. -/
def first : List Instr :=
  limit ++ [.mov .edx (.mem (param 0)), .mov .ebx (.mem (at_ .edx 0)), st 0 .eax, .mov .eax (.imm 1)]

def valid : Prog isa := .seq (.block words) (.seq isThree (.block first))

def init : Prog isa :=
  guard checkLow .b (guard checkHigh .ae (guard checkMod .ne
    (guard checkEmpty .b (guard checkLong .ae valid))))

end VG.Impl.RsaKeyGen.X86.SearchInit
