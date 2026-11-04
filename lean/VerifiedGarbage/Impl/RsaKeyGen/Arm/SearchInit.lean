module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Starting the RSA prime search on ARMv7

`vg_rsa_prime_search_init(state = r0, prime_len = r1, e = r2, e_len = r3)`
(`VG.Spec.RsaKeyGen.primeInit`), as on AArch64
(`Impl/RsaKeyGen/AArch64/SearchInit.lean`): for a width `prime_len` a
multiple of 8 in 32..=512 and an exponent of 1 to 8 octets, the counted
candidates allowed (`40 prime_len`, or `64 prime_len` for an exponent of 3,
with any leading zeros), `prime_len`, the entropy budget `32769 prime_len`
and the first request `32 prime_len`, and 1 returned; otherwise four zeros
and 0 returned. Each `u64` word is two 32-bit stores, its high half zero:
every value is below `2 ^ 32`.

It uses only the argument registers and `r12`: the checks of the width and
of `e_len`, public arguments, branch; then the words but the first are
written, `prime_len` is read back from the state once `r1` has served as
the OR of `e`'s octets, and the first word is chosen without a branch.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.Arm.SearchInit

open VG VG.Arm

/-- `r12 := C`, and `Z` set iff the carry was clear. -/
def carryZ : List Instr := [.mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0), .cmp .r12 (.imm 0)]

/-- Zeros to the four words, and 0 returned. -/
def clear : List Instr := [
  .mov .r12 (.imm 0), .str .r12 .r0 0, .str .r12 .r0 4, .str .r12 .r0 8, .str .r12 .r0 12,
  .str .r12 .r0 16, .str .r12 .r0 20, .str .r12 .r0 24, .str .r12 .r0 28, .mov .r0 (.imm 0)]

/-- `check`, then zeros if `cond` holds, and `rest` otherwise. -/
def guard (check : List Instr) (cond : Cond) (rest : Prog isa) : Prog isa :=
  .seq (.block check) (.ite cond (.block clear) rest)

/-- `Z` iff `prime_len < 32`. -/
def checkLow : List Instr := .cmp .r1 (.imm 32) :: carryZ
/-- `Z` iff `512 < prime_len`. -/
def checkHigh : List Instr := [.mov .r12 (.imm 512), .cmp .r12 (.reg .r1)] ++ carryZ
/-- `Z` iff `prime_len` is a multiple of 8. -/
def checkMod : List Instr := [.dp .and .r12 .r1 (.imm 7), .cmp .r12 (.imm 0)]
/-- `Z` iff `e_len = 0`. -/
def checkEmpty : List Instr := [.cmp .r3 (.imm 0)]
/-- `Z` iff `8 < e_len`. -/
def checkLong : List Instr := [.mov .r12 (.imm 8), .cmp .r12 (.reg .r3)] ++ carryZ

/-- The high halves, and the words but the first: `prime_len`, the budget
`32769 prime_len` and the request `32 prime_len`. -/
def words : List Instr := [
  .mov .r12 (.imm 0), .str .r12 .r0 4, .str .r12 .r0 12, .str .r12 .r0 20, .str .r12 .r0 28,
  .str .r1 .r0 8, .mov .r12 (.shifted .r1 .lsl 15), .dp .add .r12 .r12 (.reg .r1), .str .r12 .r0 16,
  .mov .r12 (.shifted .r1 .lsl 5), .str .r12 .r0 24]

/-- One of `e`'s leading octets ORed into `r1`. -/
def leadStep : List Instr := [
  .ldrb .r12 .r2 0, .dp .orr .r1 .r1 (.reg .r12), .dp .add .r2 .r2 (.imm 1), .subs .r3 .r3 (.imm 1)]

/-- `r1` is 0 exactly when `e` (`e_len` octets at `r2`) is 3: the OR of its
leading octets and of its last octet XOR 3. -/
def isThree : Prog isa := .seq (.block [.mov .r1 (.imm 0), .subs .r3 .r3 (.imm 1)])
  (.seq (.ite .eq (.block []) (.loop (.block leadStep) .ne))
    (.block [.ldrb .r12 .r2 0, .dp .eor .r12 .r12 (.imm 3), .dp .orr .r1 .r1 (.reg .r12)]))

/-- `r1 := [e ≠ 3]`, from the OR in `r1`. -/
def notThree : List Instr := [.subs .r1 .r1 (.imm 1), .mov .r1 (.imm 0), .adc .r1 .r1 (.imm 0)]

/-- The first word, `64 prime_len - 24 prime_len · r1`, `prime_len` read
back from the state, and 1 returned. -/
def limitWord : List Instr := [
  .ldr .r12 .r0 8, .mov .r3 (.shifted .r12 .lsl 3), .dp .add .r3 .r3 (.shifted .r12 .lsl 4),
  .mul .r1 .r1 .r3, .mov .r12 (.shifted .r12 .lsl 6), .dp .sub .r12 .r12 (.reg .r1), .str .r12 .r0 0,
  .mov .r0 (.imm 1)]

def first : List Instr := notThree ++ limitWord

def valid : Prog isa := .seq (.block words) (.seq isThree (.block first))

def init : Prog isa :=
  guard checkLow .eq (guard checkHigh .eq (guard checkMod .ne
    (guard checkEmpty .eq (guard checkLong .eq valid))))

end VG.Impl.RsaKeyGen.Arm.SearchInit
