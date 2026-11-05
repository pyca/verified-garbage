module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.GenerateKey
public import VerifiedGarbage.Impl.Ffdh.RISCV64.VettedValidation

/-!
# FFDH key generation from a reusable public comb context on RISC-V

As on PPC64LE (`Impl/Ffdh/PPC64LE/Cached.lean`).

`vg_ffdh_generate_key_precompute(ctx = a0, ctx_len = a1, domain = a2,
domain_len = a3, p_len = a4, scratch = a5, scratch_len = a6)` writes
`Spec.Ffdh.generationPrecompute`: the public scalar width of
`Spec.Ffdh.generationScalarBits` (the vetted groups' widths,
`VettedValidation.recognize`, capped by the bound's bit length), its byte
length and the comb's row count, then `p` and `R² mod p`, then the 32
entries of the five-tooth comb in Montgomery form, each `w = ⌈p_len / 8⌉`
words.

`vg_ffdh_generate_key_cached(x = a0, x_len = a1, y = a2, y_len = a3,
domain = a4, domain_len = a5, p_len = a6, rand = a7, rand_len, scratch,
scratch_len, ctx, ctx_len)`, the last five on the stack, is
`vg_ffdh_derive_public`'s body (`Derive.lean`) on a scalar cut from `rand`
at the context's public width, with `g^x mod p` the comb's: one square and
one product per row, the product's entry read by scanning every entry of
the context under an equality mask. x's octets are then masked by the
status being 1 (`GenerateKey.maskX`).

Both run in the exchange's working space (`Impl/Ffdh/RISCV64.lean`):
array 0 `p`, array 1 `R² mod p`, arrays 2 and 3 the multiplications'; the
header's words 0–3 are the exchange's, the attempt keeps the context's
pointer and its three public words in words 4–7. Every loop count and every
address depends on the public width and indices alone; the context's
address is in `s10` wherever its rows are read or written.
-/

@[expose] public section

namespace VG.Impl.Ffdh.RISCV64.Cached

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Ffdh.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base saveRegs restore setup montOp)

/-- `c₁; c₂; …`. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-! ## Header words -/

def hCtx : Nat := 32
def hBits : Nat := 40
def hBytes : Nat := 48
def hRows : Nat := 56

/-- `rd :=` the address of row `j` (in `t2`) of the context at `s10`, rows of
`w` (`t0`) words after its three public words: `p` (`j = 0`), `R² mod p` (1),
then entry `e` (`2 + e`). -/
def rowPtr (rd : Reg) : List Instr :=
  [.mul .t2 .t2 .t0, .shift .sll .d .t2 .t2 3, .add rd .s10 .t2, .addi rd rd 24]

/-- Array `a`'s `w` words to the context's row `t2`. -/
def storeRow (a : Nat) : Prog isa := .seq (.block (rowPtr .t3 ++ base .t4 a)) Precompute.copyWords

/-- The context's row `t2` to array `a`'s `w` words. -/
def loadRow (a : Nat) : Prog isa := .seq (.block (rowPtr .t4 ++ base .t3 a)) Precompute.copyWords

namespace Precompute

/-- The registers saved at `scratch`; the context, the domain, `p_len` and
g's address in the header's words 0–3; the domain's arguments where
`recognize` reads them. -/
def front : List Instr :=
  [.addi .t0 .a5 0] ++ saveRegs ++
    [.store .d .a0 .s6 0, .store .d .a2 .s6 8, .store .d .a4 .s6 16, .add .t2 .a2 .a4, .store .d .t2 .s6 24,
      .addi .a0 .a2 0, .addi .a1 .a3 0, .addi .a2 .a4 0]

/-- After `recognize` (its width in `a5`): the domain back in `a2`, p's load
registers, and `setup` with the context in `s10`. -/
def post : List Instr :=
  [.addi .a2 .a0 0, .addi .s7 .a0 0, .addi .s8 .a4 0, .addi .a1 .a4 0, .load .d .a0 .s6 0] ++ setup

/-- `t2 += 1` if the octet `s2` exceeds `c`. -/
def blStep (c : Int) : List Instr := [.li .t3 c, .sltu .t3 .t3 .s2, .add .t2 .t2 .t3]

/-- `t2 :=` the bit length of the octet `s2`, without a branch. -/
def bitLen : List Instr :=
  [.li .t2 0] ++ blStep 0 ++ blStep 1 ++ blStep 3 ++ blStep 7 ++ blStep 15 ++ blStep 31 ++ blStep 63 ++
    blStep 127

/-- `s3 :=` the bound's bit length, from its first nonzero octet's index
`s1` and that octet `s2`. -/
def boundBl : List Instr :=
  bitLen ++ [.sub .s3 .a4 .s1, .shift .sll .d .s3 .s3 3, .addi .s3 .s3 (-8), .add .s3 .s3 .t2]

/-- `s3 :=` the bound's bit length: its first nonzero octet's index
(`GenerateKey`'s scan) and that octet's bit length. -/
def bound : Prog isa :=
  .seq GenerateKey.boundPtr (.seq (.block GenerateKey.scanSetup)
    (.seq (countLoop .t5 GenerateKey.scanBody) (.block boundBl)))

/-- `s9 :=` the recognized width (`a5`) if it is not zero and below the
bound's (`s3`), else the bound's. -/
def width : Prog isa :=
  .seq (.block [.sltu .t3 .a5 .s3])
    (.ite (.zero .a5) (.block [.addi .s9 .s3 0])
      (.ite (.zero .t3) (.block [.addi .s9 .s3 0]) (.block [.addi .s9 .a5 0])))

/-- The width (`s9`), its byte length and the comb's row count `⌈s9 / 5⌉`
(`(s9 + 4) · 52429 >> 18`) into the context's first three words; `s9 :=` the
rows. -/
def metadata : List Instr :=
  [.addi .t3 .s9 7, .shift .srl .d .t3 .t3 3, .addi .t4 .s9 4, .lui .t5 13, .addi .t5 .t5 (-819),
    .mul .t4 .t4 .t5, .shift .srl .d .t4 .t4 18, .store .d .s9 .s10 0, .store .d .t3 .s10 8,
    .store .d .t4 .s10 16, .addi .s9 .t4 0]

/-- p and `R² mod p` to the context's first two rows. -/
def storePrefix : Prog isa := seqs [.block [.li .t2 0], storeRow 0, .block [.li .t2 1], storeRow 1]

/-- g's octets (at `domain + p_len`) into array 4. -/
def loadG : Prog isa := .seq (.block [.add .a6 .s7 .s11]) PublicChecked.loadX

/-- Entry 0, Montgomery one (`R mod p`, from 1 in array 7), and entry 1,
`g R mod p`, which array 6 then keeps. -/
def initial : Prog isa := seqs [
  PublicChecked.one, montOp 6 1 7, .block [.li .t2 2], storeRow 6,
  loadG, montOp 5 4 1, .block [.li .t2 3], storeRow 5, ModExp.copy 6 5]

/-- Array 6 `:=` its `2^rows`-th power (`rows` in `s9`): the next tooth's
entry. -/
def squares : Prog isa := .seq (.block [.addi .s8 .s9 0])
  (.loop (.seq (montOp 6 6 6) (.block [.addi .s8 .s8 (-1)])) (.nonzero .s8))

/-- Entry `d + j :=` entry `j` (`s8`) times entry `d` (`s7`, array 6), for
`0 < j < d`. -/
def product : Prog isa := seqs [
  .block [.addi .t2 .s8 2], loadRow 5, montOp 5 5 6,
  .block [.add .t2 .s8 .s7, .addi .t2 .t2 2], storeRow 5,
  .block [.addi .s8 .s8 1, .sub .t2 .s8 .s7]]

/-- The tooth `d = 2^k` (`s7`) and the entries it adds to the ones below it. -/
def column : Prog isa := seqs [squares,
  .block [.addi .t2 .s7 2], storeRow 6,
  .block [.li .s8 1],
  .loop product (.nonzero .t2),
  .block [.add .s7 .s7 .s7, .addi .t2 .s7 (-32)]]

def table : Prog isa :=
  .seq initial (.seq (.block [.li .s7 2]) (.loop column (.nonzero .t2)))

/-- With p a valid modulus: the bound's bit length, the width and the
metadata, `R² mod p` (and `-p⁻¹ mod 2⁶⁴` in `t1`), the prefix and the
table. -/
def main : Prog isa :=
  seqs [bound, width, .block metadata, r2, storePrefix, table, .block [.li .a0 1]]

/-- `vg_ffdh_generate_key_precompute(ctx, ctx_len, domain, domain_len, p_len,
scratch, scratch_len)`. -/
def code : Prog isa :=
  .seq (.block front) (.seq VettedValidation.recognize (.seq (.block post)
    (.seq loadP (.seq (.ite (.zero .s0) main (.block [.li .a0 0])) (.block restore)))))

end Precompute

namespace Generate

/-- The context's pointer (`t1`) and its three public words into the
header's words 4–7. -/
def ctxHdr : List Instr :=
  [.load .d .t2 .t1 0, .load .d .t3 .t1 8, .load .d .t4 .t1 16, .store .d .t1 .s6 hCtx, .store .d .t2 .s6 hBits,
    .store .d .t3 .s6 hBytes, .store .d .t4 .s6 hRows]

/-- The working space and the context (the second and fourth arguments on the
stack), the registers saved, the context's header words, then
`GenerateKey.gkHdr` and `setup`. -/
def front : List Instr :=
  ([.addSp .t0 8, .load .d .t0 .t0 0, .addSp .t1 24, .load .d .t1 .t1 0] : List Instr) ++ saveRegs ++ ctxHdr ++
    GenerateKey.gkHdr ++ setup

/-- `s2 :=` the mask of the first octet's bits, `255 >> (8 bytes − bits)`,
and `s1 :=` the cut's index `p_len − bytes`; then `GenerateKey.cutSetup`. -/
def scalarBlock : List Instr :=
  [.load .d .t2 .s6 hBytes, .shift .sll .d .t2 .t2 3, .load .d .t3 .s6 hBits, .sub .t2 .t2 .t3, .li .s2 255,
    .shiftReg .srl .d .s2 .s2 .t2, .load .d .s1 .s6 hBytes, .sub .s1 .a4 .s1] ++ GenerateKey.cutSetup

/-- x := `rand`'s `p_len` octets cut to the context's width, then `s0 := 0`. -/
def scalar : Prog isa :=
  .seq (.block scalarBlock) (.seq (countLoop .t5 GenerateKey.cutBody) (.block [.li .s0 0]))

/-- `t5 :=` bit `k` (`t6`) of x, its `p_len` (`s11`) octets most significant
first at `s8`; 0 from `8 p_len` up. -/
def bit : Prog isa :=
  .seq (.block [.shift .sll .d .t2 .s11 3]) (.ite (.ltu .t6 .t2)
    (.block [.shift .srl .d .t2 .t6 3, .sub .t2 .s11 .t2, .addi .t2 .t2 (-1), .add .t2 .s8 .t2, .load .b .t5 .t2 0,
      .logicImm .and .t2 .t6 7, .shiftReg .srl .d .t5 .t5 .t2, .logicImm .and .t5 .t5 1])
    (.block [.li .t5 0]))

/-- Bit `j` of the digit in `a1`; `t6` to the next tooth's bit, `rows`
(`s7`) on. -/
def tooth (j : Nat) : Prog isa :=
  .seq bit (.block ((if j = 0 then [] else [.shift .sll .d .t5 .t5 j]) ++ [.logic .or .a1 .a1 .t5, .add .t6 .t6 .s7]))

/-- Row `i`'s digit into `a1`, for `i + 1` in `s9`. -/
def digit : Prog isa :=
  .seq (.block [.li .a1 0, .addi .t6 .s9 (-1)]) (seqs ((List.range 5).map tooth))

/-- `s4 :=` all ones if the entry `a3` is the digit `a1`, else 0 (both below
32). -/
def isEntry : List Instr :=
  [.logic .xor .t2 .a3 .a1, .addi .t2 .t2 (-1), .shift .srl .d .t2 .t2 63, .li .t3 0, .sub .s4 .t3 .t2]

/-- Entry `e` (`a3`) into array 3, then array `o :=` it if `e` is the digit
`d` (`a1`), else array `t`; `e` advanced. -/
def selEntry (o t : Nat) : Prog isa := seqs [
  .block ([.addi .t2 .a3 2] ++ rowPtr .t4 ++ base .t3 3), Precompute.copyWords,
  .block (isEntry ++ base .a5 3 ++ base .a6 t ++ base .a2 o), selectAcc64, .block [.addi .a3 .a3 1]]

/-- Array 4 `:=` the digit's entry, reading every entry: two at a time,
alternately into arrays 5 and 4, from 0 in array 4. -/
def select : Prog isa := seqs [
  .block (base .t3 4), Precompute.zeroWords, .block [.li .a3 0],
  .loop (seqs [selEntry 5 4, selEntry 4 5, .block [.addi .t2 .a3 (-32)]]) (.nonzero .t2)]

/-- One row: the square, the digit's entry and the product; `s9` counts the
rows left. -/
def step : Prog isa := seqs [montOp 6 6 6, digit, select, montOp 6 6 4, .block [.addi .s9 .s9 (-1)]]

/-- The comb's first block: the context into `s10`, x's address (the
header's word 1) into `s8`, the rows into `s7`, and `t2 := 1`. -/
def headBlock : List Instr := [.load .d .s10 .s6 hCtx, .load .d .s8 .s6 8, .load .d .s7 .s6 hRows, .li .t2 1]

/-- `g^x mod p` into array 4, by the context's comb: `-p⁻¹`, `R² mod p` from
the context, Montgomery one in array 6, the rows, then out of Montgomery
form. -/
def combRest : Prog isa := seqs [
  .block PublicChecked.minv, loadRow 1, PublicChecked.one, montOp 6 1 7,
  .block [.addi .s9 .s7 0], .loop step (.nonzero .s9), montOp 4 6 7]

def comb : Prog isa := .seq (.block headBlock) combRest

/-- x in range: `g^x mod p` to `y` or zeros, status 1 or 3. -/
def good : Prog isa := .seq comb (.seq exOut (.block Derive.status))

/-- After p's check: x, its range, the power, then zeros at x but for the
status 1. -/
def body : Prog isa :=
  .seq scalar (.seq (.seq Derive.xRange (.ite (.zero .s9) Derive.dpBad good)) GenerateKey.maskX)

/-- `vg_ffdh_generate_key_cached`. -/
def code : Prog isa :=
  .seq (.block front) (.seq loadP
    (.seq (.ite (.zero .s0) body (.block [.li .a0 0])) (.block restore)))

end Generate

end VG.Impl.Ffdh.RISCV64.Cached
