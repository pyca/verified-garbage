module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.GenerateKey
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.VettedValidation
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.KeyGeneration.Search
public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Round

/-!
# FFDH key generation from a reusable public comb context on PPC64LE

`vg_ffdh_generate_key_precompute` writes `Spec.Ffdh.generationPrecompute`:
the public scalar width of `Spec.Ffdh.generationScalarBits` (the vetted
groups' widths, `VettedValidation.recognize`, capped by the bound's bit
length), its byte length and the comb's row count, then `p` and `R² mod p`,
then the 32 entries of the five-tooth comb in Montgomery form, each
`w = ⌈p_len / 8⌉` words.

`vg_ffdh_generate_key_cached` is `vg_ffdh_generate_key`'s attempt
(`GenerateKey.lean`) with two stages replaced: the scalar is cut at the
context's public width rather than at the bound's first byte, and
`g^x mod p` is the comb's: one square and one product per row, the product's
entry read by scanning every entry of the table under an equality mask.

`vg_ffdh_generate_key_search_cached` is the existing controller around it,
which also passes the context.

All of it runs in `Domain.lean`'s working space: array 0 `p`, array 1
`R² mod p`, arrays 2 and 3 the multiplication's, and the header's free words
(below the arguments at 64–88 and the saved registers from 112) hold the
context's pointer and the comb's public counters. Every loop count and every
address depends on the public width and indices alone.
-/

@[expose] public section

namespace VG.Impl.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Bignum.PPC64LE.PublicChecked (base montOp)

/-- `c₁; c₂; …`. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-! ## Header words -/

def hCtx : Nat := 0
def hBits : Nat := 8
def hBytes : Nat := 16
def hRows : Nat := 24
def hI : Nat := 32
def hD : Nat := 40
def hJ : Nat := 48
def hCap : Nat := 96

def ldh (r : Reg) (o : Nat) : Instr := .load .d r .r23 o
def sth (r : Reg) (o : Nat) : Instr := .store .d r .r23 o

/-- `r8 := ctx + 24 + 8 w j` for the public row `j` in `r3`: `p` (`j = 0`),
`R² mod p` (1), then entry `e` of the table (`2 + e`). -/
def rowPtr : List Instr :=
  [ldh .r8 hCtx, .lsr .d .r9 .r11 1, .mul .r9 .r9 .r3, .lsl .r9 .r9 3, .add .r8 .r8 .r9,
    .addi .r8 .r8 24]

/-- Array `a`'s `w` words to the context's row `r3`. -/
def storeRow (a : Nat) : Prog isa :=
  .seq (.block (rowPtr ++ [.addi .r14 .r8 0] ++ base .r15 a)) VG.Impl.Bignum.PPC64LE.Precompute.copyWords

/-- The context's row `r3` to array `a`'s `w` words. -/
def loadRow (a : Nat) : Prog isa :=
  .seq (.block (rowPtr ++ [.addi .r15 .r8 0] ++ base .r14 a)) VG.Impl.Bignum.PPC64LE.Precompute.copyWords

namespace Precompute

/-- `(ctx, ctx_len, domain, domain_len, p_len, scratch, scratch_len)`: the
registers saved at `scratch`, the context's pointer in the header, and the
domain where `recognize` reads it. -/
def front : List Instr :=
  Domain.save .r8 ++ [sth .r3 hCtx, .addi .r3 .r5 0, .addi .r4 .r6 0, .addi .r5 .r7 0]

/-- `r16 :=` the bound's bit length: its first nonzero octet's index
(`GenerateKey`'s scan) and that octet's bit length. -/
def boundBits : Prog isa :=
  .seq GenerateKey.boundPtr (.seq (.block GenerateKey.scanSetup)
    (.seq (VG.Impl.Bignum.PPC64LE.Precompute.countLoop .r6 GenerateKey.scanBody)
      (.seq (.block [.li .r15 0])
        (.seq (.loop (.block [.lsr .d .r14 .r14 1, .addi .r15 .r15 1]) (.nonzero .d .r14))
          (.block [.sub .r16 .r28 .r22, .lsl .r16 .r16 3, .subi .r16 .r16 8, .add .r16 .r16 .r15])))))

/-- `r16 :=` the recognized width if it is not zero and below the bound's. -/
def width : Prog isa :=
  .seq (.block [ldh .r8 hCap, .sub .r9 .r8 .r16, .lsr .d .r9 .r9 63])
    (.ite (.zero .d .r8) (.block []) (.ite (.zero .d .r9) (.block []) (.block [.addi .r16 .r8 0])))

/-- `r18 :=` `⌈r16 / 5⌉` (at least 1), by subtracting 5 from `r19`. -/
def rows : Prog isa :=
  .seq (.block [.addi .r19 .r16 0, .li .r18 0])
    (.loop (.block [.subi .r19 .r19 5, .addi .r18 .r18 1, .li .r0 0, .sub .r0 .r0 .r19, .lsr .d .r0 .r0 63])
      (.nonzero .d .r0))

/-- The three metadata words, in the header and the context. -/
def metadata : Prog isa :=
  .seq (.block [sth .r16 hBits, .addi .r17 .r16 7, .lsr .d .r17 .r17 3, sth .r17 hBytes])
    (.seq rows (.block [sth .r18 hRows, ldh .r8 hCtx, .store .d .r16 .r8 0, .store .d .r17 .r8 8,
      .store .d .r18 .r8 16]))

/-- `R² mod p` into array 1 and `-p⁻¹ mod 2³²` into `r12`. -/
def montgomery : Prog isa :=
  .seq (.block (base .r5 1 ++ base .r8 2 ++ base .r9 3)) (.seq VG.Impl.Bignum.PPC64LE.Precompute.r2
    (.block PublicChecked.minv))

/-- `p` and `R² mod p` to the context's first two rows. -/
def storePrefix : Prog isa :=
  .seq (.block [.li .r3 0]) (.seq (storeRow 0) (.seq (.block [.li .r3 1]) (storeRow 1)))

/-- g's octets into array 4, and `r10` back to array 0. -/
def loadG : Prog isa :=
  .seq (.block ([.add .r12 .r21 .r28, .addi .r6 .r28 0] ++ base .r10 4))
    (.seq VG.Impl.Bignum.PPC64LE.Precompute.loadN (.block [.addi .r10 .r23 hdrBytes]))

/-- Entry 0, Montgomery one (`R mod p`, from 1 in array 7), and entry 1,
`g R mod p`, which array 6 then keeps. -/
def initial : Prog isa := seqs [
  PublicChecked.one, montOp 6 1 7, .block [.li .r3 2], storeRow 6,
  loadG, .block PublicChecked.minv, montOp 5 4 1, .block [.li .r3 3], storeRow 5, ModExp.copy 6 5]

/-- Array 6 `:= ` its `2^rows`-th power: the next tooth's entry. -/
def squares : Prog isa := .seq (.block [ldh .r3 hRows, sth .r3 hI])
  (.loop (.seq (montOp 6 6 6) (.block [ldh .r3 hI, .subi .r3 .r3 1, sth .r3 hI])) (.nonzero .d .r3))

/-- Entry `d + j :=` entry `j` times entry `d` (array 6), for `0 < j < d`. -/
def product : Prog isa := seqs [
  .block [ldh .r3 hJ, .addi .r3 .r3 2], loadRow 5, montOp 5 5 6,
  .block [ldh .r3 hJ, ldh .r4 hD, .add .r3 .r3 .r4, .addi .r3 .r3 2], storeRow 5,
  .block [ldh .r3 hJ, .addi .r3 .r3 1, sth .r3 hJ, ldh .r4 hD, .sub .r3 .r3 .r4]]

/-- The tooth `d = 2^k` and the entries it adds to the ones below it. -/
def column : Prog isa := seqs [squares,
  .block [ldh .r3 hD, .addi .r3 .r3 2], storeRow 6,
  .block [.li .r3 1, sth .r3 hJ],
  .loop product (.nonzero .d .r3),
  .block [ldh .r3 hD, .add .r3 .r3 .r3, sth .r3 hD, .subi .r3 .r3 32]]

def table : Prog isa :=
  .seq initial (.seq (.block [.li .r3 2, sth .r3 hD]) (.loop column (.nonzero .d .r3)))

/-- With p a valid modulus: the width and the metadata, `R² mod p`, the
prefix and the table. -/
def main : Prog isa :=
  seqs [boundBits, width, metadata, montgomery, storePrefix, table, .block [.li .r3 1]]

/-- `vg_ffdh_generate_key_precompute(ctx, ctx_len, domain, domain_len, p_len,
scratch, scratch_len)`. -/
def code : Prog isa :=
  .seq (.block front) (.seq VettedValidation.recognize (.seq (.block ([sth .r8 hCap] ++ Domain.setup))
    (.seq loadP (.seq (.ite (.zero .d .r0) main (.block [.li .r3 0])) (.block Domain.restore)))))

end Precompute

namespace Generate

/-- The context's pointer (`r12`) and its three metadata words into the header. -/
def ctxHdr : List Instr :=
  [.load .d .r0 .r12 0, .load .d .r6 .r12 8, .load .d .r11 .r12 16, sth .r12 hCtx, sth .r0 hBits, sth .r6 hBytes,
    sth .r11 hRows]

/-- `vg_ffdh_generate_key_cached(x, x_len, y, y_len, domain, domain_len,
p_len, rand, rand_len, scratch, scratch_len, ctx, ctx_len)`, the last five on
the stack: `GenerateKey.gkFront` with the context's pointer and its three
metadata words in the header. -/
def front : List Instr :=
  ([.addSp .r11 104, .load .d .r11 .r11 0] : List Instr) ++ ([.addSp .r12 120, .load .d .r12 .r12 0] : List Instr) ++
    save .r11 ++ ctxHdr ++
    ([.store .d .r3 .r23 64, .store .d .r4 .r23 72, .store .d .r5 .r23 80, .store .d .r10 .r23 88,
      .addi .r3 .r7 0, .addi .r4 .r8 0, .addi .r5 .r9 0] : List Instr) ++ setup

/-- `r14 :=` the mask of the first octet's bits, `255 >> (8 bytes − bits)`. -/
def maskByte : Prog isa :=
  .seq (.block [ldh .r17 hBytes, .lsl .r17 .r17 3, ldh .r18 hBits, .sub .r17 .r17 .r18, .li .r14 255])
    (.ite (.zero .d .r17) (.block [])
      (.loop (.block [.lsr .d .r14 .r14 1, .subi .r17 .r17 1]) (.nonzero .d .r17)))

/-- x := `rand`'s `p_len` octets cut to the context's width: `GenerateKey`'s
cut at the index `p_len − bytes` (`r22`) with the mask `r14`. -/
def scalar : Prog isa :=
  .seq maskByte (.seq (.block ([ldh .r22 hBytes, .sub .r22 .r28 .r22] ++ GenerateKey.ptrs ++
    GenerateKey.cutSetup)) (VG.Impl.Bignum.PPC64LE.Precompute.countLoop .r6 GenerateKey.cutBody))

/-- `r20 :=` bit `k` of x (`r19 := k = i − 1 + j rows`), its `p_len` octets
most significant first at the header's word 8; 0 from `8 p_len` up. -/
def bit (j : Nat) : Prog isa :=
  .seq (.block [ldh .r19 hI, .subi .r19 .r19 1, ldh .r18 hRows, .li .r0 j, .mul .r18 .r18 .r0,
      .add .r19 .r19 .r18, .load .d .r17 .r23 64, .lsl .r18 .r28 3, .sub .r18 .r19 .r18, .lsr .d .r18 .r18 63])
    (.ite (.zero .d .r18) (.block [.li .r20 0])
      (.seq (.block [.lsr .d .r18 .r19 3, .sub .r18 .r28 .r18, .subi .r18 .r18 1,
          .add .r17 .r17 .r18, .lbz .r20 .r17 0, .li .r0 7, .logic .and .r18 .r19 .r0])
        (.seq (.ite (.zero .d .r18) (.block [])
            (.loop (.block [.lsr .d .r20 .r20 1, .subi .r18 .r18 1]) (.nonzero .d .r18)))
          (.block [.li .r0 1, .logic .and .r20 .r20 .r0]))))

/-- Bit `j` of the digit in `r16`. -/
def tooth (j : Nat) : Prog isa :=
  .seq (bit j) (.block ((if j = 0 then [] else [.lsl .r20 .r20 j]) ++ [.logic .or .r16 .r16 .r20]))

/-- Row `i − 1`'s digit into the header. -/
def digit : Prog isa :=
  .seq (.block [.li .r16 0]) (.seq (seqs ((List.range 5).map tooth)) (.block [sth .r16 hD]))

/-- Entry `e` (the header's `hJ`) into array 3, then array `o :=` it if
`e = d`, else array `t`; `e` advanced. -/
def selEntry (o t : Nat) : Prog isa :=
  .seq (.block [ldh .r3 hJ, .addi .r3 .r3 2]) (.seq (loadRow 3)
    (.seq (.block [ldh .r4 hJ, ldh .r0 hD, .logic .xor .r4 .r4 .r0, .subi .r4 .r4 1, .lsr .d .r4 .r4 63,
        .li .r0 0, .sub .r20 .r0 .r4])
      (.seq (VG.Impl.MillerRabin.PPC64LE.sel o 3 t) (.block [ldh .r3 hJ, .addi .r3 .r3 1, sth .r3 hJ]))))

/-- Array 4 `:=` the digit's entry, reading every entry: two at a time,
alternately into arrays 5 and 4, from 0 in array 4. -/
def select : Prog isa :=
  .seq (.block (base .r14 4)) (.seq VG.Impl.Bignum.PPC64LE.Precompute.zeroWords
    (.seq (.block [.li .r3 0, sth .r3 hJ])
      (.loop (.seq (selEntry 5 4) (.seq (selEntry 4 5) (.block [ldh .r3 hJ, .subi .r3 .r3 32])))
        (.nonzero .d .r3))))

/-- One row: the square, the digit's entry and the product. -/
def step : Prog isa := seqs [montOp 6 6 6, digit, select, montOp 6 6 4,
  .block [ldh .r3 hI, .subi .r3 .r3 1, sth .r3 hI]]

/-- `g^x mod p` into array 4, by the context's comb: `R² mod p` from the
context, `-p⁻¹`, Montgomery one in array 6, the rows, then out of Montgomery
form. -/
def comb : Prog isa := seqs [
  .block [.li .r3 1], loadRow 1, .block PublicChecked.minv, PublicChecked.one, montOp 6 1 7,
  .block [ldh .r3 hRows, sth .r3 hI], .loop step (.nonzero .d .r3), montOp 4 6 7]

/-- x in range: `g^x mod p` to `y` or zeros, status 1 or 3. -/
def good : Prog isa := .seq comb (.seq exOut (.block Derive.status))

/-- After p's check: x, its range, the power, then zeros at x but for the
status 1. -/
def body : Prog isa :=
  .seq scalar (.seq (.seq Derive.xRange (.ite (.zero .d .r26) Derive.dpBad good)) GenerateKey.maskX)

/-- `vg_ffdh_generate_key_cached`. -/
def code : Prog isa :=
  .seq (.block front) (.seq loadP
    (.seq (.ite (.zero .d .r0) body (.block [.li .r3 0])) (.block Domain.restore)))

end Generate

namespace Search

open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search

/-- The attempt's arguments, and the context's two (the controller's
fourteenth and fifteenth, above its frames of 48 and 144 bytes) as its
twelfth and thirteenth, at offsets 24 and 32 of its stack arguments. -/
def cachedArguments : List Instr := arguments ++
  [.addSp .r12 328, .load .d .r0 .r12 0, .store .d .r0 .r11 24, .load .d .r0 .r12 8,
    .store .d .r0 .r11 32]

variable (attempt : Prog isa)

/-- The attempt in a frame of its five stack arguments. -/
def attemptRun : Prog isa := .frame (.alloc 144) (.seq (.block cachedArguments) attempt) (.free 144)

def attemptOrRequest : Prog isa := .seq (.block room)
  (.ite (.zero .d .r12) (.seq (attemptRun attempt) classify) request)

def branch : Prog isa :=
  .ite (.zero .d .r9) exhausted (.seq (.block [ldf .r9 1])
    (.ite (.zero .d .r9) exhausted (attemptOrRequest attempt)))

def iteration : Prog isa :=
  .seq (.block [ldf .r9 0]) (.seq (branch attempt) (.block [ldf .r9 14, .subi .r9 .r9 4]))

def search : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq (.frame (.push .r0) (.loop (iteration attempt) (.zero .d .r9)) (.pop .r0)) (.block [.mtlr .r0]))

def code : Prog isa := .seq (.block entry) (.seq (search attempt) (.block finish))

end Search

end VG.Impl.Ffdh.PPC64LE.Cached
