module

public import VerifiedGarbage.Impl.Ffdh.X86.KeySearch
public import VerifiedGarbage.Impl.Ffdh.X86.VettedValidation
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract

/-!
# FFDH on i686: key generation from a reusable public comb context

`vg_ffdh_generate_key_precompute` writes `Spec.Ffdh.generationPrecompute`
at `ctx`: the public scalar width of `Spec.Ffdh.generationScalarBits` (the
vetted groups' recognized width, `VettedValidation.scan`, capped by the
bound's bit length, from `GenerateKey.scan`), its byte length and the comb's
row count, then `p` and `R² mod p`, then the 32 entries of the five-tooth
comb in Montgomery form, each a row of `B` bytes. Rows are copied to and
from the wide slots by `selectLoop` under an all-ones mask.

`vg_ffdh_generate_key_cached` is `vg_ffdh_generate_key`'s attempt with two
stages replaced: the scalar is cut at the context's public width rather than
at the bound's first byte (`metaCut`, for `GenerateKey.cut`), and `g^x mod p`
is the comb's (`comb`): one square and one product per row, with the row's
entry read by scanning every entry of the table under an equality mask. The
digit is kept in the window word, and every address, count and branch
depends on the public width alone.

`vg_ffdh_generate_key_search_cached` is `vg_ffdh_generate_key_search`'s
controller, which also passes the context.

The context's pointer is synthetic argument 13. The header words past the
callee-saved registers keep the public counters: the recognized width
(48), the width (52), the rows (56), the tooth's entry (60), the product's
entry (64) and the row (68).
-/

@[expose] public section
namespace VG.Impl.Ffdh.X86.Cached
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- Wide slot `j`. -/
local notation:max "sl " j:max => Loc.slot Ctx.wide j
/-- A number of the wide context. -/
local notation "n1" => one Ctx.wide

/-- The programs in order. -/
def seqs (xs : List (Prog isa)) : Prog isa := xs.foldr .seq (.block [])

def recOff : Nat := 48
def bitsOff : Nat := 52
def rowsOff : Nat := 56
def dOff : Nat := 60
def jOff : Nat := 64
def iOff : Nat := 68

/-- The synthetic argument of the context's pointer. -/
def ctxArg : Nat := 13

/-- `r :=` the context's row in `eax` (public): `ctx + 24 + B row`; `eax` and `edx` change. -/
def rowAt (r : Reg) : List Instr :=
  widthC 0 .wide .edx ++ [.mul .edx, .alu .add .eax (.mem (argAt 0 ctxArg)), .alu .add .eax (.imm 24),
    .mov r (.reg .eax)]

/-- Slot `a` to the context's row that `idx` leaves in `eax`. -/
def storeRow (idx : List Instr) (a : Nat) : Prog isa :=
  .seq (.block (idx ++ rowAt .ebx ++ [.mov .ecx (.imm (BitVec.allOnes 32))] ++ ptrTo (sl a) .ebp .edx ++
    cntTo n1 .edi)) (.seq selectLoop (.block restoreEdi))

/-- The context's row that `idx` leaves in `eax` to slot `a`. -/
def loadRow (idx : List Instr) (a : Nat) : Prog isa :=
  .seq (.block (idx ++ rowAt .ebp ++ [.mov .ecx (.imm (BitVec.allOnes 32))] ++ ptrTo (sl a) .ebx .edx ++
    cntTo n1 .edi)) (.seq selectLoop (.block restoreEdi))

/-- `eax := k`. -/
def rowImm (k : Nat) : List Instr := [.mov .eax (.imm (BitVec.ofNat 32 k))]

/-- `eax :=` the header word at `d` plus `k`. -/
def rowWord (d k : Nat) : List Instr := [.mov .eax (.mem (sc d)), .alu .add .eax (.imm (BitVec.ofNat 32 k))]

namespace Precompute

/-- `(ctx, ctx_len, domain, domain_len, p_len, scratch, scratch_len)`. -/
def args : Args := { dom := 2, dlen := 3, plen := 4, ws := 5, ctx := some 0 }

/-- The domain, its length and `p_len` (synthetic arguments 2, 12 and 1) as the scan's arguments. -/
def scanArgs : List Instr :=
  [.mov .eax (.mem (argAt 4 2)), .store (at_ .esp 4) .eax, .mov .eax (.mem (argAt 4 12)),
    .store (at_ .esp 8) .eax, .mov .eax (.mem (argAt 4 1)), .store (at_ .esp 12) .eax]

/-- The recognized width (0 for any other domain) to its header word. -/
def recognize : Prog isa :=
  .seq (.block [.mov .ebx (.reg .edi)]) <|
  .seq VettedValidation.tableAddress <|
  .seq (.block VettedValidation.saveTable) <|
  .seq (.frame (.alloc 16) (.seq (.block scanArgs) (VettedValidation.scan VettedGroups.groups 0)) (.free 16))
    (.block (restoreEdi ++ [.store (sc recOff) .eax]))

/-- `eax :=` the bit length of the bound's first nonzero byte, from its mask (not zero). -/
def maskBits : Prog isa :=
  .seq (.block [.mov .eax (.imm 0), .mov .ecx (.mem (sc tOff))])
    (.loop (.block [.alu .add .eax (.imm 1), .shift .shr .ecx 1, .alu .test .ecx (.reg .ecx)]) .ne)

/-- `eax :=` the bound's bit length, `8 (p_len − 1 − ld)` plus its first byte's. -/
def boundBits : List Instr :=
  [.mov .ecx (.mem (argAt 0 3)), .alu .sub .ecx (.imm 1), .alu .sub .ecx (.mem (sc ldOff)),
    .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .eax (.reg .ecx)]

/-- `eax :=` the recognized width where it is not zero and below `eax`. -/
def cap : Prog isa :=
  .seq (.block [.mov .edx (.mem (sc recOff)), .alu .test .edx (.reg .edx)])
    (.ite .e (.block []) (.seq (.block [.alu .cmp .edx (.reg .eax)]) (.ite .b (.block [.mov .eax (.reg .edx)]) (.block []))))

/-- The three metadata words, 64 bits each: the width, its bytes and `⌈width / 5⌉` rows
(`⌊(width + 4) 52429 / 2^18⌋`, exact below `2^18`); the width and the rows also to the header. -/
def metadata : List Instr :=
  [.store (sc bitsOff) .eax, .mov .ecx (.mem (argAt 0 ctxArg)), .store (at_ .ecx 0) .eax,
    .mov .edx (.reg .eax), .alu .add .edx (.imm 7), .shift .shr .edx 3, .store (at_ .ecx 8) .edx,
    .alu .add .eax (.imm 4), .mov .edx (.imm 52429), .mul .edx, .shift .shr .eax 18,
    .store (sc rowsOff) .eax, .mov .ecx (.mem (argAt 0 ctxArg)), .store (at_ .ecx 16) .eax,
    .mov .eax (.imm 0), .store (at_ .ecx 4) .eax, .store (at_ .ecx 12) .eax, .store (at_ .ecx 20) .eax]

/-- Entry 0, Montgomery one (slot 6), and entry 1, `g R mod p` (slot 7, which keeps it). -/
def initial : List (Prog isa) :=
  [mul .wide 6 4 3, storeRow (rowImm 2) 6, copy (sl 10) (sl 5) n1, mul .wide 7 5 4, storeRow (rowImm 3) 7]

/-- Slot 7 to the power `2^rows`: the next tooth's entry from the last. -/
def squares : Prog isa := .seq (.block [.mov .eax (.mem (sc rowsOff)), .store (sc iOff) .eax])
  (.loop (.seq (mul .wide 7 7 7)
    (.block [.mov .eax (.mem (sc iOff)), .alu .sub .eax (.imm 1), .store (sc iOff) .eax])) .ne)

/-- Entry `d + j :=` entry `j` times entry `d` (slot 7), for `0 < j < d`. -/
def product : Prog isa :=
  .seq (loadRow (rowWord jOff 2) 5) <| .seq (mul .wide 8 5 7) <|
  .seq (storeRow ([.mov .eax (.mem (sc jOff)), .alu .add .eax (.mem (sc dOff)), .alu .add .eax (.imm 2)]) 8)
    (.block [.mov .eax (.mem (sc jOff)), .alu .add .eax (.imm 1), .store (sc jOff) .eax,
      .alu .cmp .eax (.mem (sc dOff))])

/-- The tooth `d := 2 d`: its entry, and the entries it adds to the ones below it. -/
def column : Prog isa :=
  .seq squares <|
  .seq (.block [.mov .eax (.mem (sc dOff)), .alu .add .eax (.reg .eax), .store (sc dOff) .eax]) <|
  .seq (storeRow (rowWord dOff 2) 7) <|
  .seq (.block [.mov .eax (.imm 1), .store (sc jOff) .eax]) <|
  .seq (.loop product .ne) (.block [.mov .eax (.mem (sc dOff)), .alu .cmp .eax (.imm 16)])

def table : Prog isa :=
  .seq (seqs initial) (.seq (.block [.mov .eax (.imm 1), .store (sc dOff) .eax]) (.loop column .ne))

/-- The width (the recognized width capped by the bound's bit length) and the metadata, p's
context, `p` and `R² mod p`, and the table; 1. -/
def body : Prog isa :=
  .seq recognize <| .seq GenerateKey.scan <| .seq maskBits <| .seq (.block boundBits) <| .seq cap <|
  .seq (.block metadata) <| .seq pSetup <| .seq (load (sl 10) n1 4 5) <| .seq ctxP <|
  .seq (storeRow (rowImm 0) 9) <| .seq (storeRow (rowImm 1) 4) <| .seq table (ret 1)

def code : Prog isa := wrap args body

end Precompute

namespace Generate

/-- `vg_ffdh_generate_key`'s arguments, then `(ctx, ctx_len)`. -/
def args : Args := { GenerateKey.args with ctx := some 11 }

/-- The cut at the context's public width: `ld := p_len − bytes`, and the mask
`t := 2^(width − 8 (bytes − 1)) − 1` of the first byte kept. -/
def metaCut : Prog isa :=
  .seq (.block [.mov .ecx (.mem (argAt 0 ctxArg)), .mov .eax (.mem (at_ .ecx 8)), .mov .edx (.mem (argAt 0 3)),
      .alu .sub .edx (.reg .eax), .store (sc ldOff) .edx, .alu .add .eax (.reg .eax),
      .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .mov .edx (.mem (at_ .ecx 0)),
      .alu .sub .edx (.reg .eax), .alu .add .edx (.imm 8), .mov .eax (.imm 1)])
    (.seq (.loop (.block [.alu .add .eax (.reg .eax), .alu .sub .edx (.imm 1)]) .ne)
      (.block [.alu .sub .eax (.imm 1), .store (sc tOff) .eax]))

/-- `eax :=` bit `esi` (public) of x (slot 13): 0 past the slot's words. -/
def bit : Prog isa :=
  .seq (.block ([.mov .ecx (.reg .esi), .shift .shr .ecx 5, .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx)] ++
      widthC 0 .wide .edx ++ [.alu .cmp .ecx (.reg .edx)]))
    (.ite .b
      (.seq (.block (ptrTo (sl 13) .ebp .edx ++ [.alu .add .ebp (.reg .ecx), .mov .eax (.mem (at_ .ebp 0)),
          .mov .ecx (.reg .esi), .alu .and .ecx (.imm 31)]))
        (seqs ([16, 8, 4, 2, 1].map fun b => .seq (.block [.alu .test .ecx (.imm (BitVec.ofNat 32 b))])
          (.ite .ne (.block [.shift .shr .eax b]) (.block [])))))
      (.block [.mov .eax (.imm 0)]))

/-- Bit `row + j rows` of x into bit `j` of the digit, the window word. -/
def tooth (j : Nat) : Prog isa :=
  .seq (.block ([.mov .esi (.mem (sc iOff)), .alu .sub .esi (.imm 1)] ++
      List.replicate j (.alu .add .esi (.mem (sc rowsOff)))))
    (.seq bit (.block ([.alu .and .eax (.imm 1)] ++ List.replicate j (.alu .add .eax (.reg .eax)) ++
      [.alu .or .eax (.mem (sc winOff)), .store (sc winOff) .eax])))

/-- The digit of row `iOff − 1` to the window word. -/
def digit : Prog isa :=
  .seq (.block [.mov .eax (.imm 0), .store (sc winOff) .eax]) (seqs ((List.range 5).map tooth))

/-- Entry `e` (at `ebp`) into slot 7 if it is the digit's; `ebp` past it. -/
def selectStep (e : Nat) : Prog isa :=
  .seq (.block (VG.Impl.Mont.X86.Dynamic.windowMask e ++ ptrTo (sl 7) .ebx .edx ++ cntTo n1 .edi))
    (.seq selectLoop (.block restoreEdi))

/-- Slot 7 the digit's entry, reading every entry. -/
def select : Prog isa :=
  .seq (zero (sl 7) n1) (.seq (.block (rowImm 2 ++ rowAt .ebp)) (seqs ((List.range 32).map selectStep)))

/-- One row: the square, the digit's entry and the product; the row counted down. -/
def step : Prog isa :=
  .seq (square .wide) <| .seq digit <| .seq select <| .seq (mul .wide 6 6 7)
    (.block [.mov .eax (.mem (sc iOff)), .alu .sub .eax (.imm 1), .store (sc iOff) .eax])

/-- Slot 6 `g^x mod p` by the context's comb over its rows: Montgomery one, the rows from the
top, and the product with one. -/
def comb : Prog isa :=
  .seq ctxP <| .seq (mul .wide 6 4 3) <|
  .seq (.block [.mov .ecx (.mem (argAt 0 ctxArg)), .mov .eax (.mem (at_ .ecx 16)), .store (sc rowsOff) .eax,
    .store (sc iOff) .eax]) <|
  .seq (.loop step .ne) (mul .wide 6 6 3)

/-- `GenerateKey.tail` with the comb. -/
def tail : Prog isa :=
  .seq comb <| .seq (copy (sl 6) (sl 12) n1) <| .seq (rangeMask 12) <|
  .seq (.block [.store (sc accOff) .ecx]) <|
  .seq (.block qTest) <|
  .seq (.ite .e (.block []) (.seq (powP 12 16) (.seq (equal (sl 6) (sl 3) n1)
    (.block [.alu .and .ecx (.mem (sc accOff)), .store (sc accOff) .ecx])))) <|
  .seq GenerateKey.outputs
    (.block [.alu .add .eax (.reg .eax), .mov .ecx (.imm 3), .alu .sub .ecx (.reg .eax), .mov .eax (.reg .ecx)])

/-- `GenerateKey.main` with the cut at the context's width and the comb. -/
def main : Prog isa :=
  .seq pSetup <| .seq (load (sl 10) n1 4 5) <| .seq metaCut <| .seq GenerateKey.cut <|
  .seq (load (sl 13) n1 0 1) <| .seq CheckPrivate.bound <| .seq CheckPrivate.scalarMask <|
  .seq testMask (.ite .e GenerateKey.fail tail)

def body : Prog isa :=
  .seq (.block PublicFn.modulusArgs) (.seq (.block modulusCheck) (.ite .e main (ret 0)))

def code : Prog isa := wrap args body

end Generate

namespace Search
open KeySearch

/-- The context's two words of the state. -/
def ctxOff : Nat := 80
def ctxLenOff : Nat := 84

/-- `KeySearch.entry`, and the context's arguments kept. -/
def entry : List Instr := KeySearch.entry ++ keep 13 ctxOff ++ keep 14 ctxLenOff

/-- The attempt's arguments, then the context's. -/
def arguments : List Instr := KeySearch.arguments ++ pass ctxOff 11 ++ pass ctxLenOff 12

def argsBytes : Nat := 52

def attempt : Prog isa :=
  .frame (.alloc argsBytes) (.seq (.block arguments) (.call Spec.Ffdh.cachedGenerateKeyApi.name Generate.code))
    (.free argsBytes)

def attemptOrRequest : Prog isa := .seq (.block room) (.ite .b request (.seq attempt classify))

def branch : Prog isa :=
  .seq (.block [.mov .eax (.mem (st keysOff)), .alu .test .eax (.reg .eax)])
    (.ite .e exhausted (.seq (.block [.mov .eax (.mem (st scalarsOff)), .alu .test .eax (.reg .eax)])
      (.ite .e exhausted attemptOrRequest)))

def iteration : Prog isa :=
  .seq branch (.block [.mov .eax (.mem (st statusOff)), .alu .cmp .eax (.imm 4)])

def code : Prog isa := .seq (.block entry) (.seq (.loop iteration .e) (.block finish))

end Search

end VG.Impl.Ffdh.X86.Cached
