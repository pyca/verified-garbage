module

public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
public import VerifiedGarbage.Impl.Ffdh.X86_64.VettedValidation

/-!
# FFDH key generation from a reusable public comb context on x86-64

`vg_ffdh_generate_key_precompute` writes `Spec.Ffdh.generationPrecompute`:
the public scalar width of `Spec.Ffdh.generationScalarBits` (the vetted
groups' recognized widths, `VettedValidation.scan`, capped by the bound's
bit length), its byte length and the comb's row count, then `p` and
`R² mod p` as `vg_rsa_public_precompute` writes them, then the 32 entries of
the five-tooth comb in Montgomery form, each `w = ⌈p_len / 8⌉` words.

`vg_ffdh_generate_key_cached` is `vg_ffdh_generate_key`'s attempt with two
stages replaced: the scalar is cut at the context's public width rather than
at the bound's first byte, and `g^x mod p` is the comb's: one square and one
product per row, with the product's entry read by scanning every entry of
the table under an equality mask. The digit is kept in `r13` only, and every
address and count depends on the public width alone.

`vg_ffdh_generate_key_search_cached` is the existing controller around it,
which also passes the context.
-/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.Domain
open Crt (ws stk leave loadArr zeroArr)

/-! ## Header slots

The outer header keeps `Domain`'s slots. The context's pointer is in `sCtx`,
a slot neither the attempt nor the precomputation otherwise uses. The inner
(Montgomery) header keeps `Crt.sLink` and, from `sFn 1`, the comb's public
counters: none of the arithmetic writes the header. -/

def sCtx : Nat := sXe
def sRec : Nat := sY
def sBits : Nat := sXl
def sRows : Nat := Domain.sOut

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

def iCtx : Nat := sFn 1
def iRows : Nat := sFn 2
def iD : Nat := sFn 3
def iJ : Nat := sFn 4
def iI : Nat := sFn 5
def iE : Nat := sFn 6
def iXp : Nat := sFn 7
def iXl : Nat := sFn 8

/-- `rbx := ctx + 24 + 8 w j` for the public index `j` in `rax`, and `r12 := w`:
`p` (`j = 0`), `R² mod p` (1), then entry `a` of the table (`2 + a`). -/
def rowPtr : List Instr :=
  [.mov .r12 (.mem (hdr sW)), .mov .rbx (.reg .rax), .imul .rbx .r12, .shift .shl .rbx 3,
    .alu .add .rbx (.mem (hdr iCtx)), .alu .add .rbx (.imm 24)]

/-- Array `a`'s `w` words to the context's row in `rax`. -/
def storeRow (a : Nat) : Prog isa :=
  .seq (.block (rowPtr ++ [.mov .rsi (.mem (hdr (sArr a)))])) copyWords

/-- The context's row in `rax` to array `a`'s `w` words. -/
def loadRow (a : Nat) : Prog isa :=
  .seq (.block (rowPtr ++ [.mov .rsi (.reg .rbx), .mov .rbx (.mem (hdr (sArr a)))])) copyWords

/-- The outer slot `o` to the inner slot `i`, through the link. -/
def fromOuter (o i : Nat) : List Instr :=
  [.mov .rax (.mem (hdr Crt.sLink)), .mov .rdx (.mem (ws .rax o)), .store (hdr i) .rdx]

namespace Precompute

/-- `(ctx, ctx_len, domain, domain_len, p_len, scratch, scratch_len)`: the
ABI registers and the context saved in the header at `scratch` (`r9`), and
the domain's length and `p_len` where `VettedValidation.scan` reads them. -/
def entry : List Instr := save .r9 ++
  [.store (ws .r9 sCtx) .rdi, .store (at_ .r9 128) .rcx, .store (at_ .r9 136) .r8, .mov .rdi (.reg .rdx)]

/-- The recognized width (0 for any other domain) kept, and `Domain`'s
argument slots laid out over the scan's two. -/
def afterScan : List Instr :=
  [.store (ws .r9 sRec) .rax, .mov .rcx (.mem (at_ .r9 128)), .store (ws .r9 sDom) .rdi,
    .store (ws .r9 sDomLen) .rcx, .store (ws .r9 sK) .r8, .mov .rdi (.reg .r9)]

/-- `rcx :=` the bit length of the bound's first byte (in `rax`, not zero). -/
def byteBits : Prog isa := .seq (.block [.mov32 .rcx (.imm 0)])
  (.loop (.block [.shift .shr .rax 1, .alu .add .rcx (.imm 1), .alu .test .rax (.reg .rax)]) .ne)

/-- `rsi :=` the context, then `rax :=` the bound's bit length, then the
recognized width if it is smaller and not zero. -/
def width : List Instr :=
  [.mov .rsi (.mem (hdr sCtx)), .mov .rax (.mem (hdr sEl)), .shift .shl .rax 3, .alu .sub .rax (.imm 8), .alu .add .rax (.reg .rcx),
    .mov .rdx (.mem (hdr sRec)), .alu .test .rdx (.reg .rdx), .cmov .e .rdx (.reg .rax),
    .alu .cmp .rdx (.reg .rax), .cmov .b .rax (.reg .rdx)]

/-- The three metadata words: the width, its bytes and `⌈width / 5⌉` rows
(`⌊(width + 4) 52429 / 2^18⌋`, exact below `2^18`). -/
def metadata : List Instr :=
  [.store (hdr sBits) .rax, .mov .rcx (.reg .rax), .alu .add .rcx (.imm 7), .shift .shr .rcx 3,
    .mov .rdx (.reg .rax), .alu .add .rdx (.imm 4), .imul3 .rdx .rdx 52429, .shift .shr .rdx 18,
    .store (hdr sRows) .rdx, .store (at_ .rsi 0) .rax, .store (at_ .rsi 8) .rcx, .store (at_ .rsi 16) .rdx]

/-- `p` and `R² mod p` to the context's first two rows. -/
def storePrefix : List (Prog isa) :=
  [.block [.mov32 .rax (.imm 0)], storeRow aN, .block [.mov32 .rax (.imm 1)], storeRow aR2]

variable (mul : Nat → Nat → Nat → Prog isa) (r2 : Prog isa)

/-- Entry 0, Montgomery one, and entry 1, `g R mod p`, which `aY` then keeps. -/
def initial : List (Prog isa) :=
  [mul aY aR2 aOne, .block [.mov32 .rax (.imm 2)], storeRow aY] ++ loadArr aX sG sK ++
  [mul aXm aX aR2, .block [.mov32 .rax (.imm 3)], storeRow aXm, .block [.mov32 .rax (.imm 3)], loadRow aY]

/-- `aY := aY^(2^rows)`, the next tooth's entry from the last. -/
def squares : Prog isa := .seq (.block [.mov .rax (.mem (hdr iRows)), .store (hdr iI) .rax])
  (.loop (.seq (mul aY aY aY)
    (.block [.mov .rax (.mem (hdr iI)), .alu .sub .rax (.imm 1), .store (hdr iI) .rax])) .ne)

/-- Entry `d + j := ` entry `j` times entry `d` (in `aY`), for `0 < j < d`. -/
def product : Prog isa := seqs [
  .block [.mov .rax (.mem (hdr iJ)), .alu .add .rax (.imm 2)], loadRow aX,
  mul aX aX aY,
  .block [.mov .rax (.mem (hdr iJ)), .alu .add .rax (.mem (hdr iD)), .alu .add .rax (.imm 2)], storeRow aX,
  .block [.mov .rax (.mem (hdr iJ)), .alu .add .rax (.imm 1), .store (hdr iJ) .rax,
    .alu .cmp .rax (.mem (hdr iD))]]

/-- The tooth `d = 2^j` and the entries it adds to the ones below it. -/
def column : Prog isa := seqs [squares mul,
  .block [.mov .rax (.mem (hdr iD)), .alu .add .rax (.imm 2)], storeRow aY,
  .block [.mov32 .rax (.imm 1), .store (hdr iJ) .rax],
  .loop (product mul) .ne,
  .block [.mov .rax (.mem (hdr iD)), .alu .add .rax (.reg .rax), .store (hdr iD) .rax,
    .alu .cmp .rax (.imm 32)]]

def table : List (Prog isa) :=
  initial mul ++ [.block [.mov32 .rax (.imm 2), .store (hdr iD) .rax], .loop (column mul) .ne]

/-- With p a valid modulus: the policy's width and the metadata, p's
workspace and `R² mod p`, the prefix and the table. -/
def main : Prog isa := seqs (GenerateKey.bound ++ [byteBits, .block (width ++ metadata), .block head] ++
  pSetup ++ [r2, .block (fromOuter sCtx iCtx ++ fromOuter sRows iRows)] ++ storePrefix ++
  table mul ++ [.block [leave, .mov32 .rax (.imm 1)]])

def body : Prog isa :=
  .seq (.block entry) (.seq (VettedValidation.scan VettedGroups.groups 0)
    (.seq (.block (afterScan ++ domHead)) (.ite .ne (ret 0) (main mul r2))))

def code : Prog isa := .seq (body mul r2) (.block exit)

end Precompute

namespace Generate

open GenerateKey

/-- `vg_ffdh_generate_key`'s entry, and the context (the sixth stack argument). -/
def entry : List Instr := GenerateKey.entry ++
  [.mov .rax (.mem (stk 6)), .store (hdr sCtx) .rax]

/-- The context's public width: `sEl :=` its bytes, `sMsk :=` the mask of
its first byte's bits, `255 >> (8 bytes - width)`. -/
def metaLoad : List Instr :=
  [.mov .rax (.mem (hdr sCtx)), .mov .rsi (.mem (at_ .rax 0)), .mov .rdx (.mem (at_ .rax 8)),
    .store (hdr sEl) .rdx, .shift .shl .rdx 3, .alu .sub .rdx (.reg .rsi), .mov .rcx (.reg .rdx),
    .mov32 .rax (.imm 255), .shiftCl .shr .rax, .store (hdr sMsk) .rax]

/-- The random bytes cut to the context's width, as `vg_ffdh_generate_key`
cuts them to the bound's. -/
def scalar : List (Prog isa) :=
  [.block metaLoad, .block cutSetup, .loop (.block cutBody) .ne, .block cutFinish]

/-- `rdx :=` bit `rax` (public) of x, the `r9` bytes at `rsi`, most
significant first; 0 above them. -/
def bitBody : List Instr :=
  [.mov .r8 (.reg .rax), .shift .shr .r8 3, .mov .r10 (.reg .r9), .alu .sub .r10 (.reg .r8),
    .movzx8 .rdx { base := .rsi, index := some .r10, disp := -1 }, .mov .rcx (.reg .rax),
    .alu .and .rcx (.imm 7), .shiftCl .shr .rdx, .alu .and .rdx (.imm 1)]

def bit : Prog isa :=
  .seq (.block [.mov .rdx (.reg .r9), .shift .shl .rdx 3, .alu .cmp .rax (.reg .rdx)])
    (.ite .b (.block bitBody) (.block [.mov32 .rdx (.imm 0)]))

/-- Bit `row + j rows` of x, at bit `j` of the digit in `r13`. -/
def tooth (j : Nat) : Prog isa :=
  .seq (.block [.mov .rax (.mem (hdr iI)), .alu .sub .rax (.imm 1), .mov .rdx (.mem (hdr iRows)),
      .imul3 .rdx .rdx (BitVec.ofNat 32 j), .alu .add .rax (.reg .rdx)])
    (.seq bit (.block ((if j = 0 then [] else [.shift .shl .rdx j]) ++ [.alu .or .r13 (.reg .rdx)])))

/-- Row `iI - 1`'s digit in `r13`. -/
def digit : Prog isa :=
  .seq (.block [.mov .rsi (.mem (hdr iXp)), .mov .r9 (.mem (hdr iXl)), .mov32 .r13 (.imm 0)])
    (seqs ((List.range 5).map tooth))

/-- Entry `e`'s word, masked, into the selected array's word. -/
def selectWord : List Instr :=
  [.mov .rax (.mem (ix .rsi .r14)), .alu .and .rax (.reg .rdx), .alu .or .rax (.mem (ix .rbx .r14)),
    .store (ix .rbx .r14) .rax]

/-- Entry `iE` under the mask of `iE = r13`. -/
def selectStep : Prog isa := seqs [
  .block [.mov .rax (.mem (hdr iE)), .alu .xor .rax (.reg .r13), .alu .cmp .rax (.imm 1),
    .alu .sbb .rdx (.reg .rdx), .mov .rax (.mem (hdr iE)), .alu .add .rax (.imm 2)],
  .block (rowPtr ++ [.mov .rsi (.reg .rbx), .mov .rbx (.mem (hdr (sArr aXm)))]),
  wordLoop 0 selectWord,
  .block [.mov .rax (.mem (hdr iE)), .alu .add .rax (.imm 1), .store (hdr iE) .rax, .alu .cmp .rax (.imm 32)]]

/-- `aXm :=` the entry of the digit in `r13`, reading every entry. -/
def select : Prog isa := seqs [.block [.mov32 .rax (.imm 0), .store (hdr iE) .rax], .loop selectStep .ne]

variable (mul : Nat → Nat → Nat → Prog isa) (r2 : Prog isa)

/-- One row: the square, the digit's entry and the product. -/
def step : Prog isa := seqs [mul aY aY aY, zeroArr aXm, digit, select, mul aY aY aXm,
  .block [.mov .rax (.mem (hdr iI)), .alu .sub .rax (.imm 1), .store (hdr iI) .rax]]

/-- `aY := g^x mod p`, by the context's comb over its rows. -/
def comb : List (Prog isa) := [
  mul aY aR2 aOne,
  .block (fromOuter sCtx iCtx ++ [.mov .rdx (.mem (at_ .rdx 16)), .store (hdr iRows) .rdx,
    .store (hdr iI) .rdx] ++ fromOuter sX iXp ++ fromOuter sXl iXl),
  .loop (step mul) .ne,
  mul aY aY aOne]

/-- `vg_ffdh_generate_key`'s tail with the comb. -/
def tail : List (Prog isa) := [r2] ++ comb mul ++ publicOutput ++ [maskX, .block status]

def core : List (Prog isa) := [.block head] ++ pSetup ++ loadArr aXm sX sXl ++
  CheckPrivate.scalarRange ++ [.block [.alu .test .rax (.reg .rax)],
    .ite .e (seqs [.block [leave], maskX, ret 2]) (seqs (tail mul r2))]

def main : Prog isa := seqs ([Keys.zeroOut sY sK] ++ scalar ++ core mul r2)

def body : Prog isa := .seq (.block (entry ++ domHead)) (.ite .ne (ret 0) (main mul r2))

def code : Prog isa := .seq (body mul r2) (.block exit)

end Generate

namespace Search

open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

/-- The attempt's arguments, and the context's two (the controller's eighth
and ninth stack arguments) as its sixth and seventh. -/
def cachedArguments : List Instr := KeyGeneration.Search.arguments ++
  [.mov .rax (.mem { base := .rsp, disp := 120 }), .store { base := .rsp, disp := 40 } .rax,
    .mov .rax (.mem { base := .rsp, disp := 128 }), .store { base := .rsp, disp := 48 } .rax]

variable (attempt : Prog isa)

/-- The attempt in a frame of its seven stack arguments. -/
def attemptRun : Prog isa := .frame (.alloc 56) (.seq (.block cachedArguments) attempt) (.free 56)

def attemptOrRequest : Prog isa := .seq
  (.block [.mov .rax (.mem (field 10)), .alu .cmp .rax (.mem (field 2))])
  (.ite .b request (.seq (attemptRun attempt) classify))

def iteration : Prog isa := seqs [
  .block [.mov .rax (.mem (field 0)), .alu .test .rax (.reg .rax)],
  .ite .e exhausted (.seq (.block [.mov .rax (.mem (field 1)), .alu .test .rax (.reg .rax)])
    (.ite .e exhausted (attemptOrRequest attempt))),
  .block [.mov .rax (.mem (field 14)), .alu .cmp .rax (.imm 4)]]

def code : Prog isa :=
  seqs [.block KeyGeneration.Search.entry, .loop (iteration attempt) .e, .block KeyGeneration.Search.finish]

end Search

end VG.Impl.Ffdh.X86_64.Cached
