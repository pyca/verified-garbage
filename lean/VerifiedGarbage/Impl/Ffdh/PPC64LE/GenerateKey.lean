module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Derive

/-!
# Finite-field Diffie–Hellman on PPC64LE: a key-generation attempt's pieces

The pieces of `vg_ffdh_generate_key`'s attempt (`Spec/Ffdh/Contract.lean`)
that its cached form (`Cached.lean`) shares, in the working space of
`Domain.lean` at `scratch`, with x's address and length, `y`'s address and
`rand`'s address in the header's words 8–11:

* the bound's octets (q's at `domain + 2 p_len`, or p's without q, whose
  first nonzero octet is `p − 1`'s, `boundPtr`) are scanned without a branch
  for the first nonzero one and its index (`scanSetup`, `scanBody`);
* `rand`'s `p_len` octets are cut into `x`: zeros before an index, and'ed
  with a mask at it, kept after it (`ptrs`, `cutSetup`, `cutBody`);
* x's octets masked by the status being 1 (`statusMask`, `maskX`): zeros
  but for 1.

The scan, the cut and the mask run over every octet without a branch.
-/

@[expose] public section

namespace VG.Impl.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain

/-- `r12 :=` the bound's octets: q's (`domain + 2 p_len`), or p's without q. -/
def boundPtr : Prog isa :=
  .seq (.block hasQ) (.ite (.zero .d .r0) (.block [.lsl .r12 .r28 1, .add .r12 .r12 .r21])
    (.block [.addi .r12 .r21 0]))

/-- The scan's start: `p_len` octets (`r6`) from index 0 (`r4`); the index
`p_len − 1` (`r22`), the octet 0 (`r14`) and nothing found (`r15`). -/
def scanSetup : List Instr :=
  [.addi .r6 .r28 0, .li .r4 0, .subi .r22 .r28 1, .li .r14 0, .li .r15 0]

/-- One octet `b` of the scan: if it is the first nonzero one (`r17`, all
ones, else 0), its index and itself are kept. -/
def scanBody : List Instr :=
  [.lbz .r16 .r12 0, .li .r0 0, .sub .r17 .r0 .r16, .logic .or .r17 .r17 .r16, .lsr .d .r17 .r17 63,
    .sub .r17 .r0 .r17, .logic .or .r17 .r17 .r15, .logic .xor .r17 .r17 .r15,
    .logic .xor .r18 .r22 .r4, .logic .and .r18 .r18 .r17, .logic .xor .r22 .r22 .r18,
    .logic .xor .r18 .r14 .r16, .logic .and .r18 .r18 .r17, .logic .xor .r14 .r14 .r18,
    .logic .or .r15 .r15 .r17, .addi .r12 .r12 1, .addi .r4 .r4 1]

/-- `rand` (`r24`) and x (`r25`) from the header. -/
def ptrs : List Instr := [.load .d .r24 .r23 88, .load .d .r25 .r23 64]

/-- The cut's start: `p_len` octets (`r6`) from index 0 (`r4`). -/
def cutSetup : List Instr := [.addi .r6 .r28 0, .li .r4 0]

/-- One octet of `rand` to x: and'ed with 0 before the index `r22`, with the
smeared octet `r14` at it, and with 255 after it. -/
def cutBody : List Instr :=
  [.lbz .r16 .r24 0, .li .r0 0, .sub .r17 .r4 .r22, .lsr .d .r17 .r17 63, .sub .r17 .r0 .r17,
    .logic .xor .r18 .r4 .r22, .subi .r18 .r18 1, .lsr .d .r18 .r18 63, .sub .r18 .r0 .r18,
    .li .r19 255, .logic .xor .r20 .r19 .r14, .logic .and .r20 .r20 .r18, .logic .xor .r20 .r20 .r19,
    .logic .or .r20 .r20 .r17, .logic .xor .r20 .r20 .r17, .logic .and .r16 .r16 .r20, .stb .r16 .r25 0,
    .addi .r24 .r24 1, .addi .r25 .r25 1, .addi .r4 .r4 1]

/-- `r17 :=` all ones if the status `r3` is 1, else 0, without a branch. -/
def statusMask : List Instr :=
  [.subi .r12 .r3 1, .li .r0 0, .sub .r17 .r0 .r12, .logic .or .r17 .r17 .r12, .lsr .d .r17 .r17 63,
    .subi .r17 .r17 1]

/-- x's `p_len` octets and'ed with the mask of the status 1: kept for 1,
zeros otherwise. -/
def maskX : Prog isa :=
  .seq (.block (statusMask ++ [.load .d .r25 .r23 64, .addi .r6 .r28 0]))
    (countLoop .r6 [.lbz .r16 .r25 0, .logic .and .r16 .r16 .r17, .stb .r16 .r25 0, .addi .r25 .r25 1])

end VG.Impl.Ffdh.PPC64LE.GenerateKey
