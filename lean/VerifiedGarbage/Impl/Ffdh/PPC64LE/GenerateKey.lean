module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Derive

/-!
# Finite-field Diffie–Hellman on PPC64LE: one key-generation attempt

`vg_ffdh_generate_key` (`Spec/Ffdh/Contract.lean`), in the working space of
`Domain.lean` at `scratch`, with x's address and length, `y`'s address and
`rand`'s address in the header's words 8–11:

* p is loaded into array 0 and checked as `vg_ffdh_derive_public` checks it;
  otherwise the result is 0;
* the bound's octets (q's at `domain + 2 p_len`, or p's without q, whose
  first nonzero octet is `p − 1`'s) are scanned without a branch for the
  first nonzero one and its index (`scan`), its bits below the highest set
  (`smear`), and `rand`'s `p_len` octets are cut there into `x`: zeros
  before it, and'ed with the smeared octet at it, kept after it (`cut`), so
  that x is `scalarOfOctets` of `rand`;
* then as `vg_ffdh_derive_public` (`Derive.dpBody`): the status 2 and zeros
  at `y` for x out of range, else `y = g^x mod p` or zeros and the status 1
  or 3;
* x's octets masked by the status being 1 (`maskX`): zeros but for 1.

The code branches on p's validity, whether there is q and x's range, which
the domain and the status reveal; the scan, the cut and the mask run over
every octet without a branch.
-/

@[expose] public section

namespace VG.Impl.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain

/-- `vg_ffdh_generate_key(x, x_len, y, y_len, domain, domain_len, p_len,
rand, rand_len, scratch, scratch_len)`, the last three on the stack: the
scratch buffer into `r11`, the registers saved there; x, `x_len`, `y` and
`rand` into its header's words 8–11; then `setup` for the domain (`r7`),
`domain_len` (`r8`) and `p_len` (`r9`). -/
def gkFront : List Instr :=
  [.addSp .r11 104, .load .d .r11 .r11 0] ++ save .r11 ++
    [.store .d .r3 .r23 64, .store .d .r4 .r23 72, .store .d .r5 .r23 80, .store .d .r10 .r23 88,
      .addi .r3 .r7 0, .addi .r4 .r8 0, .addi .r5 .r9 0] ++ setup

/-- `r12 :=` the bound's octets: q's (`domain + 2 p_len`), or p's without q. -/
def boundPtr : Prog isa :=
  .seq (.block hasQ) (.ite (.zero .d .r0) (.block [.lsl .r12 .r28 1, .add .r12 .r12 .r21])
    (.block [.addi .r12 .r21 0]))

/-- The scan's start: `p_len` octets (`r6`) from index 0 (`r4`); the index
`p_len − 1` (`r9`), the octet 0 (`r14`) and nothing found (`r15`). -/
def scanSetup : List Instr :=
  [.addi .r6 .r28 0, .li .r4 0, .subi .r9 .r28 1, .li .r14 0, .li .r15 0]

/-- One octet `b` of the scan: if it is the first nonzero one (`r17`, all
ones, else 0), its index and itself are kept. -/
def scanBody : List Instr :=
  [.lbz .r16 .r12 0, .li .r0 0, .sub .r17 .r0 .r16, .logic .or .r17 .r17 .r16, .lsr .d .r17 .r17 63,
    .sub .r17 .r0 .r17, .logic .or .r17 .r17 .r15, .logic .xor .r17 .r17 .r15,
    .logic .xor .r18 .r9 .r4, .logic .and .r18 .r18 .r17, .logic .xor .r9 .r9 .r18,
    .logic .xor .r18 .r14 .r16, .logic .and .r18 .r18 .r17, .logic .xor .r14 .r14 .r18,
    .logic .or .r15 .r15 .r17, .addi .r12 .r12 1, .addi .r4 .r4 1]

/-- The bits of the octet `r14` below its highest set one, that one too. -/
def smear : List Instr :=
  [.lsr .d .r16 .r14 1, .logic .or .r14 .r14 .r16, .lsr .d .r16 .r14 2, .logic .or .r14 .r14 .r16,
    .lsr .d .r16 .r14 4, .logic .or .r14 .r14 .r16]

/-- The cut's start: `rand` (`r24`) and x (`r25`) from the header, `p_len`
octets (`r6`) from index 0 (`r4`). -/
def cutSetup : List Instr :=
  [.load .d .r24 .r23 88, .load .d .r25 .r23 64, .addi .r6 .r28 0, .li .r4 0]

/-- One octet of `rand` to x: and'ed with 0 before the index `r9`, with the
smeared octet `r14` at it, and with 255 after it. -/
def cutBody : List Instr :=
  [.lbz .r16 .r24 0, .li .r0 0, .sub .r17 .r4 .r9, .lsr .d .r17 .r17 63, .sub .r17 .r0 .r17,
    .logic .xor .r18 .r4 .r9, .subi .r18 .r18 1, .lsr .d .r18 .r18 63, .sub .r18 .r0 .r18,
    .li .r19 255, .logic .xor .r20 .r19 .r14, .logic .and .r20 .r20 .r18, .logic .xor .r20 .r20 .r19,
    .logic .or .r20 .r20 .r17, .logic .xor .r20 .r20 .r17, .logic .and .r16 .r16 .r20, .stb .r16 .r25 0,
    .addi .r24 .r24 1, .addi .r25 .r25 1, .addi .r4 .r4 1]

/-- x := `rand`'s `p_len` octets cut to the bound's bit length. -/
def scalar : Prog isa :=
  .seq boundPtr (.seq (.block scanSetup) (.seq (countLoop .r6 scanBody)
    (.seq (.block (smear ++ cutSetup)) (countLoop .r6 cutBody))))

/-- `r17 :=` all ones if the status `r3` is 1, else 0, without a branch. -/
def statusMask : List Instr :=
  [.subi .r12 .r3 1, .li .r0 0, .sub .r17 .r0 .r12, .logic .or .r17 .r17 .r12, .lsr .d .r17 .r17 63,
    .subi .r17 .r17 1]

/-- x's `p_len` octets and'ed with the mask of the status 1: kept for 1,
zeros otherwise. -/
def maskX : Prog isa :=
  .seq (.block (statusMask ++ [.load .d .r25 .r23 64, .addi .r6 .r28 0]))
    (countLoop .r6 [.lbz .r16 .r25 0, .logic .and .r16 .r16 .r17, .stb .r16 .r25 0, .addi .r25 .r25 1])

/-- After p's check: x, then `vg_ffdh_derive_public`'s body, then zeros at
x but for the status 1. -/
def gkBody : Prog isa := .seq scalar (.seq Derive.dpBody maskX)

/-- `vg_ffdh_generate_key`. -/
def generateKey : Prog isa :=
  .seq (.block gkFront) (.seq loadP
    (.seq (.ite (.zero .d .r0) gkBody (.block [.li .r3 0])) (.block Domain.restore)))

end VG.Impl.Ffdh.PPC64LE.GenerateKey
