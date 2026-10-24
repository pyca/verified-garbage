module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Common
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Top
public import VerifiedGarbage.Impl.MdStream.PPC64LE

/-!
# DSA parameter generation on PPC64LE

`vg_dsa_generate_parameters(out, out_len, p_len, q_len, seeds, seeds_len, hs,
hs_len, witnesses, witnesses_len, scratch, scratch_len)`: the first eight in
`r3`–`r10`, the others on the stack, at `sp + 96 + 8 i` for the `i`-th of
them (`witnesses` is the 0th). No argument is a `u32`. As on ARMv7
(`Impl/Dsa/Arm/Generation.lean`), for each seed of the `seeds` tape (FIPS
186-4 A.1.1.2):

1. q: the seed's hash (SHA-1 for a 160-bit q, else SHA-256: one block, by
   the compression function), its top and low bits set, tested by
   `vg_dsa_probable_prime_{N}` with witnesses from the front of what is left
   of `witnesses`.
2. p: for each of the `4 L` counters, the hashes of `seed + offset + j`
   (big-endian, `seedlen` bytes) for `j ≤ count`, assembled into `X` with its
   top bit set; `p = X − (X mod 2q) + 1`, by division of `X` by `q` in the
   RSA key working space (`Impl/Rsa/PPC64LE/KeyWs.lean`: the quotient's
   parity gives `X mod 2q`, and the quotient with its low bit cleared is
   `(p − 1) / q`); if `p` has `L` bits, tested by
   `vg_dsa_probable_prime_{L}`.
3. g: for each `h` of the `hs` tape with `1 < h < p − 1` (in the key working
   space), `g = h^((p−1)/q) mod p` by the fixed-window power of the RSA code
   (`ModExp.powSecret`, in a working space of the DSA functions' P space
   layout, `Impl/Dsa/PPC64LE/Common.lean`), until `1 < g` (`elemRange`).
4. p||q||g checked by `vg_dsa_check_parameters`.

The first domain that passes is copied to `out`, with status 1; otherwise
`out` is zeroed, with status 0: no seed left, or `witnesses` ran out.

`scratch` (`S`) holds, from byte 0, the search's state (`f…`), our
caller's `r2`, `r14`–`r31` and our return address, then small buffers (`s…`),
then the P space (at `pB`), the key working space (at `kB pLen`) and the
working space of the functions we call (at `wB pLen`). `S` stays in `r28`,
which no code here or that we call writes: every value of the search is
loaded from and stored to `S`'s header, so that it survives the calls and
the arithmetic, which use every other register.
-/

@[expose] public section
namespace VG.Impl.Dsa.PPC64LE.Generation
open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Keys

/-! ## The state -/

def fOut : Nat := 0
def fSeed : Nat := 8
def fSeedLeft : Nat := 16
def fUsed : Nat := 24
def fCounter : Nat := 32
def fOffset : Nat := 40
def fH : Nat := 48
def fHLeft : Nat := 56
def fStatus : Nat := 64
def fWit : Nat := 72
def fWitLen : Nat := 80
/-- A test's result, the p search's and the generator search's state. -/
def fRes : Nat := 88
def fP : Nat := 96
def fG : Nat := 104
/-- The octets a test read, a 64-bit word. -/
def fUsedOut : Nat := 112
def fLR : Nat := 120
def fHs : Nat := 128
def fHsLen : Nat := 136
/-- Our caller's `r2` and `r14`–`r31`. -/
def fSave : Nat := 144

/-- The nonvolatile registers saved, `r28` (which keeps `S`) last. -/
def saved : List Reg :=
  [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r29, .r30,
    .r31, .r28]

/-- `r :=` the state word at `o`. -/
def ld (r : Reg) (o : Nat) : Instr := .load .d r .r28 o

/-- The state word at `o` := `r`. -/
def st (r : Reg) (o : Nat) : Instr := .store .d r .r28 o

/-- The state word at `o` := `v`. -/
def stImm (o v : Nat) : List Instr := [.li .r3 v, st .r3 o]

/-- `r0 := ` the state word at `o` minus `v`, for a test against zero (through
`r3`: `subi` reads `r0` as 0). -/
def cmpF (o v : Nat) : List Instr := [ld .r3 o, .subi .r0 .r3 v]

/-! ## The scratch -/

def sMsg : Nat := 512
def sState : Nat := 576
def sQ : Nat := 608
def sX : Nat := 672
def sPBE : Nat := 1056
def sE : Nat := 1440
def sG : Nat := 1824
def sPacked : Nat := 2208

/-- The P space. -/
def pB : Nat := 3072

/-- The key working space: after the P space's header and its 28 arrays of
`p_len / 8 + 2` words. -/
def kB (pLen : Nat) : Nat := pB + 256 + 28 * (pLen + 16)

/-- The key working space's arrays. -/
def aQt : Nat := 0
def aRm : Nat := 1
def aDv : Nat := 2
def aDt : Nat := 3
def aX : Nat := 4
def aT : Nat := 5
def aS : Nat := 6
def aPm1 : Nat := 7
def aP : Nat := 8
def aE : Nat := 9
def aH : Nat := 10
def aOne : Nat := 11
def aZero : Nat := 13
def aTmp : Nat := 14
def nArrs : Nat := 15

/-- The key working space's slots (past those of its shared routines). -/
def slOdd : Nat := 136
def slLo : Nat := 140
def slHi : Nat := 144

/-- The working space of the functions we call, 64-byte aligned. -/
def wB (pLen : Nat) : Nat := (kB pLen + hdr + nArrs * (pLen + 8) + 63) / 64 * 64

/-- Its 64-bit words: the rest of `scratch`. -/
def wWords (pLen : Nat) : Nat := 64 * pLen + 1024 - wB pLen / 8

/-- `rd := S + o`. -/
def scr (rd : Reg) (o : Nat) : Instr := .addi rd .r28 o

/-! ## Bytes -/

/-- `n > 0` bytes copied: `src` sets `r3` to the source, then `dst` sets `r4`
to the destination. -/
def copyN (src dst : List Instr) (n : Nat) : Prog isa :=
  .seq (.block (src ++ dst ++ [.li .r5 n]))
    (.loop (.block VG.Impl.MlKem.PPC64LE.copyBody) (.nonzero .d .r5))

/-- From `S + src` to `S + dst`. -/
def copyS (dst src n : Nat) : Prog isa := copyN [scr .r3 src] [scr .r4 dst] n

/-- A byte of the big-endian addition: `[r3] + r4`, its carry and the
addend's higher bytes on in `r4`. -/
def addStep : List Instr :=
  [.lbz .r5 .r3 0, .add .r5 .r5 .r4, .stb .r5 .r3 0, .lsr .d .r4 .r5 8, .subi .r3 .r3 1,
    .subi .r6 .r6 1]

/-- `offset + j` (the state word `fOffset` plus `j`) added to the `n`-byte
seed at `sMsg`, modulo `2^(8 n)`. -/
def seedAdd (n j : Nat) : Prog isa :=
  .seq (.block [scr .r3 (sMsg + n - 1), ld .r4 fOffset, .addi .r4 .r4 j, .li .r6 n])
    (.loop (.block addStep) (.nonzero .d .r6))

/-- `n > 0` bytes from `r3` zeroed. -/
def zeroN : Prog isa :=
  .seq (.block [.li .r0 0]) (.loop (.block [.stb .r0 .r3 0, .addi .r3 .r3 1, .subi .r5 .r5 1]) (.nonzero .d .r5))

/-! ## Hashes -/

/-- A hash function by its compression function. -/
structure Hash where
  /-- The words of the hash value. -/
  k : Nat
  iv : List (BitVec 32)
  name : String
  code : Prog isa

/-- `r ← v`, for `v < 2³²`: `lis` of the high half and `ori` of the low one. -/
def loadImm (r : Reg) (v : Nat) : List Instr :=
  [.lis r (BitVec.ofNat 16 (v / 65536)), .ori r r (BitVec.ofNat 16 (v % 65536))]

/-- The initial hash value at `sState`. -/
def ivStore (iv : List (BitVec 32)) : List Instr :=
  iv.zipIdx.flatMap fun (v, i) => loadImm .r0 v.toNat ++ [.store .w .r0 .r28 (sState + 4 * i)]

/-- The block at `sMsg` hashed into `S + dst`: the initial hash value at
`sState`, the block compressed into it (`MdStream.PPC64LE.compressAt`, with
the hash value in `r26` and the working space of the compression function,
at `wB`, in `r27`), and its words big-endian at `dst`
(`MdStream.PPC64LE.out32`, to `r28`, which is moved to `dst` and back). -/
def hash (pLen : Nat) (G : Hash) (dst : Nat) : Prog isa := seqs [
  .block (ivStore G.iv ++ [scr .r26 sState, scr .r27 (wB pLen), scr .r4 sMsg]),
  VG.Impl.MdStream.PPC64LE.compressAt G.name G.code,
  .block ([.addi .r28 .r28 dst] ++ VG.Impl.MdStream.PPC64LE.out32 G.k true ++ [.subi .r28 .r28 dst])]

/-- The block's padding after a message of `n < 56` bytes. -/
def padInit (n : Nat) : List Instr :=
  [.li .r0 0] ++ (List.range 8).map (fun i => st .r0 (sMsg + 8 * i)) ++
    [.li .r0 0x80, .stb .r0 .r28 (sMsg + n), .li .r0 ((8 * n) / 256), .stb .r0 .r28 (sMsg + 62),
      .li .r0 ((8 * n) % 256), .stb .r0 .r28 (sMsg + 63)]

/-! ## Tests -/

/-- A probable-prime test of the candidate at byte `c` of the working space
`wB`, copied there from `S + src` (`n` bytes), with the witnesses left (from
`witnesses` itself when none is: an empty range within the tape): its
result, zero-extended, into `fRes`, and the octets it read added to `fUsed`
unless it ran out. -/
def test (pLen c src n : Nat) (name : String) (callee : Prog isa) : Prog isa := seqs [
  copyS (wB pLen + c) src n,
  .block [scr .r3 (wB pLen), .li .r4 (wWords pLen), ld .r9 fUsed, ld .r5 fWit, ld .r6 fWitLen,
    .add .r5 .r5 .r9, .sub .r6 .r6 .r9, scr .r7 fUsedOut],
  .ite (.zero .d .r6) (.block [ld .r5 fWit]) (.block []),
  .call name callee,
  .block [.lsr .w .r3 .r3 0, st .r3 fRes],
  .ite (.zero .d .r3) (.block [])
    (.block [ld .r4 fUsedOut, ld .r5 fUsed, .add .r5 .r5 .r4, st .r5 fUsed])]

/-! ## Arithmetic, in the key working space -/

/-- `r31`, `r29` and `r30`: the key working space, its digits and its stride. -/
def ksRegs (pLen : Nat) : List Instr := [scr .r31 (kB pLen), .li .r29 (pLen / 4)] ++ stride

/-- Every array zeroed, and 1 set. -/
def ksSetup : Prog isa :=
  .seq (.block [.li .r8 nArrs, .mul .r8 .r8 .r30, .lsr .d .r8 .r8 2])
    (.seq (zeroArrays .r8) (.block (setOne aOne)))

/-- Array `j` := the `n` big-endian bytes at `S + o`. -/
def loadS (j o n : Nat) : Prog isa :=
  .seq (.block [scr .r6 o, .li .r8 n]) (VG.Impl.Rsa.PPC64LE.CrtValues.load j)

/-- `S + o` := `[j]`'s low `n` bytes, big-endian. -/
def storeS (j o n : Nat) : Prog isa :=
  .seq (.block [scr .r5 o, .li .r8 n, .li .r9 0, .subi .r9 .r9 1])
    (VG.Impl.Rsa.PPC64LE.CrtValues.storeBytes j)

/-- The slot `d` := `[a] < [b]`. -/
def ltS (d a b : Nat) : List (Prog isa) := [sub3 aTmp a b, .block (stBorrow d)]

/-- The octets of `(p − 1) / q` kept: `8 (p_len − q_len) + 1` bits. -/
def eBytes (pLen qLen : Nat) : Nat := pLen - qLen + 1

/-- `p` and `(p − 1) / q` from `X` at `sX` and `q` at `sQ`: `p − 1` in array
`aPm1`, `p` in array `aP` and to `sPBE` (big-endian), `(p − 1) / q` in
array `aE` and to `sE`. -/
def pArith (pLen qLen : Nat) : Prog isa := seqs [
  seqs [.block (ksRegs pLen), ksSetup, loadS aQt sX pLen, loadS aX sX pLen, loadS aDv sQ qLen],
  VG.Impl.Rsa.PPC64LE.Div.div aQt aRm aDv aDt,
  seqs [sub3 aT aX aRm, .block (bitOf slOdd aQt), sel aS aZero aDv slOdd, sub3 aPm1 aT aS],
  seqs [copy aP aPm1, .block (orOne aP), copy aE aQt, .block (clrLow aE), storeS aP sPBE pLen,
    storeS aE sE (eBytes pLen qLen)]]

/-! ## The power, in the P space -/

/-- Into the P space at `pB`, with `w = p_len / 8`. -/
def enterP (pLen : Nat) : List Instr :=
  [scr .r21 pB, .addi .r23 .r21 0, .addi .r31 .r21 0, .addi .r10 .r21 VG.Impl.Bignum.hdrBytes,
    .li .r11 (pLen / 4), .li .r29 (pLen + 16)]

/-- Array 4's word `w` := 0 (as `elemRange` reads it), and `r10` back to array 0. -/
def zeroTop4 : List Instr :=
  VG.Impl.Bignum.PPC64LE.PublicChecked.base .r10 4 ++
    [.add .r14 .r10 .r29, .subi .r14 .r14 16, .li .r0 0, .store .d .r0 .r14 0,
      .addi .r10 .r31 VG.Impl.Bignum.hdrBytes]

/-- `[4] := h^((p−1)/q) mod p` for `h` at `fH`: p into array 0, `R² mod p`
into array 1, `h` into array 4, then the power over `sE`; `r0 := 0` exactly
when `1 < [4] < p`. -/
def power (pLen qLen : Nat) : Prog isa := seqs [
  .block (enterP pLen ++ [scr .r12 sPBE, .li .r6 pLen]), VG.Impl.Dsa.PPC64LE.loadArr 0,
  .block (VG.Impl.Bignum.PPC64LE.PublicChecked.base .r5 1 ++ VG.Impl.Bignum.PPC64LE.PublicChecked.base .r8 2 ++
    VG.Impl.Bignum.PPC64LE.PublicChecked.base .r9 3),
  VG.Impl.Bignum.PPC64LE.Precompute.r2,
  .block [ld .r12 fH, .li .r6 pLen], VG.Impl.Dsa.PPC64LE.loadArr 4,
  .block (VG.Impl.Bignum.PPC64LE.PublicChecked.minv ++ [scr .r30 sE, .li .r31 (eBytes pLen qLen)]),
  VG.Impl.Bignum.PPC64LE.ModExp.powSecret,
  .block ([.addi .r31 .r23 0] ++ zeroTop4),
  VG.Impl.Dsa.PPC64LE.elemRange]

/-! ## The search -/

/-- The geometry and the functions called. -/
structure Geo where
  pLen : Nat
  qLen : Nat
  G : Hash
  /-- The candidate's byte offset in the working space of the tests. -/
  qCand : Nat
  qName : String
  qCode : Prog isa
  pCand : Nat
  pName : String
  pCode : Prog isa
  checkName : String
  checkCode : Prog isa

namespace Geo
variable (g : Geo)

/-- `(L − 1) / N`. -/
def count : Nat := (8 * g.pLen - 1) / (8 * g.qLen)

/-- q from the seed: hashed, shaped, and tested. -/
def qPart : Prog isa := seqs [
  copyN [ld .r3 fSeed] [scr .r4 sMsg] g.qLen,
  hash g.pLen g.G sQ,
  .block [.lbz .r0 .r28 sQ, .ori .r0 .r0 0x80, .stb .r0 .r28 sQ,
    .lbz .r0 .r28 (sQ + g.qLen - 1), .ori .r0 .r0 1, .stb .r0 .r28 (sQ + g.qLen - 1)],
  test g.pLen g.qCand sQ g.qLen g.qName g.qCode]

/-- The hash of `seed + offset + j`, into its place in `X`. -/
def pHash (j : Nat) : Prog isa := seqs [
  copyN [ld .r3 fSeed] [scr .r4 sMsg] g.qLen,
  seedAdd g.qLen j,
  hash g.pLen g.G (sX + g.pLen - (j + 1) * g.qLen)]

/-- The first `m` hashes of `X`. -/
def pHashes : Nat → Prog isa
  | 0 => .block []
  | m + 1 => .seq (pHashes m) (g.pHash m)

/-- `X`: the hashes, the top bit set. -/
def pX : Prog isa :=
  .seq (g.pHashes (g.count + 1)) (.block [.lbz .r0 .r28 sX, .ori .r0 .r0 0x80, .stb .r0 .r28 sX])

/-- A counter's candidate: `fP` := 0 if the witnesses ran out, 1 if it is a
probable prime, else as it was. -/
def pAttempt : Prog isa := seqs [
  g.pX, pArith g.pLen g.qLen,
  .block [.lbz .r0 .r28 sPBE, .lsr .d .r0 .r0 7],
  .ite (.zero .d .r0) (.block [])
    (seqs [test g.pLen g.pCand sPBE g.pLen g.pName g.pCode,
      .block (cmpF fRes 0), .ite (.zero .d .r0) (.block (stImm fP 0))
        (seqs [.block (cmpF fRes 1), .ite (.zero .d .r0) (.block (stImm fP 1)) (.block [])])])]

/-- The next counter: `r0 = 0` when the `4 L` are done. -/
def pAdvance : List Instr :=
  [ld .r3 fCounter, .addi .r3 .r3 1, st .r3 fCounter, ld .r4 fOffset, .addi .r4 .r4 (g.count + 1),
    st .r4 fOffset, .subi .r0 .r3 (32 * g.pLen)]

/-- p: `fP` := 0, 1 or 2 (none found). -/
def pPart : Prog isa := seqs [
  .block (stImm fCounter 0 ++ stImm fOffset 1 ++ stImm fP 4),
  .loop (seqs [g.pAttempt, .block (cmpF fP 4),
    .ite (.zero .d .r0) (.seq (.block g.pAdvance) (.ite (.zero .d .r0) (.block (stImm fP 2)) (.block [])))
      (.block []),
    .block (cmpF fP 4)]) (.zero .d .r0)]

/-- An `h`: `fG` := 1 with `g` at `sG` if `1 < h < p − 1` and `1 < g`. -/
def gStep : Prog isa := seqs [
  .block (ksRegs g.pLen ++ [ld .r6 fH, .li .r8 g.pLen]),
  VG.Impl.Rsa.PPC64LE.CrtValues.load aH,
  seqs (ltS slLo aOne aH), seqs (ltS slHi aH aPm1),
  .block (andS slLo slLo slHi ++ [.load .w .r0 .r31 slLo]),
  .ite (.zero .d .r0) (.block [])
    (seqs [power g.pLen g.qLen,
      .ite (.zero .d .r0)
        (seqs [.block [scr .r12 sG, .li .r6 g.pLen], VG.Impl.Dsa.PPC64LE.storeBE 4, .block (stImm fG 1)])
        (.block [])])]

/-- g: `fG` := 1, or 2 if no `h` gives one. -/
def gPart : Prog isa := seqs [
  .block [ld .r3 fHs, st .r3 fH, ld .r3 fHsLen, st .r3 fHLeft], .block (stImm fG 4),
  .loop (seqs [.block (cmpF fHLeft 0),
    .ite (.zero .d .r0) (.block (stImm fG 2))
      (seqs [g.gStep, .block [ld .r3 fH, .addi .r3 .r3 g.pLen, st .r3 fH, ld .r3 fHLeft,
        .subi .r3 .r3 g.pLen, st .r3 fHLeft]]),
    .block (cmpF fG 4)]) (.zero .d .r0)]

/-- p||q||g, checked: `fStatus` := 1 if it passes. -/
def checkPart : Prog isa := seqs [
  copyS sPacked sPBE g.pLen, copyS (sPacked + g.pLen) sQ g.qLen,
  copyS (sPacked + g.pLen + g.qLen) sG g.pLen,
  .block [scr .r3 sPacked, .li .r4 (2 * g.pLen + g.qLen), .li .r5 g.pLen, .li .r6 g.qLen,
    scr .r7 (wB g.pLen), .li .r8 (wWords g.pLen)],
  .call g.checkName g.checkCode,
  .block [.lsr .w .r3 .r3 0, .subi .r0 .r3 1],
  .ite (.zero .d .r0) (.block (stImm fStatus 1)) (.block [])]

/-- A seed. -/
def attempt : Prog isa := seqs [
  g.qPart, .block (cmpF fRes 0),
  .ite (.zero .d .r0) (.block (stImm fStatus 2))
    (seqs [.block (cmpF fRes 1),
      .ite (.zero .d .r0)
        (seqs [g.pPart, .block (cmpF fP 0),
          .ite (.zero .d .r0) (.block (stImm fStatus 2))
            (seqs [.block (cmpF fP 1),
              .ite (.zero .d .r0) (seqs [g.gPart, .block (cmpF fG 1), .ite (.zero .d .r0) g.checkPart (.block [])])
                (.block [])])])
        (.block [])])]

/-- The seeds, one at a time, until a domain passes or none is left. -/
def search : Prog isa := seqs [
  .block (padInit g.qLen),
  .loop (seqs [.block (cmpF fSeedLeft 0),
    .ite (.zero .d .r0) (.block (stImm fStatus 2))
      (seqs [g.attempt, .block [ld .r3 fSeed, .addi .r3 .r3 g.qLen, st .r3 fSeed, ld .r3 fSeedLeft,
        .subi .r3 .r3 g.qLen, st .r3 fSeedLeft]]),
    .block (cmpF fStatus 0)]) (.zero .d .r0)]

/-- The result: p||q||g to `out` and 1, or zeros and 0. -/
def finish : Prog isa :=
  .seq (.block (cmpF fStatus 1))
    (.ite (.zero .d .r0)
      (seqs [copyN [scr .r3 sPacked] [ld .r4 fOut] (2 * g.pLen + g.qLen), .block [.li .r3 1]])
      (seqs [.block [ld .r3 fOut, .li .r5 (2 * g.pLen + g.qLen)], zeroN, .block [.li .r3 0]]))

def generate : Prog isa := .seq g.search g.finish

end Geo

/-! ## Entry -/

/-- The words `entry` stores into the header (through `r11`, `scratch`): our
return address, our caller's registers, `out`, the tapes' pointers and
lengths; nothing used, searching. -/
def entryStores : List (Reg × Nat) :=
  [(.r0, fLR)] ++ saved.zipIdx.map (fun (r, i) => (r, fSave + 8 * i)) ++
    [(.r3, fOut), (.r7, fSeed), (.r8, fSeedLeft), (.r9, fHs), (.r10, fHsLen), (.r12, fWit), (.r4, fWitLen),
      (.r6, fUsed), (.r6, fStatus)]

/-- `scratch` into `r11`, the witnesses' pointer and length into `r12` and
`r4`, our return address into `r0` and 0 into `r6`; the header's words
stored, and `scratch` into `r28`. -/
def entry : List Instr :=
  [.addSp .r11 (96 + 8 * 2), .load .d .r11 .r11 0, .addSp .r12 96, .load .d .r12 .r12 0,
    .addSp .r4 (96 + 8), .load .d .r4 .r4 0, .mflr .r0, .li .r6 0] ++
    entryStores.map (fun p => .store .d p.1 .r11 p.2) ++ [.addi .r28 .r11 0]

/-- Our caller's registers but `r28`, and where they are in the header. -/
def restoreLoads : List (Reg × Nat) := (saved.zipIdx.map fun (r, i) => (r, fSave + 8 * i)).take 18

/-- Our return address and our caller's registers back, `r28` last. -/
def restore : List Instr :=
  [ld .r0 fLR, .mtlr .r0] ++ restoreLoads.map (fun p => .load .d p.1 .r28 p.2) ++ [ld .r28 (fSave + 8 * 18)]

/-- The three geometries, by `p_len` (in `r5`). -/
def dispatch (g1 g2 g3 : Geo) : Prog isa :=
  .seq (.block [.subi .r0 .r5 128])
    (.ite (.zero .d .r0) g1.generate
      (.seq (.block [.subi .r0 .r5 256]) (.ite (.zero .d .r0) g2.generate g3.generate)))

def code (g1 g2 g3 : Geo) : Prog isa :=
  .seq (.block entry) (.seq (dispatch g1 g2 g3) (.block restore))

end VG.Impl.Dsa.PPC64LE.Generation
