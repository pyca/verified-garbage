module

public import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
public import VerifiedGarbage.Impl.Rsa.Arm.Div
public import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes
public import VerifiedGarbage.Impl.Sha1.Arm
public import VerifiedGarbage.Impl.Sha256.Arm
public import VerifiedGarbage.Impl.MdStream.Arm
public import VerifiedGarbage.Impl.RsaKeyGen.Arm.SearchInit

/-!
# DSA parameter generation over refillable random tapes on 32-bit ARM (AAPCS)

`vg_dsa_parameter_search(out, out_len, used, rand, rand_len, scratch,
scratch_len, state)` (`Spec/Dsa/ParameterSearch.lean`): the first four in
`r0`–`r3`, the rest on the stack, for the modulus width `state[1]`; and
`vg_dsa_parameter_search_init(state, p_len)`. The search allocates a frame
of `F` bytes whose base is the stack pointer: the callee-saved registers,
`out`, the pointers to `used` and `state`, and the search's state (`f…`).
`scratch` holds small buffers below byte 4096 (`s…`), the working space of
the functions it calls from byte 4096 (`sA`), and the RSA key working space
of its arithmetic after that (`sK`).

The seeds, the witnesses of their tests and the generator's `h` candidates
are all read from one tape, `rand`. Each seed, at the cursor `fC` (FIPS
186-4 A.1.1.2 and A.2.1):

1. q: the seed's `q_len` octets hashed (SHA-1 for a 160-bit q, else
   SHA-256: one block, by the compression function), its top and low bits
   set, tested by `vg_dsa_probable_prime` of size `N` with witnesses from
   `rand` after the seed (`fUsed`, the octets of `rand` read so far).
2. p: for each of the `4 L` counters, the hashes of `seed + offset + j`
   (big-endian, `seedlen` bytes) for `j ≤ count`, assembled into `X` with its
   top bit set; `p = X − (X mod 2q) + 1`, by division of `X` by `q` in the
   key working space (the quotient's parity gives `X mod 2q`, and the
   quotient with its low bit cleared is `(p − 1) / q`); if `p` has `L` bits,
   tested by `vg_dsa_probable_prime` of size `L`.
3. g: for each `h` of the window of `rand` after p's witnesses (`fHs`,
   `fHsLen`: at most `generatorAttempts` candidates of `p_len` octets) with
   `1 < h < p − 1`, `g = h^((p−1)/q) mod p` by `vg_dsa_pow_{n}_{e}`, until
   `g > 1`. The candidates it read count as read; without a g, a window
   shorter than `generatorAttempts` candidates ran out.
4. p||q||g checked by `vg_dsa_check_parameters`.

A seed sets `fStatus` to 2 if `rand` ran out inside it, to 1 with p||q||g
when the domain passes, and leaves it 0 when it is rejected: the controller
(`search`) then counts it against the seeds left (`fSeedLeft`, from
`state[0]`) and moves the cursor past it. It stops with no seeds left
(`fStatus` = 3), a tape too short for the next seed or one that ran out
(2), or parameters (1); `finish` puts the result's words in the frame
(`fRU`, `fRet`, `fR0`, `fR3`), writes `out`, then `used`, `state[0]` and
`state[3]` (their high halves zero) and returns the protocol's status
(`Entropy.Outcome.status`), asking, after a tape that ran out, for twice the
octets left (at least `256 p_len`, at most the entropy budget), unless they
reached the budget. ARMv7's conditions are `eq` and `ne` alone: an unsigned
comparison is the carry of a subtraction (`less`).
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.Generation
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Rsa.Arm.Keys

/-! ## The frame -/

/-- The frame's bytes. -/
def F : Nat := 128

/-- The callee-saved registers and their offsets. -/
def saved : List (Reg × Nat) :=
  [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20), (.r10, 24), (.r11, 28), (.lr, 32)]

def fOut : Nat := 40
/-- The pointers to `used` and to `state`. -/
def fUsedP : Nat := 44
def fStP : Nat := 68
def fSeed : Nat := 48
def fSeedLeft : Nat := 52
def fUsed : Nat := 56
def fCounter : Nat := 60
def fOffset : Nat := 64
def fH : Nat := 72
def fHLeft : Nat := 76
def fStatus : Nat := 80
def fScratch : Nat := 84
/-- The octets a test read, a 64-bit word. -/
def fUsedOut : Nat := 88
def fWit : Nat := 96
def fWitLen : Nat := 100
/-- A test's result, the p search's and the generator search's state. -/
def fRes : Nat := 104
def fP : Nat := 108
def fG : Nat := 112
/-- The cursor: the current seed's start in `rand`. -/
def fC : Nat := 116
/-- The window of `h` candidates: its start and its length. -/
def fHs : Nat := 120
def fHsLen : Nat := 124
/-- The result's words, `used`, the status, `state[0]` and `state[3]`, in the
words of the search for p (`fCounter`, `fOffset`, `fP`, `fG`), which no
longer hold anything by then. -/
def fRU : Nat := 60
def fRet : Nat := 64
def fR0 : Nat := 108
def fR3 : Nat := 112

/-- The `i`-th stack argument. -/
def arg (i : Nat) : Nat := F + 4 * i

/-- `r` := the frame word at `o`. -/
def ld (r : Reg) (o : Nat) : Instr := .ldrSp r o

/-- The frame word at `o` := `r` (through `r12`). -/
def st (r : Reg) (o : Nat) : List Instr := [.addSp .r12 0, .str r .r12 o]

/-- The frame word at `o` := `v`. -/
def stImm (o v : Nat) : List Instr := [.mov .r1 (.imm (BitVec.ofNat 32 v))] ++ st .r1 o

/-- `Z` iff `r0 < r1`, unsigned: the carry of `r0 − r1`, through `r12`. -/
def less : List Instr :=
  [.subs .r12 .r0 (.reg .r1), .mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0), .cmp .r12 (.imm 0)]

/-- `d` := `v`, a 32-bit constant. -/
def cst (d : Reg) (v : Nat) : List Instr :=
  [.movw d (BitVec.ofNat 16 (v % 2 ^ 16)), .movt d (BitVec.ofNat 16 (v / 2 ^ 16))]

/-! ## The scratch -/

def sMsg : Nat := 0
def sState : Nat := 64
def sQ : Nat := 128
def sX : Nat := 192
def sPBE : Nat := 576
def sG : Nat := 1728
def sPacked : Nat := 2112
def sA : Nat := 4096

/-- The working space of the functions we call. -/
def wa (pLen : Nat) : Nat := 128 * pLen + 640

/-- The key working space. -/
def sK (pLen : Nat) : Nat := sA + wa pLen
def kz (pLen : Nat) : Nat := 128 * pLen + 256

/-- `d` := `scratch + o`, from the key working space's base in `r8`
(through `r12`). -/
def scr (L : Nat) (d : Reg) (o : Nat) : List Instr :=
  [.movw .r12 (BitVec.ofNat 16 (sK L - o)), .dp .sub d .r8 (.reg .r12)]

/-! ## Bytes -/

/-- `n > 0` bytes copied (`copyBytes`): `src` sets `r1` to the source, then
`dst` sets `r0` to the destination. -/
def copyN (dst : List Instr) (src : List Instr) (n : Nat) : Prog isa :=
  .seq (.block (src ++ dst ++ [.movw .lr (BitVec.ofNat 16 n)])) copyBytes

/-- From `scratch + src` to `scratch + dst`. -/
def copyS (L dst src n : Nat) : Prog isa := copyN (scr L .r0 dst) (scr L .r1 src) n

/-- A byte of the big-endian addition: `[r0] + r1`, its carry and the
addend's higher bytes on in `r1`. -/
def addStep : List Instr :=
  [.ldrb .r3 .r0 0, .dp .add .r3 .r3 (.reg .r1), .strb .r3 .r0 0, .mov .r1 (.shifted .r3 .lsr 8),
    .dp .sub .r0 .r0 (.imm 1), .subs .r2 .r2 (.imm 1)]

/-- The `n` big-endian bytes ending at `r0` plus `r1`, modulo `2^(8 n)`. -/
def addBE (n : Nat) : Prog isa :=
  .seq (.block [.mov .r2 (.imm (BitVec.ofNat 32 n))]) (.loop (.block addStep) .ne)

/-- `offset + j` (the frame word `fOffset` plus `j`) added to the `n`-byte
seed at `sMsg`. -/
def seedAdd (L n j : Nat) : Prog isa := seqs [
  .block (scr L .r0 (sMsg + n - 1)), .block [ld .r1 fOffset],
  .block [.dp .add .r1 .r1 (.imm (BitVec.ofNat 32 j))],
  addBE n]

/-- A byte zeroed: `strb r3`, then on. -/
def zeroStep : List Instr := [.strb .r3 .r0 0, .dp .add .r0 .r0 (.imm 1), .subs .lr .lr (.imm 1)]

/-! ## Hashes -/

/-- A hash function by its compression function. -/
structure Hash where
  /-- The words of the hash value. -/
  k : Nat
  iv : List (BitVec 32)
  name : String
  code : Prog isa

/-- SHA-1, for a 160-bit q. -/
def sha1 : Hash := ⟨5, Spec.Sha1.H0.toList, "vg_sha1_compress", VG.Impl.Sha1.Arm.compress⟩

/-- SHA-256. -/
def sha256 : Hash := ⟨8, Spec.Sha256.H0.toList, "vg_sha256_compress", VG.Impl.Sha256.Arm.compress⟩

/-- A 32-bit constant into `r1`. -/
def const (v : BitVec 32) : List Instr :=
  [.movw .r1 (v.extractLsb' 0 16), .movt .r1 (v.extractLsb' 16 16)]

/-- The initial hash value at `r0`. -/
def ivStore (iv : List (BitVec 32)) : List Instr :=
  iv.zipIdx.flatMap fun (v, i) => const v ++ [.str .r1 .r0 (4 * i)]

/-- The block at `sMsg` hashed into `dst`: the initial hash value at
`sState`, the block compressed into it with the working space at `sA`, and
its words big-endian at `dst` (through `r9`, set back). -/
def hash (L : Nat) (G : Hash) (dst : Nat) : Prog isa := seqs [
  .block (scr L .r0 sState ++ ivStore G.iv ++ scr L .r1 sMsg ++ scr L .r3 sA),
  VG.Impl.MdStream.Arm.compressAt G.name G.code,
  .block (scr L .r6 dst ++ VG.Impl.MdStream.Arm.out32 G.k true ++ [.mov .r9 (.imm (BitVec.ofNat 32 (L / 4)))])]

/-- The block's padding after a message of `n < 56` bytes. -/
def padInit (L n : Nat) : List Instr :=
  scr L .r0 sMsg ++ [.mov .r3 (.imm 0)] ++ (List.range 16).map (fun i => .str .r3 .r0 (4 * i)) ++
    [.mov .r1 (.imm 0x80), .strb .r1 .r0 n,
      .mov .r1 (.imm (BitVec.ofNat 32 ((8 * n) / 256))), .strb .r1 .r0 62,
      .mov .r1 (.imm (BitVec.ofNat 32 ((8 * n) % 256))), .strb .r1 .r0 63]

/-! ## Calls -/

/-- A call, its stack arguments pushed (`r4`–`r11`, to keep `sp` 8-byte
aligned). -/
def callWith (name : String) (callee : Prog isa) : Prog isa :=
  .frame (.push [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]) (.call name callee) (.pop .r4 32)

/-- A probable-prime test of the candidate of `bits` bits at `sA`, with the
witnesses left (from `witnesses` itself when none is: an empty range within
the tape): its result into `fRes`, and the octets it read added to `fUsed`
unless it ran out. The size is the second stack argument, in `r5`. -/
def test (pLen bits : Nat) (name : String) (callee : Prog isa) : Prog isa := seqs [
  .block (scr pLen .r0 sA ++ [.movw .r1 (BitVec.ofNat 16 (wa pLen / 8)), .movw .r5 (BitVec.ofNat 16 bits)]),
  .block [ld .r4 fUsed, ld .r2 fWit, ld .r3 fWitLen],
  .block [.dp .add .r2 .r2 (.reg .r4), .dp .sub .r3 .r3 (.reg .r4), .addSp .r4 fUsedOut, .cmp .r3 (.imm 0)],
  .ite .eq (.block [ld .r2 fWit]) (.block []),
  callWith name callee,
  .block (st .r0 fRes),
  .block [.cmp .r0 (.imm 0)],
  .ite .eq (.block [])
    (seqs [.block [ld .r1 fUsedOut, ld .r2 fUsed], .block [.dp .add .r2 .r2 (.reg .r1)], .block (st .r2 fUsed)])]

/-! ## Arithmetic, in the key working space -/

/-- The arrays: the dividend `X` and then the quotient, the remainder, the
divisor `q`, the division's temporary, `X`, `X − r`, `q` or 0, `p − 1`, `p`,
`(p − 1) / q`, `h`, 1, `g`, 0, and a temporary. -/
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
def aG : Nat := 12
def aZero : Nat := 13
def aTmp : Nat := 14
def nArrs : Nat := 15

/-- Header slots. -/
def slOdd : Nat := 120
def slLo : Nat := 124
def slHi : Nat := 128
def slG : Nat := 136

/-- `r9` and `r7`: the words of the key working space and the stride, which
the division changes. -/
def wRegs (pLen : Nat) : List Instr := [.mov .r9 (.imm (BitVec.ofNat 32 (pLen / 4)))] ++ stride

/-- `r8`, `r9` and `r7`: the key working space, its words and the stride,
which the search keeps. -/
def ksRegs (pLen : Nat) : List Instr :=
  [ld .r8 fScratch, .movw .r12 (BitVec.ofNat 16 (sK pLen)), .dp .add .r8 .r8 (.reg .r12)] ++ wRegs pLen

/-- The words into the division's header, every array zeroed and 1 set. -/
def ksSetup : Prog isa :=
  .seq (.block [.str .r9 .r8 16, .dp .add .r0 .r8 (.imm (BitVec.ofNat 32 hdr)),
      .mov .lr (.imm (BitVec.ofNat 32 nArrs)), .mul .lr .lr .r7, .mov .lr (.shifted .lr .lsr 2),
      .mov .r3 (.imm 0)])
    (.seq zero (.block (setOne aOne)))

/-- Array `j` := the `n` big-endian bytes at `scratch + o`. -/
def loadS (L j o n : Nat) : Prog isa :=
  .seq (.block (scr L .r4 o ++ [.movw .r6 (BitVec.ofNat 16 n)])) (VG.Impl.Rsa.Arm.CrtValues.load j)

/-- `scratch + o` := `[j]`'s low `n` bytes, big-endian. -/
def storeBE (L j o n : Nat) : Prog isa :=
  .seq (.block (ptr .r1 j ++ [.movw .r2 (BitVec.ofNat 16 (n - 1)), .dp .add .r1 .r1 (.reg .r2)] ++ scr L .r0 o ++
    [.movw .lr (BitVec.ofNat 16 n)])) reverseBytes

/-- The slot `d` := `[a] < [b]`. -/
def ltS (d a b : Nat) : List (Prog isa) := [sub3 aTmp a b, .block [.str .r11 .r8 d]]

/-- `p` and `(p − 1) / q` from `X` at `sX` and `q` at `sQ`: `p` in array
`aP` and to `sPBE` (big-endian), `(p − 1) / q` in array `aE`. -/
def pArith (pLen qLen : Nat) : Prog isa := seqs [
  seqs [ksSetup, loadS pLen aQt sX pLen, loadS pLen aX sX pLen, loadS pLen aDv sQ qLen],
  seqs [.block (VG.Impl.Rsa.Arm.CrtValues.divHdr aQt aRm aDv aDt), VG.Impl.Rsa.Arm.Div.code, .block (wRegs pLen)],
  seqs [sub3 aT aX aRm, .block (bitOf slOdd aQt), sel aS aZero aDv slOdd, sub3 aPm1 aT aS],
  seqs [copy aP aPm1, .block (orOne aP), copy aE aQt, .block (clrLow aE), storeBE pLen aP sPBE pLen]]

/-! ## The search -/

/-- The frame word `o` compared with `v`. -/
def cmpF (o v : Nat) : List Instr := [ld .r0 o, .cmp .r0 (.imm (BitVec.ofNat 32 v))]

/-- The geometry and the functions called. -/
structure Geo where
  pLen : Nat
  qLen : Nat
  /-- The words of `(p − 1) / q` for the exponentiation. -/
  e : Nat
  G : Hash
  qName : String
  qCode : Prog isa
  pName : String
  pCode : Prog isa
  powName : String
  powCode : Prog isa
  /-- Byte offsets of the exponentiation's numbers in its working space. -/
  powMod : Nat
  powBase : Nat
  powExp : Nat
  powRes : Nat
  checkName : String
  checkCode : Prog isa

namespace Geo
variable (g : Geo)

/-- `(L − 1) / N`. -/
def count : Nat := (8 * g.pLen - 1) / (8 * g.qLen)

/-- q from the seed: hashed, shaped, at `sA`, and tested. -/
def qPart : Prog isa := seqs [
  copyN (scr g.pLen .r0 sMsg) [ld .r1 fSeed] g.qLen,
  hash g.pLen g.G sQ,
  .block (scr g.pLen .r0 sQ ++ [.ldrb .r1 .r0 0, .dp .orr .r1 .r1 (.imm 0x80), .strb .r1 .r0 0,
    .ldrb .r1 .r0 (g.qLen - 1), .dp .orr .r1 .r1 (.imm 1), .strb .r1 .r0 (g.qLen - 1)]),
  copyS g.pLen sA sQ g.qLen,
  test g.pLen (8 * g.qLen) g.qName g.qCode]

/-- The hash of `seed + offset + j`, into its place in `X`. -/
def pHash (j : Nat) : Prog isa := seqs [
  copyN (scr g.pLen .r0 sMsg) [ld .r1 fSeed] g.qLen,
  seedAdd g.pLen g.qLen j,
  hash g.pLen g.G (sX + g.pLen - (j + 1) * g.qLen)]

/-- The first `m` hashes of `X`. -/
def pHashes : Nat → Prog isa
  | 0 => .block []
  | m + 1 => .seq (pHashes m) (g.pHash m)

/-- `X`: the hashes, the top bit set. -/
def pX : Prog isa :=
  .seq (g.pHashes (g.count + 1))
    (.block (scr g.pLen .r0 sX ++ [.ldrb .r1 .r0 0, .dp .orr .r1 .r1 (.imm 0x80), .strb .r1 .r0 0]))

/-- A counter's candidate: `fP` := 0 if the witnesses ran out, 1 if it is a
probable prime, else as it was. -/
def pAttempt : Prog isa := seqs [
  g.pX, pArith g.pLen g.qLen,
  .block (scr g.pLen .r0 sPBE ++ [.ldrb .r1 .r0 0, .dp .and .r1 .r1 (.imm 0x80), .cmp .r1 (.imm 0)]),
  .ite .eq (.block [])
    (seqs [copyS g.pLen sA sPBE g.pLen, test g.pLen (8 * g.pLen) g.pName g.pCode,
      .block (cmpF fRes 0), .ite .eq (.block (stImm fP 0))
        (seqs [.block (cmpF fRes 1), .ite .eq (.block (stImm fP 1)) (.block [])])])]

/-- The next counter: Z when the `4 L` are done. -/
def pAdvance : Prog isa := seqs [
  .block [ld .r1 fCounter], .block [.dp .add .r1 .r1 (.imm 1)], .block (st .r1 fCounter),
  .block [ld .r2 fOffset], .block [.dp .add .r2 .r2 (.imm (BitVec.ofNat 32 (g.count + 1)))],
  .block (st .r2 fOffset), .block [.movw .r2 (BitVec.ofNat 16 (32 * g.pLen)), .cmp .r1 (.reg .r2)]]

/-- p: `fP` := 0, 1 or 2 (none found). -/
def pPart : Prog isa := seqs [
  .block (stImm fCounter 0), .block (stImm fOffset 1), .block (stImm fP 4),
  .loop (seqs [g.pAttempt, .block (cmpF fP 4),
    .ite .eq (seqs [g.pAdvance, .ite .eq (.block (stImm fP 2)) (.block [])]) (.block []),
    .block (cmpF fP 4)]) .eq]

/-- An `h`: `fG` := 1 with `g` at `sG` if `1 < h < p − 1` and `g > 1`. -/
def gStep : Prog isa := seqs [
  .block [ld .r4 fH], .block [.movw .r6 (BitVec.ofNat 16 g.pLen)],
  VG.Impl.Rsa.Arm.CrtValues.load aH,
  seqs (ltS slLo aOne aH), seqs (ltS slHi aH aPm1),
  .block (andS slLo slLo slHi ++ [.ldr .r1 .r8 slLo, .cmp .r1 (.imm 0)]),
  .ite .eq (.block [])
    (seqs [copyN (scr g.pLen .r0 (sA + g.powMod)) (ptr .r1 aP) g.pLen,
      copyN (scr g.pLen .r0 (sA + g.powBase)) (ptr .r1 aH) g.pLen,
      copyN (scr g.pLen .r0 (sA + g.powExp)) (ptr .r1 aE) (4 * g.e),
      .block (scr g.pLen .r0 sA ++ [.movw .r1 (BitVec.ofNat 16 (wa g.pLen / 8))]),
      .call g.powName g.powCode,
      copyN (ptr .r0 aG) (scr g.pLen .r1 (sA + g.powRes)) g.pLen,
      seqs (ltS slG aOne aG),
      .block [.ldr .r1 .r8 slG, .cmp .r1 (.imm 0)],
      .ite .eq (.block [])
        (seqs [storeBE g.pLen aG sG g.pLen, .block (stImm fG 1)])])]

/-- The window of `h` candidates: `rand` after the octets read (`fHs`), and
at most `generatorAttempts` candidates' octets of it (`fHsLen`). -/
def gWindow : Prog isa := seqs [
  .block [ld .r1 fUsed], .block [ld .r0 fWit], .block [.dp .add .r0 .r0 (.reg .r1)], .block (st .r0 fHs),
  .block [ld .r0 fWitLen], .block ([.dp .sub .r0 .r0 (.reg .r1)] ++ cst .r1 (128 * g.pLen) ++ less),
  .ite .eq (.block (st .r0 fHsLen)) (.block (st .r1 fHsLen))]

/-- g over the window: `fG` := 1, or 2 if no `h` gives one, with at least
`p_len` octets left before each. -/
def gPart : Prog isa := seqs [
  .block [ld .r1 fHs], .block (st .r1 fH), .block [ld .r1 fHsLen], .block (st .r1 fHLeft),
  .block (stImm fG 4),
  .loop (seqs [.block [ld .r0 fHLeft], .block ([.movw .r1 (BitVec.ofNat 16 g.pLen)] ++ less),
    .ite .eq (.block (stImm fG 2))
      (seqs [g.gStep, .block [ld .r1 fH], .block [.movw .r2 (BitVec.ofNat 16 g.pLen), .dp .add .r1 .r1 (.reg .r2)],
        .block (st .r1 fH), .block [ld .r1 fHLeft], .block [.dp .sub .r1 .r1 (.reg .r2)], .block (st .r1 fHLeft)]),
    .block (cmpF fG 4)]) .eq]

/-- The candidates the search for g read count as read. -/
def gUsed : Prog isa := seqs [
  .block [ld .r0 fH], .block [ld .r1 fWit], .block [.dp .sub .r0 .r0 (.reg .r1)], .block (st .r0 fUsed)]

/-- Without a g, a window shorter than `generatorAttempts` candidates ran out. -/
def gShort : Prog isa := seqs [
  .block [ld .r0 fHsLen], .block (cst .r1 (128 * g.pLen) ++ less),
  .ite .eq (.block (stImm fStatus 2)) (.block [])]

/-- p||q||g, checked: `fStatus` := 1 if it passes. -/
def checkPart : Prog isa := seqs [
  copyS g.pLen sPacked sPBE g.pLen, copyS g.pLen (sPacked + g.pLen) sQ g.qLen, copyS g.pLen (sPacked + g.pLen + g.qLen) sG g.pLen,
  .block (scr g.pLen .r0 sPacked ++ [.movw .r1 (BitVec.ofNat 16 (2 * g.pLen + g.qLen)),
    .movw .r2 (BitVec.ofNat 16 g.pLen), .mov .r3 (.imm (BitVec.ofNat 32 g.qLen))] ++ scr g.pLen .r4 sA ++
    [.movw .r5 (BitVec.ofNat 16 (wa g.pLen / 8))]),
  callWith g.checkName g.checkCode,
  .block [.cmp .r0 (.imm 1)],
  .ite .eq (.block (stImm fStatus 1)) (.block [])]

/-- A seed: `fStatus` := 2 if `rand` ran out, 1 if the domain passes, else as
it was (0). -/
def attempt : Prog isa := seqs [
  g.qPart, .block (cmpF fRes 0),
  .ite .eq (.block (stImm fStatus 2))
    (seqs [.block (cmpF fRes 1),
      .ite .eq
        (seqs [g.pPart, .block (cmpF fP 0),
          .ite .eq (.block (stImm fStatus 2))
            (seqs [.block (cmpF fP 1),
              .ite .eq (seqs [g.gWindow, g.gPart, gUsed, .block (cmpF fG 1), .ite .eq g.checkPart g.gShort])
                (.block [])])])
        (.block [])])]

/-- `Z` iff fewer octets than a seed's are left after the cursor. -/
def avail : Prog isa := seqs [
  .block [ld .r0 fWitLen], .block [ld .r1 fC],
  .block [.dp .sub .r0 .r0 (.reg .r1), .movw .r1 (BitVec.ofNat 16 g.qLen)], .block less]

/-- The next seed starts at the cursor, its witnesses after it. -/
def seedStart : Prog isa := seqs [
  .block [ld .r0 fWit], .block [ld .r1 fC], .block [.dp .add .r0 .r0 (.reg .r1)], .block (st .r0 fSeed),
  .block [.dp .add .r1 .r1 (.imm (BitVec.ofNat 32 g.qLen))], .block (st .r1 fUsed)]

/-- A rejected seed: the cursor past it, one seed fewer left. -/
def rejected : Prog isa := seqs [
  .block [ld .r0 fUsed], .block (st .r0 fC), .block [ld .r0 fSeedLeft], .block [.dp .sub .r0 .r0 (.imm 1)],
  .block (st .r0 fSeedLeft)]

/-- The seeds, one at a time, until a domain passes (`fStatus` = 1), `rand`
runs out (2) or the seeds do (3). -/
def search : Prog isa := seqs [
  .block (ksRegs g.pLen ++ padInit g.pLen g.qLen),
  .loop (seqs [.block (cmpF fSeedLeft 0),
    .ite .eq (.block (stImm fStatus 3))
      (seqs [g.avail,
        .ite .eq (.block (stImm fStatus 2))
          (seqs [g.seedStart, g.attempt, .block (cmpF fStatus 0), .ite .eq rejected (.block [])])]),
    .block (cmpF fStatus 0)]) .eq]

/-- The entropy budget, `32769 p_len`. -/
def budget : Nat := 32769 * g.pLen

/-- The result's words into the frame: `used` from the frame word `u`, the
status `v`, `state[0]` from `r2` and `state[3]` from `r3`. -/
def results (u v : Nat) : Prog isa := seqs [
  .block [ld .r0 u], .block (st .r0 fRU), .block (stImm fRet v), .block (st .r2 fR0), .block (st .r3 fR3)]

/-- No seeds left nor a request: `state[0]` and `state[3]` zero. -/
def zres (u v : Nat) : Prog isa := .seq (.block [.mov .r2 (.imm 0), .mov .r3 (.imm 0)]) (results u v)

/-- `rand` ran out at the cursor: exhausted if the octets left reach the
budget; else the seeds left, and the next tape's length, twice the octets
left, at least `256 p_len` and at most the budget. -/
def ranOut : Prog isa := seqs [
  .block [ld .r0 fWitLen], .block [ld .r1 fC], .block ([.dp .sub .r0 .r0 (.reg .r1)] ++ cst .r1 g.budget ++ less),
  .ite .eq
    (seqs [.block (cst .r1 (256 * g.pLen) ++ less),
      .ite .eq (.block [.mov .r0 (.reg .r1)]) (.block []),
      .block ([.dp .add .r0 .r0 (.reg .r0)] ++ cst .r1 g.budget ++ less),
      .ite .eq (.block []) (.block [.mov .r0 (.reg .r1)]),
      .block [.mov .r3 (.reg .r0)], .block [ld .r2 fSeedLeft],
      results fC 0])
    (zres fC 3)]

/-- `out` := p||q||g. -/
def outCopy : Prog isa := seqs [
  .block [ld .r0 fOut], .block (scr g.pLen .r1 sPacked ++ [.movw .lr (BitVec.ofNat 16 (2 * g.pLen + g.qLen))]),
  copyBytes]

/-- `out` := zeros. -/
def outZero : Prog isa := seqs [
  .block [ld .r0 fOut], .block [.mov .r3 (.imm 0), .movw .lr (BitVec.ofNat 16 (2 * g.pLen + g.qLen))],
  .loop (.block zeroStep) .ne]

/-- The result's words to `state` and `used`, their high halves zero, and the
status into `r0`. -/
def writeBack : Prog isa := seqs [
  .block [ld .r1 fStP], .block [ld .r0 fR0], .block [.mov .r2 (.imm 0), .str .r0 .r1 0, .str .r2 .r1 4],
  .block [ld .r0 fR3], .block [.str .r0 .r1 24, .str .r2 .r1 28],
  .block [ld .r1 fUsedP], .block [ld .r0 fRU], .block [.str .r0 .r1 0, .str .r2 .r1 4],
  .block [ld .r0 fRet]]

/-- The result: its words into the frame; p||q||g to `out` for status 1, else
zeros; then the words to `state` and `used`, and the status. -/
def finish : Prog isa := seqs [
  .block (cmpF fStatus 1),
  .ite .eq (zres fUsed 1) (seqs [.block (cmpF fStatus 2), .ite .eq g.ranOut (zres fC 3)]),
  .block (cmpF fStatus 1),
  .ite .eq g.outCopy g.outZero,
  writeBack]

def generate : Prog isa := .seq g.search g.finish

end Geo

/-! ## Entry -/

/-- Save the callee-saved registers, `out`, `used`, `rand` and its length,
`scratch` and `state`; the cursor at 0, searching. -/
def entry : List Instr :=
  [.addSp .r12 0] ++ saved.map (fun (r, o) => .str r .r12 o) ++
  [.str .r0 .r12 fOut, .str .r2 .r12 fUsedP, .str .r3 .r12 fWit,
    ld .r1 (arg 0), .str .r1 .r12 fWitLen, ld .r1 (arg 1), .str .r1 .r12 fScratch,
    ld .r1 (arg 3), .str .r1 .r12 fStP,
    .mov .r1 (.imm 0), .str .r1 .r12 fC, .str .r1 .r12 fStatus]

def restore : List Instr := saved.map fun (r, o) => ld r o

/-- `state[0]` (the seeds left) into `fSeedLeft`, and the three geometries,
by the modulus's width, `state[1]` (in `r2`). The pointer to `state` is
loaded in a block of its own, before the block that reads through it. -/
def dispatch (g1 g2 g3 : Geo) : Prog isa := seqs [
  .block [ld .r1 (arg 3)], .block [.ldr .r2 .r1 8, .ldr .r1 .r1 0], .block (st .r1 fSeedLeft),
  .block [.cmp .r2 (.imm 128)],
  .ite .eq g1.generate
    (.seq (.block [.cmp .r2 (.imm 0x100)]) (.ite .eq g2.generate g3.generate))]

/-- `vg_dsa_parameter_search`. -/
def code (g1 g2 g3 : Geo) : Prog isa :=
  .frame (.alloc F) (.seq (.block entry) (.seq (dispatch g1 g2 g3) (.block restore))) (.free F)

/-! ## `vg_dsa_parameter_search_init` -/

/-- `state` (`r0`) := `[4096, p_len, 32769 p_len, 512 p_len]` from `p_len`
(`r1`), the high halves zero (every value is below `2 ^ 32`), and 1, through
`r12`. -/
def initWords : List Instr := [
  .mov .r12 (.imm 0), .str .r12 .r0 4, .str .r12 .r0 12, .str .r12 .r0 20, .str .r12 .r0 28,
  .str .r1 .r0 8, .mov .r12 (.shifted .r1 .lsl 15), .dp .add .r12 .r12 (.reg .r1), .str .r12 .r0 16,
  .mov .r12 (.shifted .r1 .lsl 9), .str .r12 .r0 24, .movw .r12 4096, .str .r12 .r0 0, .mov .r0 (.imm 1)]

/-- `vg_dsa_parameter_search_init(state, p_len)`: the words for a supported
`p_len`, else zeros and 0 (the RSA prime search's `clear`). -/
def init : Prog isa :=
  .seq (.block [.cmp .r1 (.imm 128)])
    (.ite .eq (.block initWords)
      (.seq (.block [.cmp .r1 (.imm 0x100)])
        (.ite .eq (.block initWords)
          (.seq (.block [.cmp .r1 (.imm 0x180)])
            (.ite .eq (.block initWords) (.block VG.Impl.RsaKeyGen.Arm.SearchInit.clear))))))

end VG.Impl.Dsa.Arm.Generation
