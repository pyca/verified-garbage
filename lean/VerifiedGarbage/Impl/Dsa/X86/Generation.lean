module

public import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Impl.Dsa.X86.ProbablePrime
public import VerifiedGarbage.Impl.Rsa.X86.Div
public import VerifiedGarbage.Impl.Bignum.X86.LoadBE
public import VerifiedGarbage.Impl.Bignum.X86.StoreBE
public import VerifiedGarbage.Impl.Bignum.X86.CopyBytes
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Impl.Pbkdf2.Md.X86

/-!
# DSA parameter generation over refillable random tapes on baseline i686 (cdecl)

`vg_dsa_parameter_search(out, out_len, used, rand, rand_len, scratch,
scratch_len, state)` (`Spec/Dsa/ParameterSearch.lean`), every argument on
the stack, for the modulus width `state[1]`, and
`vg_dsa_parameter_search_init(state, p_len)`. The callee-saved registers are
pushed, and `edi` holds `scratch` throughout: every function called keeps it,
and both the exponentiation's working space and the division's arrays are at
fixed offsets from it. `scratch` holds, at fixed offsets: the exponentiation's
working space (from byte 0, `Pow.layout`), the search's state (`f…`), the hash
value and block and the compression function's scratch space, `X`, p||q||g
(`sPk`), the division's and the comparisons' arrays (`arr`), the
probable-prime test's working space (`sPP`) and `vg_dsa_check_parameters`'s
scratch (`sChk`).

The seeds, the witnesses of their tests and the generator's `h` candidates
are all read from one tape, `rand`. Each seed, at the cursor `fC` (FIPS 186-4
A.1.1.2 and A.2.1):

1. q: the seed's `q_len` octets hashed (SHA-1 for a 160-bit q, else SHA-256:
   one block, by the compression function), its top and low bits set, into
   p||q||g, and tested by `vg_dsa_probable_prime_{N}` with witnesses from
   `rand` after the seed (`fUsed`, the octets of `rand` read so far).
2. p: for each of the `4 L` counters, the hashes of `seed + offset + j`
   (big-endian, `seedlen` bytes) for `j ≤ count`, assembled into `X` with
   its top bit set; `X` divided by `2 q` (RSA's division), `p − 1 = X − (X
   mod 2 q)` and `(p − 1) / q = 2 ⌊X / 2 q⌋`; `p` into p||q||g, and if it has
   `L` bits, tested by `vg_dsa_probable_prime_{L}`.
3. g: for each `h` of the window of `rand` after p's witnesses (`fHs`,
   `fHsLen`: at most `generatorAttempts` candidates of `p_len` octets) with
   `1 < h < p − 1`, `g = h^((p−1)/q) mod p` by `vg_dsa_pow_{n}_{e}`, until
   `g > 1`, into p||q||g. The candidates it read count as read; without a
   g, a window shorter than `generatorAttempts` candidates ran out.
4. p||q||g checked by `vg_dsa_check_parameters`.

A seed sets `fStatus` to 2 if `rand` ran out inside it, to 1 with p||q||g
when the domain passes, and leaves it 0 when it is rejected: the controller
(`search`) then counts it against the seeds left (`fSeedLeft`, from
`state[0]`) and moves the cursor past it. It stops with no seeds left
(`fStatus` = 3), a tape too short for the next seed or one that ran out
(2), or parameters (1); `finish` writes `out`, `used` and `state` and
returns the protocol's status (`Entropy.Outcome.status`), asking, after a
tape that ran out, for twice the octets left (at least `256 p_len`, at most
the entropy budget), unless they reached the budget. Every branch and loop
count depends on the lengths, `state` and `rand`, which the contract makes
public, and on nothing else.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Bignum.X86

def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [p] => p
  | p :: ps => .seq p (seqs ps)

/-! ## The scratch -/

/-- The search's state. -/
def hdr : Nat := 7168
def fOut : Nat := hdr
def fSeed : Nat := hdr + 4
def fSeedLeft : Nat := hdr + 8
/-- The pointers to `used` and to `state`. -/
def fUsedP : Nat := hdr + 12
def fStP : Nat := hdr + 16
/-- `rand` and its length. -/
def fWit : Nat := hdr + 20
def fWitLen : Nat := hdr + 24
/-- The octets of `rand` read so far. -/
def fUsed : Nat := hdr + 28
/-- The octets a test read, a 64-bit word. -/
def fUsedOut : Nat := hdr + 32
/-- A test's result, and the state of the searches. -/
def fRes : Nat := hdr + 40
def fCounter : Nat := hdr + 44
def fOffset : Nat := hdr + 48
def fP : Nat := hdr + 52
def fH : Nat := hdr + 56
def fHLeft : Nat := hdr + 60
def fG : Nat := hdr + 64
def fStatus : Nat := hdr + 68
/-- The comparisons' masks. -/
def fLo : Nat := hdr + 72
/-- The cursor: the current seed's start in `rand`. -/
def fC : Nat := hdr + 76
/-- The window of `h` candidates: its start and its length. -/
def fHs : Nat := hdr + 80
def fHsLen : Nat := hdr + 84

/-- The hash value, the block right after it, and the compression
function's scratch space. -/
def sState : Nat := 7296
def sHScr : Nat := 7424
/-- `X`, big-endian; the high hash may start up to 12 bytes before it. -/
def sX : Nat := 8032
/-- p||q||g, big-endian. -/
def sPk : Nat := 8448
/-- The arrays of 32-bit words, little-endian. -/
def arr (k : Nat) : Nat := 9728 + 400 * k
/-- The probable-prime test's working space, and its 64-bit words. -/
def sPP : Nat := 14848
def ppWords : Nat := 1480
/-- `vg_dsa_check_parameters`'s scratch. -/
def sChk : Nat := 26880

/-- The arrays: the dividend `X` and then the quotient, the remainder, the
divisor `2 q`, the division's temporary, `X`, `p − 1`, `(p − 1) / q`, 1, a
temporary (`q`, then the comparisons'), `h` and `p`. -/
def aQt : Nat := arr 0
def aRm : Nat := arr 1
def aDv : Nat := arr 2
def aDt : Nat := arr 3
def aX : Nat := arr 4
def aPm1 : Nat := arr 5
def aE : Nat := arr 6
def aOne : Nat := arr 7
def aTmp : Nat := arr 8
def aH : Nat := arr 9
def aP : Nat := arr 10

/-! ## Bytes -/

/-- `d := edi + o`. -/
def scr (d : Reg) (o : Nat) : List Instr := [.mov d (.reg .edi), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- `n > 0` bytes from `esi` (set by `src`) to `scratch + dst`. -/
def copyTo (src : List Instr) (dst n : Nat) : Prog isa :=
  .seq (.block (src ++ scr .ebx dst ++ [.mov .ecx (.imm (BitVec.ofNat 32 n))])) copyBytes

/-- `n > 0` bytes from `scratch + src` to `scratch + dst`. -/
def copyS (dst src n : Nat) : Prog isa := copyTo (scr .esi src) dst n

/-- The state word at `o` := `v`. -/
def stImm (o v : Nat) : List Instr := [.mov .eax (.imm (BitVec.ofNat 32 v)), .store (sc o) .eax]

/-- The state word at `o` compared with `v`. -/
def cmpF (o v : Nat) : List Instr := [.mov .eax (.mem (sc o)), .alu .cmp .eax (.imm (BitVec.ofNat 32 v))]

/-- A byte of the big-endian addition: `[edx] + ecx`, its carry and the
addend's higher bytes on in `ecx`; `esi` counts the bytes. -/
def addStep : List Instr :=
  [.movzx8 .eax (at_ .edx 0), .alu .add .eax (.reg .ecx), .store8 (at_ .edx 0) .al,
    .shift .shr .eax 8, .mov .ecx (.reg .eax), .alu .sub .edx (.imm 1), .alu .sub .esi (.imm 1),
    .alu .cmp .esi (.imm 0)]

/-- The `n` big-endian bytes ending at `edx` plus `ecx`, modulo `2^(8 n)`. -/
def addBE (n : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.imm (BitVec.ofNat 32 n))]) (.loop (.block addStep) .ne)

/-- The byte at `scratch + o` ORed with `v`. -/
def orByte (o v : Nat) : List Instr :=
  [.movzx8 .eax (sc o), .alu .or .eax (.imm (BitVec.ofNat 32 v)), .store8 (sc o) .al]

/-! ## Hashes -/

/-- The end of the block of a message of `n` bytes: `0x80`, zeros and the
length in bits, big-endian, in 8 bytes. -/
def padBytes (n : Nat) : List Byte :=
  [(0x80 : Byte)] ++ List.replicate (64 - 9 - n) (0 : Byte) ++
    (List.range 8).map fun i => BitVec.ofNat 8 ((8 * n) >>> (8 * (7 - i)))

/-- The little-endian bytes of the words `iv`. -/
def ivBytes (iv : List (BitVec 32)) : List Byte :=
  iv.flatMap fun w => (List.range 4).map fun i => w.extractLsb' (8 * i) 8

/-- The initial value into the hash value at `ebx`. -/
def ivStore (iv : List (BitVec 32)) : List Instr :=
  Impl.Pbkdf2.Md.X86.storeW .ebx 0 (ivBytes iv) iv.length

/-- The message of `n` bytes in the block hashed from the initial value
`iv`, its digest to `scratch + dst`. -/
def hash (H : Impl.Pbkdf2.Md.X86.Hash) (iv : List (BitVec 32)) (n dst : Nat) : Prog isa := seqs [
  .block (scr .ebx sState ++ ivStore iv ++
    Impl.Pbkdf2.Md.X86.storeW .ebx (H.N + n) (padBytes n) ((64 - n) / 4) ++
    [.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 H.N))] ++ scr .ebp sHScr),
  Impl.MdStream.X86.compressAt H.compN H.compC .ebx .ebp,
  .block (scr .ebx sState ++ scr .eax dst ++ H.out)]

/-! ## Calls -/

/-- A probable-prime test of the candidate at its place in `sPP`, with the
witnesses left (none, at the start of the tape, once all are read): its
result into `fRes`, and the octets it read added to `fUsed` unless it ran
out. -/
def test (name : String) (callee : Prog isa) : Prog isa := seqs [
  .block [.mov .ecx (.mem (sc fUsed)), .mov .edx (.mem (sc fWit)), .alu .add .edx (.reg .ecx),
    .mov .ebx (.mem (sc fWitLen)), .alu .sub .ebx (.reg .ecx)],
  .ite .e (.block [.mov .edx (.mem (sc fWit))]) (.block []),
  .block (scr .eax sPP ++ [.mov .ecx (.imm (BitVec.ofNat 32 ppWords))] ++ scr .ebp fUsedOut),
  .frame (.push [.ebp, .ebx, .edx, .ecx, .eax]) (.call name callee) (.pop .ecx 5),
  .block [.store (sc fRes) .eax, .alu .cmp .eax (.imm 0)],
  .ite .e (.block [])
    (.block [.mov .eax (.mem (sc fUsedOut)), .alu .add .eax (.mem (sc fUsed)), .store (sc fUsed) .eax])]

/-- `vg_dsa_check_parameters` of p||q||g: `fStatus` := 1 if it passes. -/
def check (pLen qLen chkWords : Nat) (name : String) (callee : Prog isa) : Prog isa := seqs [
  .block (scr .eax sPk ++ [.mov .ecx (.imm (BitVec.ofNat 32 (2 * pLen + qLen))),
    .mov .edx (.imm (BitVec.ofNat 32 pLen)), .mov .ebx (.imm (BitVec.ofNat 32 qLen))] ++ scr .esi sChk ++
    [.mov .ebp (.imm (BitVec.ofNat 32 chkWords))]),
  .frame (.push [.ebp, .esi, .ebx, .edx, .ecx, .eax]) (.call name callee) (.pop .ecx 6),
  .block [.alu .cmp .eax (.imm 1)],
  .ite .e (.block (stImm fStatus 1)) (.block [])]

/-! ## Arithmetic -/

/-- Array `o` := the `len` big-endian bytes at `scratch + src`, as `2 k`
words. -/
def loadS (k o src len : Nat) : Prog isa :=
  .seq (.block (scr .esi src ++ [.mov .ecx (.imm (BitVec.ofNat 32 len))])) (loadBE k o)

/-- The `len` big-endian bytes at `scratch + dst` := array `o`. -/
def storeS (o dst len : Nat) : Prog isa :=
  .seq (.block (scr .ebx dst ++ [.mov .ecx (.imm (BitVec.ofNat 32 len))])) (storeBE o)

/-- `p` and `(p − 1) / q` from `X` and `q` (`n` words of `p`): `p − 1` and
`(p − 1) / q` in their arrays, `p` in its array and in p||q||g. -/
def pArith (pLen qLen : Nat) : Prog isa :=
  let n := pLen / 4
  seqs [
    loadS (pLen / 8) aQt sX pLen, loadS (pLen / 8) aX sX pLen,
    loadS (pLen / 8) aTmp (sPk + pLen) qLen, .block [.mov .eax (.imm 0), .store (sc (aTmp + 4 * n)) .eax],
    chainW .adc (n + 1) aDv aTmp aTmp,
    Rsa.X86.Div.code n aQt aRm aDv aDt,
    chainW .sbb n aPm1 aX aRm,
    chainW .adc n aE aQt aQt,
    setConstW n aOne 1,
    chainW .adc n aP aPm1 aOne,
    storeS aP sPk pLen]

/-! ## The search -/

/-- The geometry and the functions called. -/
structure Geo where
  pLen : Nat
  qLen : Nat
  /-- The 32-bit words of `(p − 1) / q` for the exponentiation. -/
  e : Nat
  /-- The hash function, by its compression function, and its initial value. -/
  H : Impl.Pbkdf2.Md.X86.Hash
  iv : List (BitVec 32)
  qName : String
  qCode : Prog isa
  pName : String
  pCode : Prog isa
  checkName : String
  checkCode : Prog isa

namespace Geo
variable (g : Geo)

/-- `(L − 1) / N`. -/
def count : Nat := (8 * g.pLen - 1) / (8 * g.qLen)

/-- The 64-bit words of p. -/
def n64 : Nat := g.pLen / 8

/-- The 32-bit words of p. -/
def n32 : Nat := g.pLen / 4

/-- The seed into the block. -/
def seedIn : Prog isa := copyTo [.mov .esi (.mem (sc fSeed))] (sState + g.H.N) g.qLen

/-- q from the seed: hashed, shaped into p||q||g, and tested. -/
def qPart : Prog isa := seqs [
  g.seedIn,
  hash g.H g.iv g.qLen (sPk + g.pLen),
  .block (orByte (sPk + g.pLen) 0x80 ++ orByte (sPk + g.pLen + g.qLen - 1) 1),
  copyS (sPP + (ProbablePrime.layout (8 * g.qLen)).candidate) (sPk + g.pLen) g.qLen,
  test g.qName g.qCode]

/-- The hash of `seed + offset + j`, into its place in `X`. -/
def pHash (j : Nat) : Prog isa := seqs [
  g.seedIn,
  .block (scr .edx (sState + g.H.N + g.qLen - 1) ++
    [.mov .ecx (.mem (sc fOffset)), .alu .add .ecx (.imm (BitVec.ofNat 32 j))]),
  addBE g.qLen,
  hash g.H g.iv g.qLen (sX + g.pLen - (j + 1) * g.qLen)]

/-- `X`: the hashes, the top bit set, and the low bit, which the reduction
modulo `2 q` discards, as q's shaping does. -/
def pX : Prog isa :=
  seqs ((List.range (g.count + 1)).map g.pHash ++ [.block (orByte sX 0x80 ++ orByte (sX + g.pLen - 1) 1)])

/-- A counter's candidate: `fP` := 0 if the witnesses ran out, 1 if it is a
probable prime, else as it was. -/
def pAttempt : Prog isa := seqs [
  g.pX, pArith g.pLen g.qLen,
  .block [.movzx8 .eax (sc sPk), .alu .and .eax (.imm 0x80), .alu .cmp .eax (.imm 0)],
  .ite .e (.block [])
    (seqs [copyS (sPP + (ProbablePrime.layout (8 * g.pLen)).candidate) sPk g.pLen, test g.pName g.pCode,
      .block (cmpF fRes 0), .ite .e (.block (stImm fP 0))
        (seqs [.block (cmpF fRes 1), .ite .e (.block (stImm fP 1)) (.block [])])])]

/-- The next counter: 2 when the `4 L` are done. -/
def pAdvance : List Instr :=
  [.mov .eax (.mem (sc fCounter)), .alu .add .eax (.imm 1), .store (sc fCounter) .eax,
    .mov .ecx (.mem (sc fOffset)), .alu .add .ecx (.imm (BitVec.ofNat 32 (g.count + 1))),
    .store (sc fOffset) .ecx, .alu .cmp .eax (.imm (BitVec.ofNat 32 (32 * g.pLen)))]

/-- p: `fP` := 0, 1 or 2 (none found). -/
def pPart : Prog isa := seqs [
  .block (stImm fCounter 0 ++ stImm fOffset 1 ++ stImm fP 4),
  .loop (seqs [g.pAttempt, .block (cmpF fP 4),
    .ite .e (seqs [.block g.pAdvance, .ite .e (.block (stImm fP 2)) (.block [])]) (.block []),
    .block (cmpF fP 4)]) .e]

/-- An `h`: `fG` := 1 with `g` in p||q||g if `1 < h < p − 1` and `g > 1`. -/
def gStep : Prog isa := seqs [
  .block [.mov .esi (.mem (sc fH)), .mov .ecx (.imm (BitVec.ofNat 32 g.pLen))],
  loadBE g.n64 aH,
  chainW .sbb g.n32 aTmp aOne aH, .block [.store (sc fLo) .ecx],
  chainW .sbb g.n32 aTmp aH aPm1,
  .block [.alu .and .ecx (.mem (sc fLo)), .alu .cmp .ecx (.imm 0)],
  .ite .e (.block [])
    (seqs [.block [.mov .ecx (.imm 0)], selectsW g.n32 aP aP (Pow.layout g.n64 g.e).modulus,
      .block [.mov .ecx (.imm 0)], selectsW g.n32 aH aH (Pow.layout g.n64 g.e).base,
      .block [.mov .ecx (.imm 0)], selectsW g.e aE aE (Pow.layout g.n64 g.e).exponent,
      Pow.call g.n64 g.e,
      chainW .sbb g.n32 aTmp aOne (Pow.layout g.n64 g.e).result,
      .block [.alu .cmp .ecx (.imm 0)],
      .ite .e (.block [])
        (seqs [storeS (Pow.layout g.n64 g.e).result (sPk + g.pLen + g.qLen) g.pLen,
          .block (stImm fG 1)])])]

/-- The window of `h` candidates: `rand` after the octets read (`fHs`), and
at most `generatorAttempts` candidates' octets of it (`fHsLen`). -/
def gWindow : Prog isa :=
  .seq (.block [.mov .ecx (.mem (sc fUsed)), .mov .eax (.mem (sc fWit)), .alu .add .eax (.reg .ecx),
      .store (sc fHs) .eax, .mov .eax (.mem (sc fWitLen)), .alu .sub .eax (.reg .ecx), .store (sc fHsLen) .eax,
      .alu .cmp .eax (.imm (BitVec.ofNat 32 (128 * g.pLen)))])
    (.ite .b (.block []) (.block (stImm fHsLen (128 * g.pLen))))

/-- g over the window: `fG` := 1, or 2 if no `h` gives one, with at least
`p_len` octets left before each. -/
def gPart : Prog isa := seqs [
  .block [.mov .eax (.mem (sc fHs)), .store (sc fH) .eax, .mov .eax (.mem (sc fHsLen)),
    .store (sc fHLeft) .eax, .mov .eax (.imm 4), .store (sc fG) .eax],
  .loop (seqs [.block (cmpF fHLeft g.pLen),
    .ite .b (.block (stImm fG 2))
      (seqs [g.gStep, .block [.mov .eax (.mem (sc fH)), .alu .add .eax (.imm (BitVec.ofNat 32 g.pLen)),
        .store (sc fH) .eax, .mov .eax (.mem (sc fHLeft)), .alu .sub .eax (.imm (BitVec.ofNat 32 g.pLen)),
        .store (sc fHLeft) .eax]]),
    .block (cmpF fG 4)]) .e]

/-- The candidates the search for g read count as read. -/
def gUsed : List Instr :=
  [.mov .eax (.mem (sc fH)), .mov .ecx (.mem (sc fWit)), .alu .sub .eax (.reg .ecx), .store (sc fUsed) .eax]

/-- Without a g, a window shorter than `generatorAttempts` candidates ran out. -/
def gShort : Prog isa :=
  .seq (.block (cmpF fHsLen (128 * g.pLen))) (.ite .b (.block (stImm fStatus 2)) (.block []))

/-- A seed: `fStatus` := 2 if `rand` ran out, 1 if the domain passes, else as
it was (0). -/
def attempt : Prog isa := seqs [
  g.qPart, .block (cmpF fRes 0),
  .ite .e (.block (stImm fStatus 2))
    (seqs [.block (cmpF fRes 1),
      .ite .e
        (seqs [g.pPart, .block (cmpF fP 0),
          .ite .e (.block (stImm fStatus 2))
            (seqs [.block (cmpF fP 1),
              .ite .e (seqs [g.gWindow, g.gPart, .block gUsed, .block (cmpF fG 1),
                  .ite .e (check g.pLen g.qLen (16 * g.pLen) g.checkName g.checkCode) g.gShort])
                (.block [])])])
        (.block [])])]

/-- `eax` := the octets of `rand` after the cursor. -/
def avail : List Instr := [.mov .eax (.mem (sc fWitLen)), .mov .ecx (.mem (sc fC)), .alu .sub .eax (.reg .ecx)]

/-- The next seed starts at the cursor, its witnesses after it. -/
def seedStart : List Instr :=
  [.mov .ecx (.mem (sc fC)), .mov .eax (.mem (sc fWit)), .alu .add .eax (.reg .ecx), .store (sc fSeed) .eax,
    .alu .add .ecx (.imm (BitVec.ofNat 32 g.qLen)), .store (sc fUsed) .ecx]

/-- A rejected seed: the cursor past it, one seed fewer left. -/
def rejected : List Instr :=
  [.mov .eax (.mem (sc fUsed)), .store (sc fC) .eax, .mov .eax (.mem (sc fSeedLeft)), .alu .sub .eax (.imm 1),
    .store (sc fSeedLeft) .eax]

/-- The seeds, one at a time, until a domain passes (`fStatus` = 1), `rand`
runs out (2) or the seeds do (3). -/
def search : Prog isa :=
  .loop (seqs [.block (cmpF fSeedLeft 0),
    .ite .e (.block (stImm fStatus 3))
      (seqs [.block (avail ++ [.alu .cmp .eax (.imm (BitVec.ofNat 32 g.qLen))]),
        .ite .b (.block (stImm fStatus 2))
          (seqs [.block g.seedStart, g.attempt, .block (cmpF fStatus 0),
            .ite .e (.block rejected) (.block [])])]),
    .block (cmpF fStatus 0)]) .e

/-- The entropy budget, `32769 p_len`. -/
def budget : Nat := 32769 * g.pLen

/-- `out` := p||q||g, for status 1, or zeros. -/
def outPart : Prog isa := seqs [
  .block (cmpF fStatus 1),
  .ite .e
    (seqs [.block ([.mov .ebx (.mem (sc fOut))] ++ scr .esi sPk ++
        [.mov .ecx (.imm (BitVec.ofNat 32 (2 * g.pLen + g.qLen)))]), copyBytes])
    (seqs [.block [.mov .esi (.mem (sc fOut)), .mov .ecx (.imm (BitVec.ofNat 32 (2 * g.pLen + g.qLen))),
        .mov .eax (.imm 0)],
      .loop (.block PublicFn.clearStep) .ne])]

/-- `state[0]` := `edx`, `state[3]` := `ecx`, `used` := the word at `u` (each
with its high half zero), and `eax` := `v`. Each pointer is loaded in a block
of its own, before the block that stores through it. -/
def results (u v : Nat) : Prog isa := seqs [
  .block [.mov .ebx (.mem (sc fStP))],
  .block [.store (at_ .ebx 0) .edx, .store (at_ .ebx 24) .ecx, .mov .eax (.imm 0), .store (at_ .ebx 4) .eax,
    .store (at_ .ebx 28) .eax, .mov .ebx (.mem (sc fUsedP))],
  .block [.store (at_ .ebx 4) .eax, .mov .eax (.mem (sc u)), .store (at_ .ebx 0) .eax,
    .mov .eax (.imm (BitVec.ofNat 32 v))]]

/-- Parameters: nothing left, no request, the octets read used. -/
def accepted : Prog isa := .seq (.block [.mov .edx (.imm 0), .mov .ecx (.imm 0)]) (results fUsed 1)

/-- Exhausted: nothing left, no request, nothing past the cursor used. -/
def exhausted : Prog isa := .seq (.block [.mov .edx (.imm 0), .mov .ecx (.imm 0)]) (results fC 3)

/-- `rand` ran out at the cursor: exhausted if the octets left reach the
budget; else the seeds left, and the next tape's length, twice the octets
left, at least `256 p_len` and at most the budget. -/
def ranOut : Prog isa := seqs [
  .block (avail ++ [.alu .cmp .eax (.imm (BitVec.ofNat 32 g.budget))]),
  .ite .b
    (seqs [.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 (256 * g.pLen)))],
      .ite .b (.block [.mov .eax (.imm (BitVec.ofNat 32 (256 * g.pLen)))]) (.block []),
      .block [.alu .add .eax (.reg .eax), .alu .cmp .eax (.imm (BitVec.ofNat 32 g.budget))],
      .ite .b (.block []) (.block [.mov .eax (.imm (BitVec.ofNat 32 g.budget))]),
      .block [.mov .ecx (.reg .eax), .mov .edx (.mem (sc fSeedLeft))],
      results fC 0])
    exhausted]

/-- The result: `out`, then `used` and `state`, and the status. -/
def finish : Prog isa := seqs [
  g.outPart,
  .block (cmpF fStatus 1),
  .ite .e accepted
    (seqs [.block (cmpF fStatus 2), .ite .e g.ranOut exhausted])]

def generate : Prog isa := .seq g.search g.finish

end Geo

/-! ## Entry -/

/-- Argument `i` into the state word at `o`. -/
def copyArg (i o : Nat) : List Instr := [.mov .eax (.mem (Compact.arg i)), .store (sc o) .eax]

/-- `edi` := `scratch`; `out`, `used`, `rand` and its length, and `state`
saved; the cursor at 0, searching. -/
def entry : List Instr :=
  [.mov .edi (.mem (Compact.arg 5))] ++ copyArg 0 fOut ++ copyArg 2 fUsedP ++ copyArg 3 fWit ++
    copyArg 4 fWitLen ++ copyArg 7 fStP ++ stImm fC 0 ++ stImm fStatus 0

/-- `state[0]` (the seeds left) into `fSeedLeft`, and the three geometries, by
the modulus's width, `state[1]`. The pointer to `state` is loaded in a block
of its own, before the block that reads through it. -/
def dispatch (g1 g2 g3 : Geo) : Prog isa := seqs [
  .block [.mov .ebx (.mem (Compact.arg 7))],
  .block [.mov .eax (.mem (at_ .ebx 0)), .store (sc fSeedLeft) .eax, .mov .eax (.mem (at_ .ebx 8)),
    .alu .cmp .eax (.imm 128)],
  .ite .e g1.generate (.seq (.block [.alu .cmp .eax (.imm 0x100)]) (.ite .e g2.generate g3.generate))]

/-- `vg_dsa_parameter_search`. -/
def code (g1 g2 g3 : Geo) : Prog isa :=
  .frame (.push [.ebx, .ebp, .esi, .edi])
    (.seq (.seq (.block entry) (dispatch g1 g2 g3)) (.block Compact.restoreRegs)) (.pop .ebx 4)

/-! ## `vg_dsa_parameter_search_init` -/

/-- `[ecx + 4 j] := eax`: word `j` of `state`, 32 bits of it. -/
def st (j : Nat) : Instr := .store (at_ .ecx (4 * j)) .eax

/-- `state` := zeros, and 0. -/
def initZeros : List Instr :=
  [.mov .ecx (.mem (PublicFn.argument 0)), .mov .eax (.imm 0), st 0, st 1, st 2, st 3, st 4, st 5, st 6, st 7]

/-- `state` := `[4096, L, 32769 L, 512 L]`, high halves zero, and 1. -/
def initWords (L : Nat) : List Instr :=
  [.mov .ecx (.mem (PublicFn.argument 0)), .mov .eax (.imm 4096), st 0, .mov .eax (.imm (BitVec.ofNat 32 L)), st 2,
    .mov .eax (.imm (BitVec.ofNat 32 (32769 * L))), st 4, .mov .eax (.imm (BitVec.ofNat 32 (512 * L))), st 6,
    .mov .eax (.imm 0), st 1, st 3, st 5, st 7, .mov .eax (.imm 1)]

/-- `vg_dsa_parameter_search_init(state, p_len)`. -/
def init : Prog isa :=
  .seq (.block [.mov .edx (.mem (PublicFn.argument 1)), .alu .cmp .edx (.imm 128)])
    (.ite .e (.block (initWords 128))
      (.seq (.block [.alu .cmp .edx (.imm 256)])
        (.ite .e (.block (initWords 256))
          (.seq (.block [.alu .cmp .edx (.imm 384)])
            (.ite .e (.block (initWords 384)) (.block initZeros))))))

end VG.Impl.Dsa.X86.Generation
