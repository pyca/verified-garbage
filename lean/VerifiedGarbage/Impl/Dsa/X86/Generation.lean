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
# DSA parameter generation on baseline i686 (cdecl)

`vg_dsa_generate_parameters(out, out_len, p_len, q_len, seeds, seeds_len, hs,
hs_len, witnesses, witnesses_len, scratch, scratch_len)`, every argument on
the stack. The callee-saved registers are pushed, and `edi` holds `scratch`
throughout: every function called keeps it, and both the exponentiation's
working space and the division's arrays are at fixed offsets from it.
`scratch` holds, at fixed offsets: the exponentiation's working space
(from byte 0, `Pow.layout`), the search's state (`f…`), the hash value and
block and the compression function's scratch space, `X`, p||q||g (`sPk`),
the division's and the comparisons' arrays (`arr`), the probable-prime
test's working space (`sPP`) and `vg_dsa_check_parameters`'s scratch
(`sChk`).

For each seed of the `seeds` tape (FIPS 186-4 A.1.1.2):

1. q: the seed's hash (SHA-1 for a 160-bit q, else SHA-256: one block, by
   the compression function), its top and low bits set, into p||q||g, and
   tested by `vg_dsa_probable_prime_{N}` with the witnesses left.
2. p: for each of the `4 L` counters, the hashes of `seed + offset + j`
   (big-endian, `seedlen` bytes) for `j ≤ count`, assembled into `X` with
   its top bit set; `X` divided by `2 q` (RSA's division), `p − 1 = X − (X
   mod 2 q)` and `(p − 1) / q = 2 ⌊X / 2 q⌋`; `p` into p||q||g, and if it has
   `L` bits, tested by `vg_dsa_probable_prime_{L}`.
3. g: for each `h` of the `hs` tape with `1 < h < p − 1`, `g = h^((p−1)/q)
   mod p` by `vg_dsa_pow_{n}_{e}`, until `g > 1`, into p||q||g.
4. p||q||g checked by `vg_dsa_check_parameters`.

The first domain that passes is copied to `out`, with status 1; otherwise
`out` is zeroed, with status 0: no seed left, or `witnesses` ran out. Every
branch and loop count depends on the lengths and the three tapes, which the
contract makes public, and on nothing else.
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
def fHs : Nat := hdr + 12
def fHsLen : Nat := hdr + 16
def fWit : Nat := hdr + 20
def fWitLen : Nat := hdr + 24
/-- The octets of `witnesses` read so far. -/
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
def fHi : Nat := hdr + 76

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
witnesses left: its result into `fRes`, and the octets it read added to
`fUsed` unless it ran out. -/
def test (name : String) (callee : Prog isa) : Prog isa := seqs [
  .block (scr .eax sPP ++ [.mov .ecx (.imm (BitVec.ofNat 32 ppWords)),
    .mov .edx (.mem (sc fWit)), .alu .add .edx (.mem (sc fUsed)),
    .mov .ebx (.mem (sc fWitLen)), .alu .sub .ebx (.mem (sc fUsed))] ++ scr .ebp fUsedOut),
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

/-- `X`: the hashes, the top bit set. -/
def pX : Prog isa :=
  seqs ((List.range (g.count + 1)).map g.pHash ++ [.block (orByte sX 0x80)])

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

/-- g: `fG` := 1, or 2 if no `h` gives one. -/
def gPart : Prog isa := seqs [
  .block [.mov .eax (.mem (sc fHs)), .store (sc fH) .eax, .mov .eax (.mem (sc fHsLen)),
    .store (sc fHLeft) .eax, .mov .eax (.imm 4), .store (sc fG) .eax],
  .loop (seqs [.block (cmpF fHLeft 0),
    .ite .e (.block (stImm fG 2))
      (seqs [g.gStep, .block [.mov .eax (.mem (sc fH)), .alu .add .eax (.imm (BitVec.ofNat 32 g.pLen)),
        .store (sc fH) .eax, .mov .eax (.mem (sc fHLeft)), .alu .sub .eax (.imm (BitVec.ofNat 32 g.pLen)),
        .store (sc fHLeft) .eax]]),
    .block (cmpF fG 4)]) .e]

/-- A seed. -/
def attempt : Prog isa := seqs [
  g.qPart, .block (cmpF fRes 0),
  .ite .e (.block (stImm fStatus 2))
    (seqs [.block (cmpF fRes 1),
      .ite .e
        (seqs [g.pPart, .block (cmpF fP 0),
          .ite .e (.block (stImm fStatus 2))
            (seqs [.block (cmpF fP 1),
              .ite .e (seqs [g.gPart, .block (cmpF fG 1),
                  .ite .e (check g.pLen g.qLen (16 * g.pLen) g.checkName g.checkCode) (.block [])])
                (.block [])])])
        (.block [])])]

/-- The seeds, one at a time, until a domain passes or none is left. -/
def search : Prog isa :=
  .loop (seqs [.block (cmpF fSeedLeft 0),
    .ite .e (.block (stImm fStatus 2))
      (seqs [g.attempt, .block [.mov .eax (.mem (sc fSeed)), .alu .add .eax (.imm (BitVec.ofNat 32 g.qLen)),
        .store (sc fSeed) .eax, .mov .eax (.mem (sc fSeedLeft)), .alu .sub .eax (.imm (BitVec.ofNat 32 g.qLen)),
        .store (sc fSeedLeft) .eax]]),
    .block (cmpF fStatus 0)]) .e

/-- The result: p||q||g to `out` and 1, or zeros and 0. -/
def finish : Prog isa := seqs [
  .block (cmpF fStatus 1),
  .ite .e
    (seqs [.block ([.mov .ebx (.mem (sc fOut))] ++ scr .esi sPk ++
        [.mov .ecx (.imm (BitVec.ofNat 32 (2 * g.pLen + g.qLen)))]), copyBytes, .block [.mov .eax (.imm 1)]])
    (seqs [.block [.mov .esi (.mem (sc fOut)), .mov .ecx (.imm (BitVec.ofNat 32 (2 * g.pLen + g.qLen))),
        .mov .eax (.imm 0)],
      .loop (.block PublicFn.clearStep) .ne, .block [.mov .eax (.imm 0)]])]

def generate : Prog isa := .seq g.search g.finish

end Geo

/-! ## Entry -/

/-- Argument `i` into the state word at `o`. -/
def copyArg (i o : Nat) : List Instr := [.mov .eax (.mem (Compact.arg i)), .store (sc o) .eax]

/-- `edi` := `scratch`; `out` and the tapes' pointers and lengths saved;
nothing read, searching. -/
def entry : List Instr :=
  [.mov .edi (.mem (Compact.arg 10))] ++ copyArg 0 fOut ++ copyArg 4 fSeed ++ copyArg 5 fSeedLeft ++
    copyArg 6 fHs ++ copyArg 7 fHsLen ++ copyArg 8 fWit ++ copyArg 9 fWitLen ++ stImm fUsed 0 ++ stImm fStatus 0

/-- The three geometries, by `p_len`. -/
def dispatch (g1 g2 g3 : Geo) : Prog isa :=
  .seq (.block [.mov .eax (.mem (Compact.arg 2)), .alu .cmp .eax (.imm 128)])
    (.ite .e g1.generate
      (.seq (.block [.alu .cmp .eax (.imm 0x100)]) (.ite .e g2.generate g3.generate)))

def code (g1 g2 g3 : Geo) : Prog isa :=
  .frame (.push [.ebx, .ebp, .esi, .edi])
    (.seq (.block entry) (.seq (dispatch g1 g2 g3) (.block Compact.restoreRegs))) (.pop .ebx 4)

end VG.Impl.Dsa.X86.Generation
