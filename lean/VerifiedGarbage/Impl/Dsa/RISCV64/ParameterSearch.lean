module

public import VerifiedGarbage.Impl.Rsa.RISCV64.Div
public import VerifiedGarbage.Impl.Dsa.RISCV64.Common
public import VerifiedGarbage.Impl.MdStream.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Loops
public import VerifiedGarbage.Impl.Sha1.RISCV64
public import VerifiedGarbage.Impl.Sha256.RISCV64
public import VerifiedGarbage.Spec.Sha1
public import VerifiedGarbage.Spec.Sha256

/-!
# DSA parameter generation over refillable random tapes on RISC-V

`vg_dsa_parameter_search(out = a0, out_len = a1, used = a2, rand = a3,
rand_len = a4, scratch = a5, scratch_len = a6, state = a7)` and
`vg_dsa_parameter_search_init(state = a0, p_len = a1)`
(`Spec/Dsa/ParameterSearch.lean`).

The search reads the seeds, the witnesses of their tests and the
generator's `h` candidates from one tape, `rand`, in the order a seed uses
them, from a cursor (`fUsed`, the octets consumed). Each seed (FIPS 186-4
A.1.1.2 and A.2.1), at the cursor, is as on PPC64LE
(`Impl/Dsa/PPC64LE/Generation.lean`):

1. q: the seed's hash (SHA-1 for a 160-bit q, else SHA-256: one block, by
   the compression function), its top and low bits set, tested by
   `vg_dsa_probable_prime_{N}` with witnesses from the cursor.
2. p: for each of the `4 L` counters, the hashes of `seed + offset + j`
   (big-endian, `seedlen` octets) for `j ≤ count`, assembled into `X` with
   its top bit set; `p = X − (X mod 2q) + 1`, by division of `X` by `q` in
   the RSA key working space (`Impl/Rsa/RISCV64/KeyWs.lean`, `divL`: the
   quotient's parity gives `X mod 2q`, and the quotient with its low bit
   cleared is `(p − 1) / q`); if `p` has `L` bits, tested by
   `vg_dsa_probable_prime_{L}`.
3. g: the window of the tape at the cursor, its first `generatorAttempts`
   candidates of `p_len` octets (fewer if the tape is shorter): for each
   `h` with `1 < h < p − 1`, `g = h^((p−1)/q) mod p` by `ModExp.powWin` in a
   working space of the DSA functions' layout (`Impl/Dsa/RISCV64/Common.lean`),
   until `1 < g` (`elemRange`); the candidates read count as consumed.
4. p||q||g checked by `vg_dsa_check_parameters`.

A test that ran out, or a window cut short by the tape's end without a
generator, ends the seed with status 0 (the tape ran out); parameters that
pass end it with status 1; any other outcome rejects the seed (status 2).

The controller (`search`) runs seeds while they are rejected, counting them
against the seeds the search may still reject (`fLeft`); it stops with none
left (status 3, exhausted), with a tape too short for the next seed or a
seed that ran out (status 0), or with parameters (status 1). `finish` then
writes `used`, the state's words 0 and 3 and `out`, and returns the
protocol's status (`Spec.Entropy.Outcome.status`): for status 0, the tape
from the seed's start exhausts the search if it holds the whole entropy
budget, and otherwise the next tape's length is `Spec.Dsa.parameterRequest`.

`scratch` (`S`) holds, from byte 0, the search's state (`f…`), our
caller's callee-saved registers and our return address, then small buffers
(`s…`), the packed parameters (at `sPacked`), the P space (at `pB`), the key
working space (at `kB p_len`) and the working space of the functions we call
(at `wB p_len`). `S` stays in `s6`, which no code here or that we call
writes: every value of the search is loaded from and stored to `S`'s header,
so that it survives the calls and the arithmetic, which use every other
register. Every value is public: the code branches on the tape's contents.
-/

@[expose] public section
namespace VG.Impl.Dsa.RISCV64.ParameterSearch
open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Keys
open VG.Impl.Bignum.RISCV64 (countLoop)

/-! ## The state -/

def fOut : Nat := 0
/-- The seed's address, in `rand`. -/
def fSeed : Nat := 8
/-- The seeds the search may still reject. -/
def fLeft : Nat := 16
/-- The octets of `rand` consumed: the cursor. -/
def fUsed : Nat := 24
def fCounter : Nat := 32
def fOffset : Nat := 40
/-- The next `h` candidate's address, and the octets left in the window. -/
def fH : Nat := 48
def fHLeft : Nat := 56
/-- The seed's status: 0 the tape ran out, 1 parameters, 2 rejected; and the
search's, 3 exhausted. -/
def fStatus : Nat := 64
/-- `rand` and `rand_len`. -/
def fWit : Nat := 72
def fWitLen : Nat := 80
/-- A test's result, the p search's and the generator search's state. -/
def fRes : Nat := 88
def fP : Nat := 96
def fG : Nat := 104
/-- The octets a test read, a 64-bit word. -/
def fUsedOut : Nat := 112
def fRA : Nat := 120
/-- The window's start, and whether it held `generatorAttempts` candidates. -/
def fHStart : Nat := 128
def fFull : Nat := 136
/-- The cursor at the seed's start. -/
def fStart : Nat := 144
/-- `used`, `state` and `scratch_len`. -/
def fUsedArg : Nat := 152
def fState : Nat := 160
def fScrLen : Nat := 168
/-- Our caller's `s0`–`s11`, `s6` (which keeps `S`) last. -/
def fSave : Nat := 184

/-- The callee-saved registers, saved at `fSave + 8 i`. -/
def saved : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s7, .s8, .s9, .s10, .s11, .s6]

/-- `r :=` the state word at `o`. -/
def ld (r : Reg) (o : Nat) : Instr := .load .d r .s6 o

/-- The state word at `o` := `r`. -/
def st (r : Reg) (o : Nat) : Instr := .store .d r .s6 o

/-- The state word at `o` := `v`, through `t2`. -/
def stImm (o v : Nat) : List Instr := [.li .t2 v, st .t2 o]

/-- `t2 :=` the state word at `o` minus `v`, for a test against zero. -/
def cmpF (o v : Nat) : List Instr := [ld .t2 o, .addi .t2 .t2 (-(v : Int))]

/-! ## The scratch -/

def sMsg : Nat := 320
def sState : Nat := 384
/-- The compression function's scratch, 80 octets, past the hash value's 32. -/
def sCS : Nat := 416
def sQ : Nat := 512
/-- `X`: 32 octets above `sQ`'s end, which the last hash of a 1024-bit `X`
writes 12 of. -/
def sX : Nat := 576
def sPBE : Nat := 960
def sE : Nat := 1344
def sG : Nat := 1728
/-- The offsets from here on are multiples of 4096 (`scrB`). -/
def sPacked : Nat := 4096

/-- The P space. -/
def pB : Nat := 8192

/-- The P space's bytes: its header and 28 arrays of `p_len / 8 + 2` words. -/
def pBytes (pLen : Nat) : Nat := 256 + 28 * (pLen + 16)

/-- The key working space, past the P space, at a multiple of 4096. -/
def kB (pLen : Nat) : Nat := pB + 4096 * ((pBytes pLen + 4095) / 4096)

/-- The key working space's arrays. -/
def aQt : Nat := 0
def aRm : Nat := 1
def aDv : Nat := 2
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
def slOdd : Nat := 160
def slLo : Nat := 168
def slHi : Nat := 176

/-- The working space of the functions we call, past the key working space,
at a multiple of 4096. -/
def wB (pLen : Nat) : Nat := kB pLen + 4096 * ((hdr + nArrs * (pLen + 16) + 4095) / 4096)

/-- `rd :=` the words of `scratch` the functions we call may use,
`scratch_len − wB / 8`, through `t3`. -/
def wsLen (rd : Reg) (pLen : Nat) : List Instr :=
  [ld rd fScrLen, .lui .t3 (BitVec.ofNat 20 (wB pLen / 4096)), .shift .srl .d .t3 .t3 3, .sub rd rd .t3]

/-- `rd := S + o`, for `o < 2048`. -/
def scr (rd : Reg) (o : Nat) : Instr := .addi rd .s6 o

/-- `rd := S + o`, for `o` a multiple of 4096 below `2³¹`. -/
def scrB (rd : Reg) (o : Nat) : List Instr := [.lui rd (BitVec.ofNat 20 (o / 4096)), .add rd rd .s6]

/-! ## Bytes -/

/-- `n > 0` octets copied: `src` sets `a0` to the source, then `dst` sets
`a1` to the destination. -/
def copyN (src dst : List Instr) (n : Nat) : Prog isa :=
  .seq (.block (src ++ dst ++ [.li .a2 n])) (Impl.Words.RISCV64.copyLoop .a3 .a0 .a1 .a2)

/-- From `S + src` to `S + dst`, both below 2048. -/
def copyS (dst src n : Nat) : Prog isa := copyN [scr .a0 src] [scr .a1 dst] n

/-- An octet of the big-endian addition: `[a0] + a2`, its carry and the
addend's higher octets on in `a2`. -/
def addStep : List Instr :=
  [.load .b .a1 .a0 0, .add .a1 .a1 .a2, .store .b .a1 .a0 0, .shift .srl .d .a2 .a1 8, .addi .a0 .a0 (-1)]

/-- `offset + j` (the state word `fOffset` plus `j`) added to the `n`-octet
seed at `sMsg`, modulo `2^(8 n)`. -/
def seedAdd (n j : Nat) : Prog isa :=
  .seq (.block [scr .a0 (sMsg + n - 1), ld .a2 fOffset, .addi .a2 .a2 j, .li .a3 n])
    (countLoop .a3 addStep)

/-! ## Hashes -/

/-- A hash function by its compression function. -/
structure Hash where
  /-- The words of the hash value. -/
  k : Nat
  iv : List (BitVec 32)
  name : String
  code : Prog isa

/-- SHA-1. -/
def sha1 : Hash := ⟨5, Spec.Sha1.H0.toList, "vg_sha1_compress", VG.Impl.Sha1.RISCV64.compress⟩

/-- SHA-256. -/
def sha256 : Hash := ⟨8, Spec.Sha256.H0.toList, "vg_sha256_compress", VG.Impl.Sha256.RISCV64.compress⟩

/-- The block at `sMsg` hashed into `S + dst`: the initial hash value at
`sState` (`MdStream.RISCV64.initWords`), the block compressed into it, and
its words big-endian at `dst` (`MdStream.RISCV64.outBE`, from `s1` to `s3`). -/
def hash (G : Hash) (dst : Nat) : Prog isa := seqs [
  .block [scr .a0 sState], VG.Impl.MdStream.RISCV64.initWords G.iv,
  .block [scr .a0 sState, scr .a1 sMsg, .li .a2 1, scr .a3 sCS],
  .call G.name G.code,
  .block ([scr .s1 sState, scr .s3 dst] ++ VG.Impl.MdStream.RISCV64.outBE G.k)]

/-- The block's padding after a message of `n < 56` octets. -/
def padInit (n : Nat) : List Instr :=
  [.li .t2 0] ++ (List.range 8).map (fun i => st .t2 (sMsg + 8 * i)) ++
    [.li .t2 0x80, .store .b .t2 .s6 (sMsg + n), .li .t2 ((8 * n) / 256), .store .b .t2 .s6 (sMsg + 62),
      .li .t2 ((8 * n) % 256), .store .b .t2 .s6 (sMsg + 63)]

/-! ## Tests -/

/-- A probable-prime test of the candidate at byte 0 of the working space
`wB`, copied there from `S + src` (`n` octets), with the tape from the cursor
(from `rand` itself when nothing is left: an empty range within the tape):
its result, zero-extended, into `fRes`, and the octets it read added to
`fUsed` unless it ran out. -/
def test (pLen src n : Nat) (name : String) (callee : Prog isa) : Prog isa := seqs [
  copyN [scr .a0 src] (scrB .a1 (wB pLen) ++ [.addi .a1 .a1 0]) n,
  .block (scrB .a0 (wB pLen) ++ wsLen .a1 pLen ++ [ld .t2 fUsed, ld .a2 fWit, ld .a3 fWitLen,
    .add .a2 .a2 .t2, .sub .a3 .a3 .t2, scr .a4 fUsedOut]),
  .ite (.zero .a3) (.block [ld .a2 fWit]) (.block []),
  .call name callee,
  .block [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32, st .a0 fRes],
  .ite (.zero .a0) (.block [])
    (.block [ld .t3 fUsedOut, ld .t4 fUsed, .add .t4 .t4 .t3, st .t4 fUsed])]

/-! ## Arithmetic, in the key working space -/

/-- `s11`, `s10` and `s9`: the key working space, its stride and its words. -/
def ksRegs (pLen : Nat) : List Instr := scrB .s11 (kB pLen) ++ [.li .s10 (pLen + 16), .li .s9 (pLen / 8)]

/-- Every array zeroed, and 1 set. -/
def ksSetup : Prog isa := .seq (zeroArrays nArrs) (.block (setOne aOne))

/-- Array `j` := the `n` big-endian octets at `S + o`. -/
def loadS (j o n : Nat) : Prog isa := .seq (.block [scr .a0 o, .li .a1 n]) (load j .a0 .a1)

/-- `S + o` := `[j]`'s low `n` octets, big-endian. -/
def storeS (j o n : Nat) : Prog isa := .seq (.block [scr .a0 o, .li .a1 n, .li .t4 (-1)]) (storeBytes j .a0 .a1)

/-- The slot `d` := `[a] < [b]`. -/
def ltS (d a b : Nat) : List (Prog isa) := [sub3 aTmp a b, .block (stBorrow d)]

/-- The octets of `(p − 1) / q` kept: `8 (p_len − q_len) + 1` bits. -/
def eBytes (pLen qLen : Nat) : Nat := pLen - qLen + 1

/-- `p` and `(p − 1) / q` from `X` at `sX` and `q` at `sQ`: `p − 1` in array
`aPm1`, `p` in array `aP` and to `sPBE` (big-endian), `(p − 1) / q` in
array `aE` and to `sE`. -/
def pArith (pLen qLen : Nat) : Prog isa := seqs [
  seqs [.block (ksRegs pLen), ksSetup, loadS aQt sX pLen, loadS aX sX pLen, loadS aDv sQ qLen],
  .seq (.block [.li .a1 qLen]) (VG.Impl.Rsa.RISCV64.Div.divL aQt aRm aDv .a1),
  seqs [sub3 aT aX aRm, .block (bitOf slOdd aQt), sel aS aZero aDv slOdd, sub3 aPm1 aT aS],
  seqs [VG.Impl.Rsa.RISCV64.Keys.copy aP aPm1, .block (orOne aP), VG.Impl.Rsa.RISCV64.Keys.copy aE aQt, .block (clrLow aE), storeS aP sPBE pLen,
    storeS aE sE (eBytes pLen qLen)]]

/-! ## The power, in the P space -/

/-- Into the P space at `pB`, with `w = p_len / 8`. -/
def enterP (pLen : Nat) : List Instr :=
  scrB .a7 pB ++ [.addi .a7 .a7 VG.Impl.Bignum.hdrBytes, .li .t0 (pLen / 8), .li .s5 (pLen + 16)]

/-- Array 4's word `w` := 0, as `elemRange` reads it: `a7 + 5 s5 − 16`. -/
def zeroTop4 : List Instr :=
  VG.Impl.Bignum.RISCV64.PublicChecked.base .t3 5 ++ [.addi .t3 .t3 (-16), .li .s0 0, .store .d .s0 .t3 0]

/-- p into array 0 of the P space, `−p⁻¹ mod 2⁶⁴` into `t1`, `R² mod p` into
arrays 1 and 24 (`rr`). -/
def powA (pLen : Nat) : Prog isa := seqs [
  .block (enterP pLen ++ [scr .s7 sPBE, .li .s8 pLen]), VG.Impl.Dsa.RISCV64.loadArr 0,
  .block VG.Impl.Bignum.RISCV64.Precompute.minv, VG.Impl.Dsa.RISCV64.rr]

/-- `h` (at `s7`, `s8` octets) into array 4, its power over `sE`, array 4's
word `w` zeroed, and the range check. -/
def powC (pLen qLen : Nat) : Prog isa := seqs [
  VG.Impl.Dsa.RISCV64.loadArr 4, VG.Impl.Dsa.RISCV64.copy 1 24,
  .block [scr .s9 sE, .li .s10 (eBytes pLen qLen)], VG.Impl.Bignum.RISCV64.ModExp.powWin,
  .block zeroTop4, VG.Impl.Dsa.RISCV64.elemRange]

/-- `[4] := h^((p−1)/q) mod p` for `h` at `fH`: p into array 0, `−p⁻¹ mod 2⁶⁴`
into `t1`, `R² mod p` into arrays 1 and 24 (`rr`), `h` into array 4, then
the power over `sE`, array 4's word `w` zeroed; `a0 := 0` exactly when `1 < [4] < p`. -/
def power (pLen qLen : Nat) : Prog isa := seqs [powA pLen, .block [ld .s7 fH, .li .s8 pLen], powC pLen qLen]

/-! ## The search -/

/-- The geometry and the functions called. -/
structure Geo where
  pLen : Nat
  qLen : Nat
  G : Hash
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

/-- q from the seed: hashed, shaped, and tested. -/
def qPart : Prog isa := seqs [
  copyN [ld .a0 fSeed] [scr .a1 sMsg] g.qLen,
  hash g.G sQ,
  .block [.load .b .t2 .s6 sQ, .logicImm .or .t2 .t2 0x80, .store .b .t2 .s6 sQ,
    .load .b .t2 .s6 (sQ + g.qLen - 1), .logicImm .or .t2 .t2 1, .store .b .t2 .s6 (sQ + g.qLen - 1)],
  test g.pLen sQ g.qLen g.qName g.qCode]

/-- The hash of `seed + offset + j`, into its place in `X`. -/
def pHash (j : Nat) : Prog isa := seqs [
  copyN [ld .a0 fSeed] [scr .a1 sMsg] g.qLen,
  seedAdd g.qLen j,
  hash g.G (sX + g.pLen - (j + 1) * g.qLen)]

/-- The first `m` hashes of `X`. -/
def pHashes : Nat → Prog isa
  | 0 => .block []
  | m + 1 => .seq (pHashes m) (g.pHash m)

/-- `X`: the hashes, the top bit set. -/
def pX : Prog isa :=
  .seq (g.pHashes (g.count + 1))
    (.block [.load .b .t2 .s6 sX, .logicImm .or .t2 .t2 0x80, .store .b .t2 .s6 sX])

/-- A counter's candidate: `fP` := 0 if the tape ran out, 1 if it is a
probable prime, else as it was. -/
def pAttempt : Prog isa := seqs [
  g.pX, pArith g.pLen g.qLen,
  .block [.load .b .t2 .s6 sPBE, .shift .srl .d .t2 .t2 7],
  .ite (.zero .t2) (.block [])
    (seqs [test g.pLen sPBE g.pLen g.pName g.pCode,
      .block (cmpF fRes 0), .ite (.zero .t2) (.block (stImm fP 0))
        (seqs [.block (cmpF fRes 1), .ite (.zero .t2) (.block (stImm fP 1)) (.block [])])])]

/-- The next counter: `t2 = 0` when the `4 L` are done. -/
def pAdvance : List Instr :=
  [ld .t3 fCounter, .addi .t3 .t3 1, st .t3 fCounter, ld .t4 fOffset, .addi .t4 .t4 (g.count + 1),
    st .t4 fOffset, .li .t2 g.pLen, .shift .sll .d .t2 .t2 5, .sub .t2 .t3 .t2]

/-- p: `fP` := 0, 1 or 2 (none found). -/
def pPart : Prog isa := seqs [
  .block (stImm fCounter 0 ++ stImm fOffset 1 ++ stImm fP 4),
  .loop (seqs [g.pAttempt, .block (cmpF fP 4),
    .ite (.zero .t2) (.seq (.block g.pAdvance) (.ite (.zero .t2) (.block (stImm fP 2)) (.block [])))
      (.block []),
    .block (cmpF fP 4)]) (.zero .t2)]

/-- An `h` at `fH` (into array `aH`, zeroed first, as `load` needs):
`fG` := 1 with `g` at `sG` if `1 < h < p − 1` and `1 < g`. -/
def gStep : Prog isa := seqs [
  .block (ksRegs g.pLen), VG.Impl.Rsa.RISCV64.Keys.copy aH aZero, .block [ld .a0 fH, .li .a1 g.pLen], load aH .a0 .a1,
  seqs (ltS slLo aOne aH), seqs (ltS slHi aH aPm1),
  .block (andS slLo slLo slHi ++ [.load .d .t2 .s11 slLo]),
  .ite (.zero .t2) (.block [])
    (seqs [power g.pLen g.qLen,
      .ite (.zero .a0)
        (seqs [.block [scr .s7 sG, .li .s8 g.pLen], VG.Impl.Dsa.RISCV64.storeBE 4, .block (stImm fG 1)])
        (.block [])])]

/-- The window at the cursor: `fH` and `fHStart` its start, `fHLeft` its
octets, the smaller of the tape's rest and `128 p_len`, and `fFull` 1 if it
holds them all. -/
def window : Prog isa := .seq
  (.block [ld .t2 fWit, ld .t3 fUsed, .add .t2 .t2 .t3, st .t2 fH, st .t2 fHStart, ld .t4 fWitLen,
    .sub .t4 .t4 .t3, .li .t5 g.pLen, .shift .sll .d .t5 .t5 7])
  (.ite (.ltu .t4 .t5) (.block ([st .t4 fHLeft] ++ stImm fFull 0)) (.block ([st .t5 fHLeft] ++ stImm fFull 1)))

/-- g: `fG` := 1, or 2 if no `h` of the window gives one; the candidates
read counted as consumed. -/
def gPart : Prog isa := seqs [
  g.window, .block (stImm fG 4),
  .loop (seqs [.block [ld .t2 fHLeft, .li .t3 g.pLen],
    .ite (.ltu .t2 .t3) (.block (stImm fG 2))
      (seqs [g.gStep, .block [ld .t2 fH, .addi .t2 .t2 g.pLen, st .t2 fH, ld .t2 fHLeft,
        .addi .t2 .t2 (-(g.pLen : Int)), st .t2 fHLeft]]),
    .block (cmpF fG 4)]) (.zero .t2),
  .block [ld .t2 fH, ld .t3 fHStart, .sub .t2 .t2 .t3, ld .t3 fUsed, .add .t3 .t3 .t2, st .t3 fUsed]]

/-- p||q||g, checked: `fStatus` := 1 if it passes. -/
def checkPart : Prog isa := seqs [
  copyN [scr .a0 sPBE] (scrB .a1 sPacked ++ [.addi .a1 .a1 0]) g.pLen,
  copyN [scr .a0 sQ] (scrB .a1 sPacked ++ [.addi .a1 .a1 g.pLen]) g.qLen,
  copyN [scr .a0 sG] (scrB .a1 sPacked ++ [.addi .a1 .a1 (g.pLen + g.qLen)]) g.pLen,
  .block (scrB .a0 sPacked ++ [.li .a1 (2 * g.pLen + g.qLen), .li .a2 g.pLen, .li .a3 g.qLen] ++
    scrB .a4 (wB g.pLen) ++ wsLen .a5 g.pLen),
  .call g.checkName g.checkCode,
  .block [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32, .addi .t2 .a0 (-1)],
  .ite (.zero .t2) (.block (stImm fStatus 1)) (.block [])]

/-- The generator and the check, once `p` is found: without a generator, a
window cut short by the tape's end ran out. -/
def gCheck : Prog isa := seqs [
  g.gPart, .block (cmpF fG 1),
  .ite (.zero .t2) g.checkPart
    (seqs [.block [ld .t2 fFull], .ite (.zero .t2) (.block (stImm fStatus 0)) (.block [])])]

/-- A seed, at `fSeed`, its status 2 on entry. -/
def attempt : Prog isa := seqs [
  g.qPart, .block (cmpF fRes 0),
  .ite (.zero .t2) (.block (stImm fStatus 0))
    (seqs [.block (cmpF fRes 1),
      .ite (.zero .t2)
        (seqs [g.pPart, .block (cmpF fP 0),
          .ite (.zero .t2) (.block (stImm fStatus 0))
            (seqs [.block (cmpF fP 1), .ite (.zero .t2) g.gCheck (.block [])])])
        (.block [])])]

/-- One step of the controller, ending with `t2 := ` the status minus 2. -/
def iteration : Prog isa := seqs [
  .block [ld .t2 fUsed, st .t2 fStart, ld .t3 fLeft],
  .ite (.zero .t3) (.block (stImm fStatus 3))
    (seqs [.block [ld .t3 fWitLen, .sub .t3 .t3 .t2, .li .t4 g.qLen],
      .ite (.ltu .t3 .t4) (.block (stImm fStatus 0))
        (seqs [.block ([ld .t3 fWit, .add .t3 .t3 .t2, st .t3 fSeed, .addi .t2 .t2 g.qLen, st .t2 fUsed] ++
            stImm fStatus 2),
          g.attempt, .block (cmpF fStatus 2),
          .ite (.zero .t2) (.block [ld .t2 fLeft, .addi .t2 .t2 (-1), st .t2 fLeft]) (.block [])])]),
  .block (cmpF fStatus 2)]

/-- The seeds, one at a time, while they are rejected. -/
def search : Prog isa := .seq (.block (padInit g.qLen)) (.loop g.iteration (.zero .t2))

/-- `used := ` the state word `o`, and the state's words 0 and 3 := `t4`
and `t5`: each pointer loaded, then the stores through it. -/
def words (o : Nat) : Prog isa := seqs [.block [ld .t2 o, ld .t3 fUsedArg], .block [.store .d .t2 .t3 0],
  .block [ld .t3 fState], .block [.store .d .t4 .t3 0, .store .d .t5 .t3 24]]

/-- An exhausted search: `used := ` the seed's start, the state's words 0 and 3
:= 0, and 3. -/
def exhausted : Prog isa := seqs [.block [.li .t4 0, .li .t5 0], words fStart, .block [.li .a0 3]]

/-- The entropy budget (`Spec.Dsa.parameterEntropy`), into `rd`. -/
def budget (rd : Reg) : List Instr := [.li rd g.pLen, .shift .sll .d rd rd 15, .addi rd rd g.pLen]

/-- A seed that ran out: the octets left from its start (`t4`) exhaust the
search if they reach the budget (`t5`); otherwise `used := ` the seed's
start, the seeds left and the next tape's length (`Spec.Dsa.parameterRequest`)
into the state, and 0. -/
def ranOut : Prog isa :=
  .seq (.block ([ld .t4 fWitLen, ld .t3 fStart, .sub .t4 .t4 .t3] ++ budget g .t5))
    (.ite (.ltu .t4 .t5)
      (seqs [.block [.li .t3 g.pLen, .shift .sll .d .t3 .t3 8],
        .ite (.ltu .t4 .t3) (.block [.addi .t4 .t3 0]) (.block []),
        .block [.add .t4 .t4 .t4],
        .ite (.ltu .t4 .t5) (.block [.addi .t5 .t4 0]) (.block []),
        .block [ld .t4 fLeft], words fStart, .block [.li .a0 0]])
      exhausted)

/-- The result: for status 1, p||q||g to `out`, `used := ` the cursor and the
state's words 0 and 3 := 0, and 1; otherwise `out` zeroed, then `exhausted`
for status 3, `ranOut` for status 0. -/
def finish : Prog isa :=
  .seq (.block (cmpF fStatus 1))
    (.ite (.zero .t2)
      (seqs [copyN (scrB .a0 sPacked) [ld .a1 fOut] (2 * g.pLen + g.qLen),
        .block [.li .t4 0, .li .t5 0], words fUsed, .block [.li .a0 1]])
      (seqs [.block [ld .a0 fOut, .li .a1 (2 * g.pLen + g.qLen)], zeroBytes .a0 .a1,
        .block (cmpF fStatus 3), .ite (.zero .t2) exhausted g.ranOut]))

/-- The search and its result. -/
def generate : Prog isa := .seq g.search g.finish

end Geo

/-! ## Entry -/

/-- The words `entry` stores through `scratch` (`a5`): our caller's
callee-saved registers, our return address, the arguments, the seeds left
(`state[0]`, in `t2`) and nothing consumed (`t3`). -/
def entryStores : List (Reg × Nat) :=
  saved.zipIdx.map (fun (r, i) => (r, fSave + 8 * i)) ++
    [(.ra, fRA), (.a0, fOut), (.a2, fUsedArg), (.a3, fWit), (.a4, fWitLen), (.a7, fState), (.a6, fScrLen),
      (.t2, fLeft), (.t3, fUsed)]

/-- `state[0]` into `t2` and 0 into `t3`; the header's words stored, and
`scratch` into `s6`. -/
def entry : List Instr :=
  [.load .d .t2 .a7 0, .li .t3 0] ++ entryStores.map (fun p => .store .d p.1 .a5 p.2) ++ [.addi .s6 .a5 0]

/-- Our return address and our caller's registers back, `s6` last. -/
def restoreLoads : List (Reg × Nat) := (.ra, fRA) :: (saved.zipIdx.take 11).map fun (r, i) => (r, fSave + 8 * i)

def restore : List Instr := restoreLoads.map (fun p => ld p.1 p.2) ++ [ld .s6 (fSave + 8 * 11)]

/-- The three geometries, by `state[1]`. -/
def dispatch (g1 g2 g3 : Geo) : Prog isa :=
  .seq (.block [ld .t3 fState]) (.seq (.block [.load .d .t2 .t3 8, .li .t3 128])
    (.ite (.eq .t2 .t3) g1.generate
      (.seq (.block [.li .t3 256]) (.ite (.eq .t2 .t3) g2.generate g3.generate))))

def code (g1 g2 g3 : Geo) : Prog isa :=
  .seq (.block entry) (.seq (dispatch g1 g2 g3) (.block restore))

/-! ## `vg_dsa_parameter_search_init` -/

/-- `[4096, p_len, 32769 p_len, 512 p_len]` and 1. -/
def initWords : List Instr :=
  [.lui .t2 1, .store .d .t2 .a0 0, .store .d .a1 .a0 8, .shift .sll .d .t2 .a1 15, .add .t2 .t2 .a1,
    .store .d .t2 .a0 16, .shift .sll .d .t2 .a1 9, .store .d .t2 .a0 24, .li .a0 1]

/-- Four zeros and 0. -/
def initZeros : List Instr :=
  [.li .t2 0, .store .d .t2 .a0 0, .store .d .t2 .a0 8, .store .d .t2 .a0 16, .store .d .t2 .a0 24, .li .a0 0]

/-- `vg_dsa_parameter_search_init(state = a0, p_len = a1)`. -/
def init : Prog isa :=
  .seq (.block [.li .t3 128]) (.ite (.eq .a1 .t3) (.block initWords)
    (.seq (.block [.li .t3 256]) (.ite (.eq .a1 .t3) (.block initWords)
      (.seq (.block [.li .t3 384]) (.ite (.eq .a1 .t3) (.block initWords) (.block initZeros))))))

end VG.Impl.Dsa.RISCV64.ParameterSearch
