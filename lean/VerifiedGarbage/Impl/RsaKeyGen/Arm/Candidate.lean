module

public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Key
public import VerifiedGarbage.Impl.RsaKeyGen.Primes
public import VerifiedGarbage.Impl.Bignum.Arm.TrialDivision16
public import VerifiedGarbage.Impl.Bignum.Arm.TwoPower

/-!
# A candidate for a prime of an RSA key on ARMv7

`vg_rsa_keygen_candidate(out, out_len, used, e, e_len, p, p_len, rand,
rand_len, scratch, scratch_len)`: the first four arguments in `r0`–`r3`, the
others on the stack. The function pushes a frame of 56 bytes (`r0`–`r12`
and `lr`), as `vg_rsa_keygen_key` does: `out_len`, `used` and `e` are then
frame words 1, 2 and 3, `out` is moved to frame word 12, and frame word 0
holds the base of Montgomery multiplication's working space, as `montOp`
and the Miller–Rabin round take it. The stack arguments start at byte 56.

The numbers live in the key working space at `scratch`
(`Impl/Rsa/Arm/KeyWs.lean`) with `W = 2 w + 2` words of 32 bits, for
`w = out_len / 8`: its stride is that of Montgomery multiplication's working
space (`Proof/Rsa/MontContract.lean`) for numbers of `w` words of 64 bits, which is
placed so that its arrays are the key arrays from `mBase` = 21 on (its array
`j` is the key array `21 + j`), and its header lies in the key arrays 15–20,
which nothing else uses. That working space is also the one the shared
Miller–Rabin round (`Proof/MillerRabin/Contract.lean`, the compact representation)
takes, from the candidate `c` in its array 0.

1. If `rand` is shorter than `out_len`, the result is 0.
2. `c`: the first `out_len` octets of `rand`, its two top bits and its low
   bit set; `used := out_len`.
3. If `p` is given: `c − p` and `p − c`, the one that does not borrow
   selected under the mask of the first's borrow, compared with
   `2^(8 out_len − 100)`; the result is 2 if it is not above.
4. Trial division by the table of small primes (`Impl/RsaKeyGen/Primes.lean`,
   two 16-bit entries a word), written over the key arrays from 22 (its
   second half only for `w > 16`): for each prime `s`, `c 2^(−64 w) mod s`
   by Montgomery reduction of `c`'s 16-bit halves from the least significant
   (`acc := (acc + h) 2^(−16) mod s`, kept below `2 s`), with
   `−s⁻¹ mod 2^16` by Newton's iteration; `s` divides `c` iff `acc` is 0 or
   `s`. The masks of all primes are or'ed, and the result is 3 if one is
   set.
5. `gcd(c − 1, e)`: 3 if `e` is even; nothing for `e = 1`; otherwise
   `inverse` modulo `e` from `c − 1` (`Impl/Rsa/Arm/Inverse.lean`), whose `v`
   ends as the gcd; 3 unless it is 1.
6. The exponent the round's contract takes: `t`, the exponent of 2 in
   `c − 1`, by `64 w` halvings of `c − 1` under masks; `E = c / 2^σ` for the
   shift `σ ∈ [1, 4]` with `σ ≡ t (mod 4)` (halvings under the masks of
   `σ > 1`, `σ > 2` and `σ > 3`), followed by the word `2^(t mod 64)`, built
   by five shifts under the masks of the bits of `t`. Then Montgomery
   multiplication's working space: its header (`setup`, and the stride),
   `−c⁻¹ mod 2^64` and `R² mod c` (`precomputeInverse`, `r2`), `R mod c`
   (from `1 · R²`) and `c − R mod c`: the Montgomery forms of 1 and `−1`.
7. Miller–Rabin, one witness an iteration, while fewer than 16 witnesses or
   fewer uniform ones than `BN_prime_checks_for_size` have passed: 0 if
   `rand` has fewer than `out_len` octets left; else the witness `x`, the
   next `out_len` octets, uniform if `2 ≤ x < c − 1`, otherwise bit 1 set and
   the top bit cleared; its Montgomery form into array 5, and a call of the
   shared round. 3 if it fails; otherwise the witness counts. Then the
   result is 1 and `c` is written to `out`.

`out` and `used` are written at the end: `c` or zeros, and the octets read
(`out_len` per number), or 0 for the result 0.

Every choice on secrets is a selection (`sel`) or a flag computed with
`and`, `orr`, `eor` and shifts; addresses and loop counts depend only on the
pointers and the lengths, and the branches on `p_len`, `e` and what the
leak allows: the result of each check and whether each witness passed.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.Arm.Candidate
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Rsa.Arm.Keys

/-! ## The frame

After the push: `out_len`, `used` and `e` at bytes 4, 8 and 12, `out`
(moved) at byte 48, and the stack arguments from byte 56: `e_len`, `p`,
`p_len`, `rand`, `rand_len`, `scratch`, `scratch_len`. -/

def foL : Nat := 4
def foUsed : Nat := 8
def foE : Nat := 12
def foOut : Nat := 48
def aoEl : Nat := 56
def aoP : Nat := 60
def aoPl : Nat := 64
def aoR : Nat := 68
def aoRl : Nat := 72
def aoS : Nat := 76
def aoSl : Nat := 80

/-! ## The arrays

0–14 are `inverse`'s; 15–20 hold Montgomery multiplication's header, and
21–48 are its arrays 0–27 (`c` the first; the table of small primes is
written from 22); then `e`, `p`, the differences and the bound of the check
against `p`, the constants 1 and 2, `c − 1`, the witness and its fixed form,
and the halvings'. -/

def mBase : Nat := 21
def aC : Nat := 21
def aTab : Nat := 22
def aE : Nat := 49
def aPr : Nat := 50
def aD1 : Nat := 51
def aD2 : Nat := 52
def aAbs : Nat := 53
/-- `2^(8 out_len − 100)`. -/
def aBnd : Nat := 54
def aTmp : Nat := 55
def aOne : Nat := 56
def aTwo : Nat := 57
def aCm1 : Nat := 58
def aX : Nat := 59
def aXf : Nat := 60
def aH1 : Nat := 61
def aH2 : Nat := 62
def aHm : Nat := 63
def aEx : Nat := 64
/-- The number of arrays. -/
def nArr : Nat := 65

/-! ## The header

Bytes 0–19 are the division's (16: `W`), 100–112 the shared routines', and
132 the mask of `CrtValues.store`. -/

def sUsed : Nat := 20
def sCl : Nat := 24
def sLt : Nat := 28
def sTr : Nat := 32
def sEo : Nat := 36
def sE1 : Nat := 40
def sG : Nat := 44
def sI : Nat := 48
def sUni : Nat := 52
def sU : Nat := 56
def sA : Nat := 60
def sBb : Nat := 64
def sTc : Nat := 68
def sBit : Nat := 72
def sCnt : Nat := 76
def sS1 : Nat := 80
def sS2 : Nat := 84
def sS3 : Nat := 88
def sLo : Nat := 92
def sHi : Nat := 96
def sF : Nat := 116
def sStat : Nat := 120
def sChk : Nat := 124
def sMask : Nat := 132

/-! ## Contexts and small steps -/

/-- The base of the working space into `r8`. -/
def ctxB : List Instr := [.ldrSp .r8 aoS]

/-- `W` (header byte 16) into `r9` and the stride into `r7`. -/
def ctxW : List Instr := [.ldr .r9 .r8 16] ++ stride

def ctx : List Instr := ctxB ++ ctxW

/-- The slot `d` := `[a] < [b]`, the borrow of `[a] − [b]` (`[aTmp]` scratch). -/
def ltS (d a b : Nat) : List (Prog isa) := [sub3 aTmp a b, .block [.str .r11 .r8 d]]

/-- The slot `d` := `v`. -/
def setS (d v : Nat) : List Instr := [.mov .r1 (.imm (BitVec.ofNat 32 v)), .str .r1 .r8 d]

/-- `[o] := [a]⁻¹ mod [m]`'s start and `inverse`: `(u, v, x₁, x₂) = (a, m, 1, 0)`. -/
def invOf (a m : Nat) : Prog isa :=
  seqs [copy aM m, copy 0 a, copy 1 aM, copy 2 aOne, copy 3 aZero, sub3 aNM aZero aM, inverse]

/-- `used` (frame word 2) := `r3`, and the status `r` returned. -/
def finish (r : Nat) : List Instr :=
  [.ldrSp .r2 foUsed, .str .r3 .r2 0, .mov .r1 (.imm 0), .str .r1 .r2 4, .mov .r0 (.imm (BitVec.ofNat 32 r))]

/-- Status 0: zeros to `out`, and `used` is 0. -/
def finNone : Prog isa := .seq (Key.zeroOut foOut foL) (.block ([.mov .r3 (.imm 0)] ++ finish 0))

/-- Status `r` (2 or 3): zeros to `out`, and `used` is the octets read. -/
def finUsed (r : Nat) : Prog isa := .seq (Key.zeroOut foOut foL) (.block ([.ldr .r3 .r8 sUsed] ++ finish r))

/-- Status 1: `c` to `out` under the mask, all ones, and `used` the octets read. -/
def finPrime : Prog isa := seqs [
  .block (setS sMask 1 ++ [.ldrSp .r10 foOut, .ldrSp .r11 foL]), Rsa.Arm.CrtValues.store aC,
  .block ([.ldr .r3 .r8 sUsed] ++ finish 1)]

/-! ## Entry -/

/-- `out` to frame word 12. -/
def entry : List Instr := [.addSp .r12 0, .str .r0 .r12 foOut]

/-- Z iff `rand_len < out_len`: the carry of `rand_len − out_len` made a value. -/
def lenCheck : List Instr :=
  [.ldrSp .r1 aoRl, .ldrSp .r2 foL, .subs .r3 .r1 (.reg .r2), .mov .r3 (.imm 0), .adc .r3 .r3 (.imm 0),
    .cmp .r3 (.imm 0)]

/-! ## The candidate -/

/-- `W = out_len / 4 + 2`, the stride, `W` into the division's header, and
every array zeroed. -/
def setupC : List Instr :=
  ctxB ++ [.ldrSp .r9 foL, .mov .r9 (.shifted .r9 .lsr 2), .dp .add .r9 .r9 (.imm 2)] ++ stride ++
  [.str .r9 .r8 16, .dp .add .r0 .r8 (.imm (BitVec.ofNat 32 hdr)), .mov .lr (.imm (BitVec.ofNat 32 nArr)),
    .mul .lr .lr .r7, .mov .lr (.shifted .lr .lsr 2), .mov .r3 (.imm 0)]

/-- The two top bits of `[aC]` (word `2 w − 1`) set. -/
def topBits : List Instr :=
  ptr .r0 aC ++ [.dp .add .r0 .r0 (.shifted .r9 .lsl 2), .dp .sub .r0 .r0 (.imm 12), .ldr .r1 .r0 0,
    .dp .orr .r1 .r1 (.imm 0xC0000000), .str .r1 .r0 0]

/-- `used := out_len`, the candidate's bits, and the constants 1 and 2. -/
def candBits : List Instr :=
  [.ldrSp .r1 foL, .str .r1 .r8 sUsed] ++ topBits ++ orOne aC ++ Key.setWd aOne 0 1 ++ Key.setWd aTwo 0 2

/-- The working space, and `c` from `rand`. -/
def loadC : List (Prog isa) :=
  [.block setupC, zero, .block [.ldrSp .r4 aoR, .ldrSp .r6 foL], Rsa.Arm.CrtValues.load aC, .block candBits]

/-! ## Too close to `p` -/

/-- `|c − p|`, the bound, and the slot `sCl` := `|c − p| ≤ 2^(8 out_len − 100)`. -/
def closeCalc : List (Prog isa) :=
  [.block [.ldrSp .r4 aoP, .ldrSp .r6 aoPl], Rsa.Arm.CrtValues.load aPr, sub3 aD1 aC aPr, .block [.str .r11 .r8 sLt],
    sub3 aD2 aPr aC, sel aAbs aD1 aD2 sLt, .block (Key.setHi aBnd 2 24 0x10000000)] ++ ltS sCl aBnd aAbs ++
  [.block (Key.notS sCl sCl)]

/-- `sCl`, 0 without `p`; then Z iff it is set. -/
def closeCheck : List (Prog isa) :=
  [.block [.ldrSp .r1 aoPl, .cmp .r1 (.imm 0)], .ite .eq (.block (setS sCl 0)) (seqs closeCalc),
    .block (Key.isOne sCl)]

/-! ## Trial division -/

/-- Word `j` of the table: entries `2 j` and `2 j + 1`, the first the less significant. -/
def tabWord32 (j : Nat) : Nat := tabEntry (2 * j) + tabEntry (2 * j + 1) * 2 ^ 16

/-- Store word `j` of the table at `[r12 + 4 j]`. -/
def tabStore (j : Nat) : List Instr :=
  [.movw .r1 (BitVec.ofNat 16 (tabEntry (2 * j))), .movt .r1 (BitVec.ofNat 16 (tabEntry (2 * j + 1))),
    .str .r1 .r12 (4 * j)]

/-- The words `a` to `a + n − 1` of the table. -/
def tabWrite (a n : Nat) : List Instr := (List.range n).flatMap fun j => tabStore (a + j)

/-- `r1 := 1` if `w > 16` (`W ≥ 35`), else 0. -/
def bigW : List Instr := [.subs .r1 .r9 (.imm 35), .mov .r1 (.imm 0), .adc .r1 .r1 (.imm 0)]

/-- The table: its first 256 words, and the other 256 for `w > 16`. -/
def table : List (Prog isa) :=
  [.block (ptr .r12 aTab ++ tabWrite 0 256 ++ bigW ++ [.cmp .r1 (.imm 0)]),
    .ite .eq (.block []) (.block (ptr .r12 aTab ++ tabWrite 256 256))]

/-- `r4 := r4 (2 − s r4)` for `s` in `r3`. -/
def newton : List Instr := TrialDivision16.newton

/-- For the prime `s` in `r3`: `−s⁻¹ mod 2^16` into `r4`, `acc := 0` (`r2`),
`c`'s first word into `r0` and its count of words `2 w` into `r1`. -/
def entryS : List Instr :=
  [.mov .r4 (.reg .r3)] ++ newton ++ newton ++ newton ++
  [.mov .r5 (.imm 0), .dp .sub .r4 .r5 (.reg .r4), .mov .r4 (.shifted .r4 .lsl 16), .mov .r4 (.shifted .r4 .lsr 16)] ++
  ptr .r0 aC ++ [.dp .sub .r1 .r9 (.imm 2), .mov .r2 (.imm 0)]

/-- `acc := (acc + h) 2^(−16) mod s` (below `2 s`), for `h` in `r5`: with
`x = acc + h` and `q = x (−s⁻¹) mod 2^16`, `(x + q s) / 2^16`. -/
def redc : List Instr := TrialDivision16.redc

/-- A word of `c`: its low half, then its high half; the next word, and the
count. -/
def trialWord : List Instr :=
  [.ldr .r5 .r0 0, .mov .r5 (.shifted .r5 .lsl 16), .mov .r5 (.shifted .r5 .lsr 16)] ++ redc ++
  [.ldr .r5 .r0 0, .mov .r5 (.shifted .r5 .lsr 16)] ++ redc ++
  [.dp .add .r0 .r0 (.imm 4), .subs .r1 .r1 (.imm 1)]

/-- `r11 |=` the mask of `acc ∈ {0, s}`. -/
def trialFlag : List Instr :=
  [.dp .sub .r5 .r2 (.imm 1), .mov .r5 (.shifted .r5 .lsr 31), .dp .eor .r6 .r2 (.reg .r3),
    .dp .sub .r6 .r6 (.imm 1), .mov .r6 (.shifted .r6 .lsr 31), .dp .orr .r5 .r5 (.reg .r6),
    .dp .orr .r11 .r11 (.reg .r5)]

/-- The prime `s` in `r3`, from the table word in `r10`. -/
def trialPrime (s : List Instr) : List (Prog isa) :=
  [.block (s ++ entryS), .loop (.block trialWord) .ne, .block trialFlag]

/-- A word of the table: its two primes. -/
def trialStep : Prog isa :=
  seqs ([.block [.ldr .r10 .r12 0, .dp .add .r12 .r12 (.imm 4)]] ++
    trialPrime [.mov .r3 (.shifted .r10 .lsl 16), .mov .r3 (.shifted .r3 .lsr 16)] ++
    trialPrime [.mov .r3 (.shifted .r10 .lsr 16)] ++ [.block [.subs .lr .lr (.imm 1)]])

/-- The table's words (256, or 512 for `w > 16`) through `r12`, counted in
`lr`; the slot `sTr` := whether a prime divides `c`, and Z iff not. -/
def trial : List (Prog isa) :=
  table ++ [.block (bigW ++ [.mov .lr (.shifted .r1 .lsl 8), .dp .add .lr .lr (.imm 256), .mov .r11 (.imm 0)] ++
    ptr .r12 aTab), .loop trialStep .ne, .block [.str .r11 .r8 sTr, .cmp .r11 (.imm 0)]]

/-! ## `gcd(c − 1, e)` -/

/-- `c − 1`, `e`, and the slot `sG` := `gcd(c − 1, e) = 1`; then Z iff it is. -/
def gcdCheck : List (Prog isa) := [
  sub3 aCm1 aC aOne,
  .block [.ldrSp .r4 foE, .ldrSp .r6 aoEl], Rsa.Arm.CrtValues.load aE,
  .block (bitOf sEo aE), eqS sE1 aE aOne aTmp,
  .block (Key.isOne sEo),
  .ite .eq
    (.seq (.block (Key.isOne sE1)) (.ite .eq (.block (setS sG 1)) (seqs [invOf aCm1 aE, eqS sG 1 aOne aTmp])))
    (.block (setS sG 0)),
  .block (Key.isOne sG)]

/-! ## Montgomery arithmetic modulo `c` -/

/-- Montgomery multiplication's working space's base, `256` bytes before the
key array `mBase`, into frame word 0 and `r0`; `w` into `r7`, `r3 = 0`. -/
def montSet : List Instr :=
  ptr .r0 mBase ++ [.dp .sub .r0 .r0 (.imm 256), .addSp .r12 0, .str .r0 .r12 0, .ldrSp .r7 foL,
    .mov .r7 (.shifted .r7 .lsr 3), .mov .r3 (.imm 0)]

/-- Its header word 28 := the stride `8 (w + 2)` (`r0` its base, `r7` the key
working space's stride, `4 (W + 2) = 8 (w + 2)`). -/
def strideW : List Instr := .mov .r1 (.imm 0) :: store64 .r7 .r1 .r0 224

/-- The base of Montgomery multiplication's working space into `r0`. -/
def mont0 : List Instr := [.ldrSp .r0 0]

/-- The words above the low `2 w` of `[j]` cleared. -/
def clrTop (j : Nat) : List Instr := Rsa.Arm.Recover.clrTop j

/-- The working space, `−c⁻¹`, `R² mod c` (array 4), `c`'s top words cleared,
and the stride. -/
def montA : Prog isa :=
  seqs [.block montSet, setup, precomputeInverse, r2, .block (ctx ++ clrTop mBase), .block mont0, .block strideW]

/-- `R mod c` (array 9, from `1 · R²`) and `c − R mod c` (array 10). -/
def montB : Prog isa :=
  seqs [copy (mBase + 1) aOne, .block mont0, montOp 1 1 4, .block (ctx ++ clrTop (mBase + 1)),
    copy (mBase + 9) (mBase + 1), sub3 (mBase + 10) mBase (mBase + 9)]

/-! ## The exponent of the round -/

/-- The halving's count `64 w = 8 out_len`. -/
def cnt8 : List Instr := [.ldrSp .r1 foL, .mov .r1 (.shifted .r1 .lsl 3), .str .r1 .r8 sCnt]

/-- `m := c − 1`, `t := 0`, and the count. -/
def halfInit : Prog isa := seqs [copy aHm aCm1, .block (setS sTc 0 ++ cnt8)]

/-- `m` even into `sBit`, and `t +=` it. -/
def halfBit : List Instr :=
  bitOf sBit aHm ++ [.ldr .r1 .r8 sBit, .dp .eor .r1 .r1 (.imm 1), .str .r1 .r8 sBit,
    .ldr .r2 .r8 sTc, .dp .add .r2 .r2 (.reg .r1), .str .r2 .r8 sTc]

/-- The count decremented: Z when it reaches 0. -/
def cntNext : List Instr := [.ldr .r1 .r8 sCnt, .subs .r1 .r1 (.imm 1), .str .r1 .r8 sCnt]

/-- A halving: `m := m / 2` and `t += 1` if `m` is even. -/
def halfBody : Prog isa := seqs [copy aH1 aHm, copy aH2 aHm, .block [.mov .r11 (.imm 0)], half aH2,
  .block halfBit, sel aHm aH1 aH2 sBit, .block cntNext]

/-- `t`: the exponent of 2 in `c − 1`. -/
def halving : Prog isa := .seq halfInit (.loop halfBody .ne)

/-- The masks of `σ > 1`, `σ > 2` and `σ > 3` from `t mod 4`. -/
def sigMasks : List Instr :=
  [.ldr .r1 .r8 sTc, .dp .and .r1 .r1 (.imm 3),
    .dp .sub .r2 .r1 (.imm 1), .mov .r2 (.shifted .r2 .lsr 31),
    .dp .eor .r3 .r1 (.imm 1), .dp .sub .r3 .r3 (.imm 1), .mov .r3 (.shifted .r3 .lsr 31),
    .dp .eor .r4 .r1 (.imm 3), .dp .sub .r4 .r4 (.imm 1), .mov .r4 (.shifted .r4 .lsr 31),
    .dp .eor .r3 .r3 (.imm 1), .str .r3 .r8 sS1,
    .dp .orr .r4 .r4 (.reg .r2), .str .r4 .r8 sS2, .str .r2 .r8 sS3]

/-- `r2 := r2 << 2^j` if bit `j` of `r1` is set (`r3`, `r4` scratch). -/
def powStep (j : Nat) : List Instr := TwoPower.step j

/-- `2^(t mod 64)` as the slots `sLo` and `sHi`. -/
def powWord : List Instr :=
  [.ldr .r1 .r8 sTc] ++ TwoPower.code ++ [.str .r2 .r8 sLo, .str .r3 .r8 sHi]

/-- `[aEx]` halved if the slot `sl` holds 1. -/
def halfIf (sl : Nat) : List (Prog isa) :=
  [copy aH1 aEx, copy aH2 aEx, .block [.mov .r11 (.imm 0)], half aH2, sel aEx aH1 aH2 sl]

/-- The word after the low `2 w` of the exponent's array := `2^(t mod 64)`. -/
def expTop : List Instr :=
  ptr .r0 (mBase + 27) ++ [.dp .add .r0 .r0 (.shifted .r9 .lsl 2), .dp .sub .r0 .r0 (.imm 8),
    .ldr .r1 .r8 sLo, .str .r1 .r0 0, .ldr .r1 .r8 sHi, .str .r1 .r0 4]

/-- The exponent `E = c / 2^σ` into array 27, followed by `2^(t mod 64)`. -/
def expSetup : List (Prog isa) :=
  [halving, .block (sigMasks ++ powWord), copy aEx aC, .block [.mov .r11 (.imm 0)], half aEx] ++
    halfIf sS1 ++ halfIf sS2 ++ halfIf sS3 ++ [copy (mBase + 27) aEx, .block expTop]

/-! ## Miller–Rabin -/

/-- `r1 += 1` if `W < k`. -/
def ltAdd (k : Nat) : List Instr :=
  [.dp .sub .r2 .r9 (.imm (BitVec.ofNat 32 k)), .mov .r2 (.shifted .r2 .lsr 31), .dp .add .r1 .r1 (.reg .r2)]

/-- `sChk := checksW w` (`w < k` iff `W < 2 k + 2`). -/
def checksC : List Instr :=
  [.mov .r1 (.imm 3)] ++ ltAdd 120 ++ ltAdd 46 ++ ltAdd 18 ++ ltAdd 16 ++ ltAdd 14 ++
  [.dp .sub .r2 .r9 (.imm 12), .mov .r2 (.shifted .r2 .lsr 31), .mov .r3 (.imm 19), .mul .r2 .r2 .r3,
    .dp .add .r1 .r1 (.reg .r2), .str .r1 .r8 sChk]

/-- `i := 1`, `uniform := 0`, and the checks needed. -/
def mrInit : List Instr := setS sI 1 ++ setS sUni 0 ++ checksC

/-- Z iff `rand` has fewer than `out_len` octets after `used`. -/
def avFlag : List Instr :=
  [.ldrSp .r1 aoRl, .ldr .r2 .r8 sUsed, .dp .sub .r1 .r1 (.reg .r2), .ldrSp .r2 foL, .subs .r3 .r1 (.reg .r2),
    .mov .r3 (.imm 0), .adc .r3 .r3 (.imm 0), .cmp .r3 (.imm 0)]

/-- The witness: the next `out_len` octets of `rand`, and `used` advanced. -/
def witnessLoad : List (Prog isa) :=
  [.block [.ldrSp .r4 aoR, .ldr .r1 .r8 sUsed, .dp .add .r4 .r4 (.reg .r1), .ldrSp .r6 foL,
    .dp .add .r1 .r1 (.reg .r6), .str .r1 .r8 sUsed], Rsa.Arm.CrtValues.load aX]

/-- Bit 1 of `[j]` set. -/
def orTwo (j : Nat) : List Instr := ptr .r0 j ++ [.ldr .r1 .r0 0, .dp .orr .r1 .r1 (.imm 2), .str .r1 .r0 0]

/-- Bit `64 w − 1` of `[j]` cleared. -/
def clrTopBit (j : Nat) : List Instr :=
  ptr .r0 j ++ [.dp .add .r0 .r0 (.shifted .r9 .lsl 2), .dp .sub .r0 .r0 (.imm 12), .ldr .r1 .r0 0,
    .mov .r1 (.shifted .r1 .lsl 1), .mov .r1 (.shifted .r1 .lsr 1), .str .r1 .r0 0]

/-- The slot `sU` := `2 ≤ x < c − 1`; the witness into `aH1`: `x` if it is
set, else `x` with bit 1 set and its top bit cleared. -/
def witnessFix : List (Prog isa) :=
  ltS sA aX aTwo ++ ltS sBb aX aCm1 ++ [.block (Key.andNotS sU sA sBb), copy aXf aX,
    .block (orTwo aXf ++ clrTopBit aXf), sel aH1 aXf aX sU]

/-- `r1 := ws_len − (21 w + 30)`, the 64-bit words of the round's working space. -/
def wsLen : List Instr :=
  [.ldrSp .r0 0, .ldrSp .r1 aoSl, .ldrSp .r2 foL, .mov .r2 (.shifted .r2 .lsr 3), .mov .r3 (.imm 21),
    .mul .r2 .r2 .r3, .dp .add .r2 .r2 (.imm 30), .dp .sub .r1 .r1 (.reg .r2)]

/-- The witness in Montgomery form (array 5), the round, and its result
into `sF`. -/
def mrCall (name : String) (round : Prog isa) : List (Prog isa) :=
  [copy (mBase + 1) aH1, .block mont0, montOp 5 1 4, .block wsLen, .call name round,
    .block (ctx ++ [.str .r0 .r8 sF])]

/-- `r1 := 1` if more witnesses are needed: `i ≤ 16` or `uniform < checks`. -/
def goFlag : List Instr :=
  [.ldr .r1 .r8 sI, .dp .sub .r1 .r1 (.imm 17), .mov .r1 (.shifted .r1 .lsr 31),
    .ldr .r2 .r8 sUni, .ldr .r3 .r8 sChk, .dp .sub .r2 .r2 (.reg .r3), .mov .r2 (.shifted .r2 .lsr 31),
    .dp .orr .r1 .r1 (.reg .r2)]

/-- A witness that passed: `i += 1`, `uniform +=` its flag, and `sStat := 4`
to go on if more witnesses are needed, else 1. -/
def onPass : List Instr :=
  [.ldr .r1 .r8 sI, .dp .add .r1 .r1 (.imm 1), .str .r1 .r8 sI, .ldr .r2 .r8 sU, .ldr .r3 .r8 sUni,
    .dp .add .r3 .r3 (.reg .r2), .str .r3 .r8 sUni] ++ goFlag ++
  [.dp .add .r1 .r1 (.shifted .r1 .lsl 1), .dp .add .r1 .r1 (.imm 1), .str .r1 .r8 sStat]

/-- One witness: `sStat := 0` (`rand` too short), `3` (it failed), or as
`onPass` sets it; Z iff on. -/
def mrBody (name : String) (round : Prog isa) : Prog isa :=
  seqs [.block avFlag,
    .ite .eq (.block (setS sStat 0))
      (seqs (witnessLoad ++ witnessFix ++ mrCall name round ++
        [.block (Key.isOne sF), .ite .eq (.block onPass) (.block (setS sStat 3))])),
    .block [.ldr .r1 .r8 sStat, .cmp .r1 (.imm 4)]]

def millerRabin (name : String) (round : Prog isa) : Prog isa :=
  .seq (.block mrInit) (.loop (mrBody name round) .eq)

/-- The result of Miller–Rabin. -/
def mrResult : Prog isa :=
  .seq (.block [.ldr .r1 .r8 sStat, .cmp .r1 (.imm 0)])
    (.ite .eq finNone (.seq (.block [.ldr .r1 .r8 sStat, .cmp .r1 (.imm 1)]) (.ite .eq finPrime (finUsed 3))))

/-! ## `vg_rsa_keygen_candidate` -/

/-- Once the candidate passed trial division and `gcd(c − 1, e) = 1`. -/
def mrPart (name : String) (round : Prog isa) : Prog isa :=
  seqs (expSetup ++ [montA, montB, millerRabin name round, mrResult])

/-- Once `rand` has the candidate's octets. -/
def main (name : String) (round : Prog isa) : Prog isa :=
  seqs (loadC ++ closeCheck ++ [.ite .eq (finUsed 2) (seqs (trial ++
    [.ite .eq (seqs (gcdCheck ++ [.ite .eq (mrPart name round) (finUsed 3)])) (finUsed 3)]))])

def body (name : String) (round : Prog isa) : Prog isa :=
  seqs [.block entry, .block lenCheck, .ite .eq finNone (main name round)]

/-- `vg_rsa_keygen_candidate`, calling the round `round` named `name`. -/
def code (name : String) (round : Prog isa) : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq (body name round) (.block PcFn.restore)) (.pop .r12 56)

end VG.Impl.RsaKeyGen.Arm.Candidate
