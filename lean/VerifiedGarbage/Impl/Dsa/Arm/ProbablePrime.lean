module

public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate

/-!
# DSA's probable-prime test on ARMv7

`vg_dsa_probable_prime_{bits}(ws, ws_len, rand, rand_len, used)`: `ws`,
`ws_len`, `rand` and `rand_len` in `r0`–`r3`, `used` on the stack. The
candidate is the `bits / 8` big-endian bytes at byte 0 of `ws`; the rest of
`ws`, from byte `keyOff`, is the key working space of the RSA candidate
(`Impl/RsaKeyGen/Arm/Candidate.lean`), whose trial division, exponent setup
and Montgomery constants this test runs as they are.

The function allocates 32 bytes and pushes the RSA candidate's frame of 56
bytes (`r0`–`r12` and `lr`) below them, so that the frame words that code
reads are this function's: before the push, the allocation holds `rand` and
`rand_len` (`aoR`, `aoRl`), the key working space and its length in 64-bit
words (`aoS`, `aoSl`), `ws` (`aoP`), and the candidate's bytes, the octets
of a witness and the uniform witnesses needed (`aoEl`, `aoPl`, `aoChk`), so
that the body depends on `bits` only through these words; `r1` is `L = 8 w`
(`foL`, `w` the 64-bit words of the arithmetic, at least 4) and `r2` is
`used` (`foUsed`).

1. The key working space zeroed, `c` loaded into the array `aC` from the
   candidate's bytes, the octets read `sUsed := 0`, the constants 1 and 2.
2. Trial division (RSA's, 512 primes through 1024 bits, 1024 above): 2 if
   a prime divides `c`.
3. `c − 1`, the exponent of the round and Montgomery arithmetic modulo `c`,
   as RSA's candidate sets them up.
4. Miller–Rabin, one witness an iteration, while fewer than 16 witnesses or
   fewer uniform ones than `primeChecks bits` have passed: 0 if `rand` has
   fewer than `D` octets left (`D = 8 ⌈bits / 64⌉`); else the witness `x`,
   the last `bits / 8` of the next `D` octets (all of them but for 160 bits),
   uniform if `2 ≤ x < c − 1`, otherwise with bit 1 set and bit `bits − 1`
   cleared; a call of the shared round; 2 if it fails.
5. 1, and `used` the octets read.
-/

@[expose] public section

namespace VG.Impl.Dsa.Arm.ProbablePrime
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate

/-! ## Widths -/

/-- The bytes of the candidate. -/
def len (bits : Nat) : Nat := bits / 8

/-- The 64-bit words of the arithmetic: the candidate's, at least 4 (the
round's least width). -/
def words (bits : Nat) : Nat := max 4 ((bits + 63) / 64)

/-- The octets a witness draws: whole 64-bit words, as many as the candidate has. -/
def draw (bits : Nat) : Nat := 8 * ((bits + 63) / 64)

/-- The uniform witnesses needed: DSA's `primeChecks`. -/
def checks (bits : Nat) : Nat := if bits ≤ 2048 then 64 else 128

/-- The key working space's byte offset in `ws`, above every candidate. -/
def keyOff : Nat := 384

/-! ## Entry -/

/-- The frame word of the uniform witnesses needed, the allocation's last. -/
def aoChk : Nat := 84

/-- Before the push (`sp` 32 below the caller's): the arguments into the
allocation where the candidate's code reads them after the push, `used`
into `r2` and `L` into `r1`; only caller-saved registers change. -/
def pre (bits : Nat) : List Instr :=
  [.addSp .r12 0, .str .r2 .r12 (aoR - 56), .str .r3 .r12 (aoRl - 56), .str .r0 .r12 (aoP - 56),
    .dp .add .r3 .r0 (.imm (BitVec.ofNat 32 keyOff)), .str .r3 .r12 (aoS - 56),
    .dp .sub .r3 .r1 (.imm (BitVec.ofNat 32 (keyOff / 8))), .str .r3 .r12 (aoSl - 56),
    .mov .r3 (.imm (BitVec.ofNat 32 (len bits))), .str .r3 .r12 (aoEl - 56),
    .mov .r3 (.imm (BitVec.ofNat 32 (draw bits))), .str .r3 .r12 (aoPl - 56),
    .mov .r3 (.imm (BitVec.ofNat 32 (checks bits))), .str .r3 .r12 (aoChk - 56),
    .ldr .r2 .r12 32, .mov .r1 (.imm (BitVec.ofNat 32 (8 * words bits)))]

/-- `sUsed := 0` and the constants 1 and 2. -/
def consts : List Instr := setS sUsed 0 ++ VG.Impl.RsaKeyGen.Arm.Key.setWd aOne 0 1 ++ VG.Impl.RsaKeyGen.Arm.Key.setWd aTwo 0 2

/-- The key working space, and `c` from the candidate's bytes. -/
def loadC : List (Prog isa) :=
  [.block setupC, zero, .block [.ldrSp .r4 aoP, .ldrSp .r6 aoEl], Rsa.Arm.CrtValues.load aC, .block consts]

/-! ## Miller–Rabin -/

/-- `i := 1`, `uniform := 0`, and the checks needed. -/
def mrInit : List Instr := setS sI 1 ++ setS sUni 0 ++ [.ldrSp .r1 aoChk, .str .r1 .r8 sChk]

/-- Z iff `rand` has fewer than `D` octets after `used`. -/
def avFlag : List Instr :=
  [.ldrSp .r1 aoRl, .ldr .r2 .r8 sUsed, .dp .sub .r1 .r1 (.reg .r2), .ldrSp .r2 aoPl, .subs .r3 .r1 (.reg .r2),
    .mov .r3 (.imm 0), .adc .r3 .r3 (.imm 0), .cmp .r3 (.imm 0)]

/-- The witness: the last `bits / 8` of the next `D` octets of `rand`, and
`used` advanced by `D`. -/
def witnessLoad : List (Prog isa) :=
  [.block [.ldrSp .r4 aoR, .ldr .r1 .r8 sUsed, .dp .add .r4 .r4 (.reg .r1), .ldrSp .r6 aoPl,
    .dp .add .r4 .r4 (.reg .r6), .dp .add .r1 .r1 (.reg .r6), .str .r1 .r8 sUsed, .ldrSp .r6 aoEl,
    .dp .sub .r4 .r4 (.reg .r6)], Rsa.Arm.CrtValues.load aX]

/-- Bit `8 len − 1` of `[j]` cleared: bit 31 of its word `len / 4 − 1`. -/
def clrBit (j : Nat) : List Instr :=
  .ldrSp .r2 aoEl :: (ptr .r0 j ++ [.dp .add .r0 .r0 (.reg .r2), .dp .sub .r0 .r0 (.imm 4), .ldr .r1 .r0 0,
    .mov .r1 (.shifted .r1 .lsl 1), .mov .r1 (.shifted .r1 .lsr 1), .str .r1 .r0 0])

/-- The slot `sU` := `2 ≤ x < c − 1`; the witness into `aH1`: `x` if it is
set, else `x` with bit 1 set and bit `bits − 1` cleared. -/
def witnessFix : List (Prog isa) :=
  ltS sA aX aTwo ++ ltS sBb aX aCm1 ++ [.block (VG.Impl.RsaKeyGen.Arm.Key.andNotS sU sA sBb), copy aXf aX,
    .block (orTwo aXf ++ clrBit aXf), sel aH1 aXf aX sU]

/-- One witness: `sStat := 0` (`rand` too short), `3` (it failed), or as
`onPass` sets it; Z iff on. -/
def mrBody (name : String) (round : Prog isa) : Prog isa :=
  seqs [.block avFlag,
    .ite .eq (.block (setS sStat 0))
      (seqs (witnessLoad ++ witnessFix ++ mrCall name round ++
        [.block (VG.Impl.RsaKeyGen.Arm.Key.isOne sF), .ite .eq (.block onPass) (.block (setS sStat 3))])),
    .block [.ldr .r1 .r8 sStat, .cmp .r1 (.imm 4)]]

def millerRabin (name : String) (round : Prog isa) : Prog isa :=
  .seq (.block mrInit) (.loop (mrBody name round) .eq)

/-! ## The result -/

/-- `used` := `r3`, and the status `r`. -/
def done (r : Nat) : List Instr := finish r

/-- The round's status 0, 1 or 3 as the result 0, 1 or 2, with the octets read. -/
def mrResult : Prog isa :=
  .seq (.block [.ldr .r1 .r8 sStat, .cmp .r1 (.imm 0)])
    (.ite .eq (.block ([.mov .r3 (.imm 0)] ++ done 0))
      (.seq (.block [.ldr .r3 .r8 sUsed, .ldr .r1 .r8 sStat, .cmp .r1 (.imm 1)])
        (.ite .eq (.block (done 1)) (.block (done 2)))))

/-- Once `c` passed trial division. -/
def mrPart (name : String) (round : Prog isa) : Prog isa :=
  seqs ([sub3 aCm1 aC aOne] ++ expSetup ++ [montA, montB, millerRabin name round, mrResult])

def body (name : String) (round : Prog isa) : Prog isa :=
  seqs (loadC ++ trial ++ [.ite .eq (mrPart name round) (.block ([.mov .r3 (.imm 0)] ++ done 2))])

/-- `vg_dsa_probable_prime_{bits}`, calling the round `round` named `name`. -/
def code (bits : Nat) (name : String) (round : Prog isa) : Prog isa :=
  .frame (.alloc 32)
    (.seq (.block (pre bits))
      (.frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
        (.seq (body name round) (.block PcFn.restore)) (.pop .r12 56)))
    (.free 32)

end VG.Impl.Dsa.Arm.ProbablePrime
