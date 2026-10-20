module

public import VerifiedGarbage.TCB.Arm.Isa

/-!
# Bounded DSA scalar sampling on 32-bit ARM

An internal program for a caller with a stack frame of `frameBytes` bytes,
whose base `r11` holds: its slots are below, and the caller's stack
arguments above it (`arg`). `prepare` scans the public q and clears the
padded nonce. `sample` consumes at most 128 complete draws from the tape at
`rand`, from the offset `[oUsed]`, and returns status 1 (accepted), 2 (short
tape) or 0 (draw limit). The caller must skip `sample` if `prepare` returns
zero.

As on x86, every branch is on public q, the tape's length, the count of
draws and the accept bit of a draw; a candidate's bytes reach no branch or
address. ARMv7's branches test only `Z`, so an unsigned comparison is a
shift (against a power of two) or the carry of a subtraction, read by `adc`.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.Random
open VG VG.Arm

/-- Slots of the frame: the saved `r4`–`r11` and `lr` at `0`–`32`. -/
def oUsed : Nat := 36
def oAttempts : Nat := 40
def oDraws : Nat := 44
def oQ : Nat := 48
def oWidth : Nat := 52
def oMask : Nat := 56
def oStatus : Nat := 60
def oNonce : Nat := 64
def oOut : Nat := 96
def oOutLen : Nat := 100
def oUsedPtr : Nat := 104
def oKey : Nat := 108
def frameBytes : Nat := 112

/-- `t = [r11 + o]`, `[r11 + o] = t`. -/
def ld (t : Reg) (o : Nat) : Instr := .ldr t .r11 o
def st (t : Reg) (o : Nat) : Instr := .str t .r11 o

/-- The caller's stack argument `j`, above the frame. -/
def arg (j : Nat) : Nat := frameBytes + 4 * j

/-- Stack arguments: `key_len`, `p_len`, `q_len`, `digest`, `digest_len`,
`rand`, `rand_len`, `scratch`, `scratch_len` (`out`, `out_len`, `used`
and `key` are the registers, saved at `oOut`–`oKey`). -/
def aKeyLen : Nat := 0
def aPLen : Nat := 1
def aQLen : Nat := 2
def aDigest : Nat := 3
def aDigestLen : Nat := 4
def aRand : Nat := 5
def aRandLen : Nat := 6
def aScratch : Nat := 7
def aScratchLen : Nat := 8

/-- Record the first nonzero byte of the scan (in `r4`), and the bytes from
it on (in `r3`), if none was found yet. -/
def significantChoose : Prog isa :=
  .seq (.block [.cmp .r3 (.imm 0)])
    (.ite .eq
      (.seq (.block [.cmp .r0 (.imm 0)])
        (.ite .ne (.block [.mov .r3 (.reg .r2), .mov .r4 (.reg .r0)]) (.block [])))
      (.block []))

def significantByte : Prog isa :=
  .seq (.block [.ldrb .r0 .r1 0])
    (.seq significantChoose (.block [.dp .add .r1 .r1 (.imm 1), .subs .r2 .r2 (.imm 1)]))

/-- The public q at `r1`, `r2 > 0` bytes: `r3` the bytes from its first
nonzero one, `r4` that byte; both zero for zero. -/
def significant : Prog isa :=
  .seq (.block [.mov .r3 (.imm 0), .mov .r4 (.imm 0)]) (.loop significantByte .ne)

/-- `r5 = bits` if the public leading byte `r4` is below `2^k`. -/
def maskStep (k bits : Nat) : Prog isa :=
  .seq (.block [.mov .r0 (.shifted .r4 .lsr k), .cmp .r0 (.imm 0)])
    (.ite .eq (.block [.mov .r5 (.imm (BitVec.ofNat 32 bits))]) (.block []))

/-- The mask of the leading byte's bits, in `r5`. -/
def mask : Prog isa :=
  .seq (.block [.mov .r5 (.imm 255)]) <|
  .seq (maskStep 7 127) <| .seq (maskStep 6 63) <| .seq (maskStep 5 31) <|
  .seq (maskStep 4 15) <| .seq (maskStep 3 7) <| .seq (maskStep 2 3) (maskStep 1 1)

/-- Clear the 32 bytes of the nonce, padding included. -/
def clearNonce : List Instr :=
  .mov .r0 (.imm 0) :: (List.range 8).map fun i => st .r0 (oNonce + 4 * i)

/-- `r0 = 1` exactly when q > 1: at least two significant bytes, or a
leading byte of at least two. -/
def prepareFinish : Prog isa :=
  .seq mask <|
  .seq (.block [st .r5 oMask, .mov .r0 (.shifted .r3 .lsr 1), .mov .r7 (.shifted .r4 .lsr 1),
      .dp .orr .r0 .r0 (.reg .r7), .cmp .r0 (.imm 0)])
    (.ite .eq (.block [.mov .r0 (.imm 0)]) (.block [.mov .r0 (.imm 1)]))

/-- Scan q (`[oQ]` holds its first significant byte afterwards, `[oWidth]`
their count, `[oMask]` the leading byte's mask), and clear the nonce. -/
def prepare : Prog isa :=
  .seq (.block (clearNonce ++ [ld .r1 oKey, ld .r0 (arg aPLen), .dp .add .r1 .r1 (.reg .r0),
      ld .r2 (arg aQLen)])) <|
  .seq significant <|
  .seq (.block [ld .r1 oKey, ld .r0 (arg aPLen), .dp .add .r1 .r1 (.reg .r0), ld .r0 (arg aQLen),
      .dp .add .r1 .r1 (.reg .r0), .dp .sub .r1 .r1 (.reg .r3), st .r1 oQ, st .r3 oWidth])
    prepareFinish

/-- Copy a byte after the masked leading one. -/
def copyByte : List Instr :=
  [.ldrb .r0 .r1 0, .strb .r0 .r4 0, .dp .add .r1 .r1 (.imm 1), .dp .add .r4 .r4 (.imm 1),
    .subs .r2 .r2 (.imm 1)]

/-- The draw's source, its count, and its place right-aligned in the
`q_len`-byte nonce. -/
def copyHeader : List Instr :=
  [ld .r1 (arg aRand), ld .r0 oUsed, .dp .add .r1 .r1 (.reg .r0), ld .r2 oWidth,
    .dp .add .r4 .r11 (.imm (BitVec.ofNat 32 oNonce)), ld .r0 (arg aQLen), .dp .add .r4 .r4 (.reg .r0),
    .dp .sub .r4 .r4 (.reg .r2)]

def copyFirst : List Instr :=
  [.ldrb .r0 .r1 0, ld .r7 oMask, .dp .and .r0 .r0 (.reg .r7), .strb .r0 .r4 0,
    .dp .add .r1 .r1 (.imm 1), .dp .add .r4 .r4 (.imm 1), .subs .r2 .r2 (.imm 1)]

def copyInit : List Instr := copyHeader ++ copyFirst

def copyRest : Prog isa := .ite .ne (.loop (.block copyByte) .ne) (.block [])

/-- One masked draw into the nonce. -/
def copy : Prog isa := .seq (.block copyInit) copyRest

/-- `r3 = 1` iff the nonce byte `r0` is below the modulus byte `r5` and the
incoming borrow `r3`. -/
def borrow : List Instr :=
  [.dp .add .r5 .r5 (.reg .r3), .dp .sub .r0 .r0 (.reg .r5), .mov .r0 (.shifted .r0 .lsr 31), .mov .r3 (.reg .r0)]

/-- One right-to-left byte of the comparison. -/
def rangeByte : List Instr :=
  [.dp .sub .r4 .r4 (.imm 1), .dp .sub .r1 .r1 (.imm 1), .ldrb .r0 .r4 0, .dp .orr .r6 .r6 (.reg .r0),
    .ldrb .r5 .r1 0] ++ borrow ++ [.subs .r2 .r2 (.imm 1)]

/-- The nonce from its end (`r4`), q from its end (`r1`), `r2` bytes. -/
def rangeInit : List Instr :=
  [.dp .add .r4 .r11 (.imm (BitVec.ofNat 32 oNonce)), ld .r0 (arg aQLen), .dp .add .r4 .r4 (.reg .r0),
    ld .r1 oQ, ld .r2 oWidth, .dp .add .r1 .r1 (.reg .r2), .mov .r3 (.imm 0), .mov .r6 (.imm 0)]

/-- Declassify only the conjunction of below q and nonzero: `r3 = 1` iff
the candidate is accepted, then its test (`Z` iff rejected). -/
def rangeFinish : List Instr :=
  [.mov .r0 (.imm 0), .dp .sub .r0 .r0 (.reg .r6), .dp .orr .r0 .r0 (.reg .r6), .mov .r0 (.shifted .r0 .lsr 31),
    .dp .and .r3 .r3 (.reg .r0), .cmp .r3 (.imm 0)]

def inRange : Prog isa :=
  .seq (.block rangeInit) (.seq (.loop (.block rangeByte) .ne) (.block rangeFinish))

/-- Record acceptance, or spend a draw of the budget. -/
def drawFinish : Prog isa :=
  .ite .ne (.block [.mov .r0 (.imm 1), st .r0 oStatus])
    (.seq (.block [ld .r0 oDraws, .subs .r0 .r0 (.imm 1), st .r0 oDraws])
      (.ite .eq (.block [st .r0 oStatus]) (.block [])))

/-- Whether the tape has a complete draw left: `Z` iff it is short (the
carry of `remaining - width`, read by `adc`). -/
def drawHead : List Instr :=
  [ld .r0 (arg aRandLen), ld .r7 oUsed, .dp .sub .r0 .r0 (.reg .r7), ld .r7 oWidth,
    .subs .r0 .r0 (.reg .r7), .mov .r0 (.imm 0), .adc .r0 .r0 (.imm 0), .cmp .r0 (.imm 0)]

/-- One complete draw, or a short tape. Status 4 means keep sampling. -/
def draw : Prog isa :=
  .seq (.block drawHead)
    (.ite .eq (.block [.mov .r0 (.imm 2), st .r0 oStatus])
      (.seq copy
        (.seq (.block [ld .r0 oUsed, ld .r7 oWidth, .dp .add .r0 .r0 (.reg .r7), st .r0 oUsed])
          (.seq inRange drawFinish))))

/-- One budget of 128 draws; the tape's consumption carries over. -/
def sample : Prog isa :=
  .seq (.block [.mov .r0 (.imm 128), st .r0 oDraws, .mov .r0 (.imm 4), st .r0 oStatus])
    (.seq (.loop (.seq draw (.block [ld .r0 oStatus, .cmp .r0 (.imm 4)])) .eq)
      (.block [ld .r0 oStatus]))

end VG.Impl.Dsa.Arm.Random
