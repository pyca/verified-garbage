module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Impl.Bignum.Arm.MaskOutput

/-! # ARMv7 RSA private-key precomputation entry point

AAPCS arguments are (pre, pre_len, n, n_len, p, p_len, q, q_len, scratch,
scratch_len). The first frame saves the caller's registers and `pre` is
cleared. A second frame, pushed from registers, then holds the stack
arguments of a private CRT call (`CrtFn`): the input and the coefficient are the cleared
`pre`, the exponents are the factors themselves, so that the CRT's validation
accepts exactly when `p q = n` for a valid `n`. Inside the CRT's own frame,
after the validation, each factor is prepared in the narrow workspace at its
own width, `max(2, ⌈len/8⌉)`, and its `R² mod p` exported to `pre` after the
modulus' values; the main workspace then gives `R² mod n` the same way, the
public precomputation's export writes `n` and it, and the secret acceptance
bit masks all of `pre`. The only branch tests the public modulus.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm.PrivPreFn
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

/-- `pre_len` 64-bit words are `2 pre_len` words of 32 bits, from `pre`. -/
def zeroArgs : List Instr := [.mov .lr (.shifted .r1 .lsl 1), .mov .r3 (.imm 0)]

/-- The private CRT's stack arguments, in the registers a second frame
pushes: the input (`pre`, `n_len` bytes), `p`, `q`, `p` and `q` again as the
exponents, the coefficient (`pre`, `p_len` bytes) and the workspace. -/
def loadArgs : List Instr :=
  [.ldrSp .r0 0, .ldrSp .r1 12, .ldrSp .r2 56, .ldrSp .r3 60, .ldrSp .r4 64, .ldrSp .r5 68,
   .mov .r6 (.reg .r2), .mov .r7 (.reg .r3), .mov .r8 (.reg .r4), .mov .r9 (.reg .r5),
   .mov .r10 (.reg .r0), .mov .r11 (.reg .r3), .ldrSp .r12 72]
/-- `pre`, `n` and `n_len`, the CRT's register arguments, from the first frame. -/
def callArgs : List Instr := [.ldrSp .r0 56, .ldrSp .r2 64, .ldrSp .r3 68]

/-- A factor's Montgomery width, `max(2, ⌈len/8⌉)` limbs for the byte length
in the given frame slot (nonzero), into r7; r3 zero. -/
def primeWidth (lenSlot : Nat) : List Instr :=
  [.ldrSp .r7 lenSlot, .dp .add .r7 .r7 (.imm 7), .mov .r7 (.shifted .r7 .lsr 3),
   .dp .sub .r1 .r7 (.imm 2), .mov .r1 (.shifted .r1 .lsr 31), .dp .add .r7 .r7 (.reg .r1),
   .mov .r3 (.imm 0)]
/-- Set up and select the narrow workspace at a factor's own width. -/
def enterFactor (lenSlot : Nat) : Prog isa :=
  .seq (.block narrowAddress) (.seq (.block (primeWidth lenSlot)) (.seq setup (.block activateWorkspace)))

/-- `pre + 16 w` into r4, for the modulus' `w` limbs in the main header. -/
def modulusEnd : List Instr :=
  [.ldrSp .r4 4, .ldrSp .r1 8, .ldr .r1 .r1 48, .dp .add .r4 .r4 (.shifted .r1 .lsl 4)]
/-- p's values follow the modulus'; array 4 is exported. -/
def pDest : List Instr := modulusEnd ++ [.mov .r2 (.imm 4)]
/-- q's values follow p's. -/
def qDest : List Instr :=
  modulusEnd ++ primeWidth 68 ++ [.dp .add .r4 .r4 (.shifted .r7 .lsl 3), .mov .r2 (.imm 4)]

/-- A factor, from its saved argument, prepared at its own width, and its
`R² mod p` exported to `pre`. -/
def phase (primeSlot : Nat) (dest : List Instr) : Prog isa :=
  .seq (enterFactor (primeSlot + 4)) (.seq (narrowPrime primeSlot) (.seq (.block dest) exportArray))

/-- `pre` in r4 and its `16 w + 8 w_p + 8 w_q` bytes in r6. -/
def maskArgs : List Instr :=
  [.ldrSp .r1 8, .ldr .r1 .r1 48, .mov .r6 (.shifted .r1 .lsl 4)] ++ primeWidth 68 ++
  [.dp .add .r6 .r6 (.shifted .r7 .lsl 3)] ++ primeWidth 76 ++
  [.dp .add .r6 .r6 (.shifted .r7 .lsl 3), .ldrSp .r4 4]

/-- `R² mod n` in the main workspace, `n` and it exported, and `pre` masked. -/
def modulusPart : Prog isa :=
  .seq selectMain (.seq prepareAcceptedPrime (.seq (.block [.ldrSp .r4 4])
    (.seq precomputeOut (.seq (.block maskArgs) maskOutput))))

def valid : Prog isa :=
  .seq CrtFn.prepare (.seq CrtFn.validate (.seq (phase 64 pDest) (.seq (phase 72 qDest) modulusPart)))
def body : Prog isa := .seq (.block modulusCheck) (.ite .eq valid (.block [.mov .r0 (.imm 0)]))
def crtFrame : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq (.block CrtFn.entry) (.seq body (.block PcFn.restore))) (.pop .r12 56)

def argsFrame : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq (.block callArgs) crtFrame) (.pop .r12 56)

def code : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq (.block zeroArgs) (.seq zero (.seq (.block loadArgs) (.seq argsFrame (.block PcFn.restore)))))
    (.pop .r12 56)

end VG.Impl.Bignum.Arm.PrivPreFn
