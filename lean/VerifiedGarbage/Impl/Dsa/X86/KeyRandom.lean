module

public import VerifiedGarbage.Impl.Mont.X86

/-!
# Bounded DSA key sampling on x86

An internal program for a caller with a stack frame: the frame's first
eleven words are the outgoing arguments of a call, then come the slots below,
and the caller's eleven arguments lie above the frame (`arg`). `prepare`
scans the public q and clears the padded scalar. `sample` consumes at most
128 complete draws from the tape at `rand`, from the offset `[oUsed]`, and
returns status 1 (accepted), 2 (short tape) or 0 (draw limit). The caller
must skip `sample` if `prepare` returns zero.

Every branch is on public q, the tape's length, the count of draws and the
accept bit of a draw; a candidate's bytes reach no branch or address.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.KeyRandom
open VG VG.X86 VG.Impl.Mont.X86

/-- Slots of the frame, after eleven outgoing argument words. -/
def oSaveEbx : Nat := 44
def oSaveEsi : Nat := 48
def oSaveEdi : Nat := 52
def oSaveEbp : Nat := 56
def oUsed : Nat := 60
def oAttempts : Nat := 64
def oDraws : Nat := 68
def oQ : Nat := 72
def oWidth : Nat := 76
def oMask : Nat := 80
def oStatus : Nat := 84
def oNonce : Nat := 88
def frameBytes : Nat := 120

def sp (offset : Nat) : MemOp := at_ .esp offset

/-- The caller's argument `j`, above the frame and the return address. -/
def arg (j : Nat) : MemOp := sp (frameBytes + 4 + 4 * j)

/-- Arguments: `out`, `out_len`, `used`, `key`, `key_len`, `p_len`, `q_len`,
`rand`, `rand_len`, `scratch`, `scratch_len`. -/
def aOut : Nat := 0
def aOutLen : Nat := 1
def aUsed : Nat := 2
def aKey : Nat := 3
def aKeyLen : Nat := 4
def aPLen : Nat := 5
def aQLen : Nat := 6
def aRand : Nat := 7
def aRandLen : Nat := 8
def aScratch : Nat := 9
def aScratchLen : Nat := 10

/-- Record the first nonzero byte of the scan (in `edx`), and the bytes
from it on (in `ebx`), if none was found yet. -/
def significantChoose : Prog isa :=
  .seq (.block [.alu .test .ebx (.reg .ebx)])
    (.ite .e
      (.seq (.block [.alu .test .eax (.reg .eax)])
        (.ite .ne (.block [.mov .ebx (.reg .ecx), .mov .edx (.reg .eax)]) (.block [])))
      (.block []))

def significantByte : Prog isa :=
  .seq (.block [.movzx8 .eax (at_ .esi 0)])
    (.seq significantChoose (.block [.alu .add .esi (.imm 1), .alu .sub .ecx (.imm 1)]))

/-- The public q at `esi`, `ecx > 0` bytes: `ebx` the bytes from its first
nonzero one, `edx` that byte; both zero for zero. -/
def significant : Prog isa :=
  .seq (.block [.mov .ebx (.imm 0), .mov .edx (.imm 0)]) (.loop significantByte .ne)

/-- `ebp = bits` if the public leading byte `edx` is below `threshold`. -/
def maskStep (threshold bits : Nat) : Prog isa :=
  .seq (.block [.alu .cmp .edx (.imm (BitVec.ofNat 32 threshold))])
    (.ite .b (.block [.mov .ebp (.imm (BitVec.ofNat 32 bits))]) (.block []))

/-- The mask of the leading byte's bits, in `ebp`. -/
def mask : Prog isa :=
  .seq (.block [.mov .ebp (.imm 255)]) <|
  .seq (maskStep 128 127) <| .seq (maskStep 64 63) <| .seq (maskStep 32 31) <|
  .seq (maskStep 16 15) <| .seq (maskStep 8 7) <| .seq (maskStep 4 3) (maskStep 2 1)

/-- Clear the 32 bytes of the scalar, padding included. -/
def clearNonce : List Instr :=
  [.mov .eax (.imm 0), .store (sp oNonce) .eax, .store (sp (oNonce + 4)) .eax,
    .store (sp (oNonce + 8)) .eax, .store (sp (oNonce + 12)) .eax,
    .store (sp (oNonce + 16)) .eax, .store (sp (oNonce + 20)) .eax,
    .store (sp (oNonce + 24)) .eax, .store (sp (oNonce + 28)) .eax]

/-- `eax = 1` exactly when q > 1: at least two significant bytes, or a
leading byte of at least two. -/
def prepareFinish : Prog isa :=
  .seq mask <|
  .seq (.block [.store (sp oMask) .ebp, .mov .eax (.imm 0), .alu .cmp .ebx (.imm 2)])
    (.seq (.ite .ae (.block [.mov .eax (.imm 1)]) (.block []))
      (.seq (.block [.alu .cmp .edx (.imm 2)]) (.ite .ae (.block [.mov .eax (.imm 1)]) (.block []))))

/-- Scan q (`[oQ]` holds its first significant byte afterwards, `[oWidth]`
their count, `[oMask]` the leading byte's mask), and clear the scalar. -/
def prepare : Prog isa :=
  .seq (.block (clearNonce ++ [.mov .esi (.mem (arg aKey)), .alu .add .esi (.mem (arg aPLen)),
      .mov .ecx (.mem (arg aQLen))])) <|
  .seq significant <|
  .seq (.block [.mov .esi (.mem (arg aKey)), .alu .add .esi (.mem (arg aPLen)),
      .alu .add .esi (.mem (arg aQLen)), .alu .sub .esi (.reg .ebx),
      .store (sp oQ) .esi, .store (sp oWidth) .ebx])
    prepareFinish

/-- Copy a byte after the masked leading one. -/
def copyByte : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .store8 (at_ .edx 0) .al,
    .alu .add .esi (.imm 1), .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]

/-- The draw's source, its count, and its place right-aligned in the
`q_len`-byte scalar. -/
def copyHeader : List Instr :=
  [.mov .esi (.mem (arg aRand)), .alu .add .esi (.mem (sp oUsed)),
    .mov .ecx (.mem (sp oWidth)), .mov .edx (.reg .esp), .alu .add .edx (.imm (BitVec.ofNat 32 oNonce)),
    .alu .add .edx (.mem (arg aQLen)), .alu .sub .edx (.reg .ecx)]

def copyFirst : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .alu .and .eax (.mem (sp oMask)), .store8 (at_ .edx 0) .al,
    .alu .add .esi (.imm 1), .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]

def copyInit : List Instr := copyHeader ++ copyFirst

def copyRest : Prog isa := .ite .ne (.loop (.block copyByte) .ne) (.block [])

/-- One masked draw into the scalar. -/
def copy : Prog isa := .seq (.block copyInit) copyRest

/-- `ebx = 1` iff the scalar byte `eax` is below the modulus byte `ebp` and
the incoming borrow `ebx`. -/
def borrow : List Instr :=
  [.alu .add .ebp (.reg .ebx), .alu .sub .eax (.reg .ebp), .shift .shr .eax 31, .mov .ebx (.reg .eax)]

/-- One right-to-left byte of the comparison. -/
def rangeByte : List Instr :=
  [.alu .sub .edx (.imm 1), .alu .sub .esi (.imm 1),
    .movzx8 .eax (at_ .edx 0), .alu .or .edi (.reg .eax), .movzx8 .ebp (at_ .esi 0)] ++
  borrow ++ [.alu .sub .ecx (.imm 1)]

/-- The scalar from its end (`edx`), q from its end (`esi`), `ecx` bytes. -/
def rangeInit : List Instr :=
  [.mov .edx (.reg .esp), .alu .add .edx (.imm (BitVec.ofNat 32 oNonce)), .alu .add .edx (.mem (arg aQLen)),
    .mov .esi (.mem (sp oQ)), .mov .ecx (.mem (sp oWidth)), .alu .add .esi (.reg .ecx),
    .mov .ebx (.imm 0), .mov .edi (.imm 0)]

/-- Declassify only the conjunction of below q and nonzero: `ebx = 1` iff
the candidate is accepted, then its test. -/
def rangeFinish : List Instr :=
  [.mov .eax (.imm 0), .alu .sub .eax (.reg .edi), .alu .sbb .eax (.reg .eax),
    .alu .and .ebx (.reg .eax), .alu .test .ebx (.reg .ebx)]

def inRange : Prog isa :=
  .seq (.block rangeInit) (.seq (.loop (.block rangeByte) .ne) (.block rangeFinish))

/-- Record acceptance, or spend a draw of the budget. -/
def drawFinish : Prog isa :=
  .ite .ne (.block [.mov .eax (.imm 1), .store (sp oStatus) .eax])
    (.seq (.block [.mov .eax (.mem (sp oDraws)), .alu .sub .eax (.imm 1), .store (sp oDraws) .eax])
      (.ite .e (.block [.store (sp oStatus) .eax]) (.block [])))

/-- One complete draw, or a short tape. Status 4 means keep sampling. -/
def draw : Prog isa :=
  .seq (.block [.mov .eax (.mem (arg aRandLen)), .alu .sub .eax (.mem (sp oUsed)),
      .alu .cmp .eax (.mem (sp oWidth))])
    (.ite .b (.block [.mov .eax (.imm 2), .store (sp oStatus) .eax])
      (.seq copy
        (.seq (.block [.mov .eax (.mem (sp oUsed)), .alu .add .eax (.mem (sp oWidth)),
            .store (sp oUsed) .eax])
          (.seq inRange drawFinish))))

/-- One budget of 128 draws; the tape's consumption carries over. -/
def sample : Prog isa :=
  .seq (.block [.mov .eax (.imm 128), .store (sp oDraws) .eax, .mov .eax (.imm 4), .store (sp oStatus) .eax])
    (.seq (.loop (.seq draw (.block [.mov .eax (.mem (sp oStatus)), .alu .cmp .eax (.imm 4)])) .e)
      (.block [.mov .eax (.mem (sp oStatus))]))

end VG.Impl.Dsa.X86.KeyRandom
