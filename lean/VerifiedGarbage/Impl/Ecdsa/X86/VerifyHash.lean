module

public import VerifiedGarbage.Impl.StackScratch.X86

/-!
# ECDSA verification of the hash function's output on x86 (32-bit)

`vg_ecdsa_<curve>_verify(public, digest, digest_len, sig, scratch) -> eax`
(`Instance.verifyHashContract`, `Spec/Ecdsa/Verify/Generic.lean`). Every
argument is on the stack. In a frame of `frameBytes` bytes
(`withStackScratch`, which copies the five argument slots into the frame and
passes the address of a buffer of `bufBytes` bytes after them as a sixth
argument, at `esp + 24`; the buffer itself is at `esp + bufOff`), the `len`
bytes of the hash that the verification of a curve takes
(`Proof.Ecdsa.Verify.fixedDigest`), then that verification, `core`, run with
them in place of the hash (`hashed`):

1. if `digest_len ≥ len`, the hash's leftmost `len` bytes copied to the
   buffer (`copyLong`);
2. otherwise 72 zero bytes stored, and the hash copied to the `len -
   digest_len` bytes after the buffer's start (`copyLoop`, if `digest_len`
   is not zero; `ecx` the source, `edx` the destination, until `edx` reaches
   the buffer's byte `len`); for a curve whose `n` has 7 bits fewer than
   `8 len` (`wide`, P-521), the `len + 1` bytes then shifted right by one
   bit, byte `i` becoming the low bit of byte `i` and the seven high bits of
   byte `i + 1` (`shiftBytes`), so that the `len` bytes are the hash's
   integer shifted left by 7 bits;
3. `core`'s arguments, in the slots `core` reads: `public` stays at
   `esp + 4`, the buffer's address goes to `esp + 8`, `sig` to `esp + 12`
   and `scratch` to `esp + 16` (`args`).

Only `eax`, `ecx` and `edx`, which the caller does not expect kept, are
written before `core`. The hash, its length and the pointers are public, so
the branches and the loop may depend on them.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.X86.VerifyHash

open VG.X86

/-- The buffer's bytes: at least `len + 1` (67 for P-521) and 72 (the zeros),
a multiple of 4. -/
def bufBytes : Nat := 80

/-- The argument slots of `vg_ecdsa_<curve>_verify`: `public`, `digest`,
`digest_len`, `sig`, `scratch`. -/
def slots : Nat := 5

/-- The buffer's offset from `esp` in the frame (`setArgs`). -/
def bufOff : Nat := 8 + 4 * slots

/-- The frame's bytes: the return address's word, the five argument slots,
the buffer's address, then the buffer (`Verified.stackScratchL`'s bound). -/
def frameBytes : Nat := bufOff + bufBytes

/-- Byte `i` of the buffer. -/
def bufAt (i : Nat) : MemOp := ⟨.esp, bufOff + i⟩

/-- The leftmost `len` bytes of the hash (its address in `ecx`), through `eax`. -/
def copyLong (len : Nat) : List Instr :=
  .mov .ecx (.mem ⟨.esp, 8⟩) :: (List.range len).flatMap fun i =>
    [.movzx8 .eax ⟨.ecx, i⟩, .store8 (bufAt i) .al]

/-- 72 zero bytes at the buffer's start, through `eax`. -/
def zeros : List Instr :=
  .mov .eax (.imm 0) :: (List.range 18).map fun k => .store (bufAt (4 * k)) .eax

/-- The hash's `digest_len` bytes from `ecx` to `edx`, until `edx` is at the
buffer's byte `len`. -/
def copyLoop (len : Nat) : Prog isa :=
  .loop (.block [.movzx8 .eax ⟨.ecx, 0⟩, .store8 ⟨.edx, 0⟩ .al,
    .alu .add .ecx (.imm 1), .alu .add .edx (.imm 1),
    .mov .eax (.reg .edx), .alu .sub .eax (.reg .esp),
    .alu .cmp .eax (.imm (BitVec.ofNat 32 (bufOff + len)))]) .ne

/-- Byte `i` of the `len` bytes becomes the low bit of byte `i` and the
seven high bits of byte `i + 1`: `(b << 7) + (c >> 1)`, through `eax` and
`ecx` (seven doublings for the shift left, which the model has no
instruction for). -/
def shiftByte (i : Nat) : List Instr :=
  [.movzx8 .eax (bufAt i), .movzx8 .ecx (bufAt (i + 1))] ++
    List.replicate 7 (.alu .add .eax (.reg .eax)) ++
    [.shift .shr .ecx 1, .alu .add .eax (.reg .ecx), .store8 (bufAt i) .al]

/-- The shift of the `len + 1` bytes. -/
def shiftBytes (len : Nat) : List Instr := (List.range len).flatMap shiftByte

/-- A hash shorter than `len` bytes: zeros, the hash after `len - digest_len`
of them, and, if `wide`, the shift. -/
def short (len : Nat) (wide : Bool) : Prog isa :=
  .seq (.block (zeros ++
    [.mov .ecx (.mem ⟨.esp, 8⟩), .mov .edx (.reg .esp),
      .alu .add .edx (.imm (BitVec.ofNat 32 (bufOff + len))), .mov .eax (.mem ⟨.esp, 12⟩),
      .alu .sub .edx (.reg .eax), .alu .test .eax (.reg .eax)])) <|
  .seq (.ite .e (.block []) (copyLoop len)) <|
  .block (if wide then shiftBytes len else [])

/-- The `len` bytes of the hash (`digest` at `esp + 8`, `digest_len` bytes
at `esp + 12`) in the buffer. -/
def convert (len : Nat) (wide : Bool) : Prog isa :=
  .seq (.block [.mov .eax (.mem ⟨.esp, 12⟩), .alu .cmp .eax (.imm (BitVec.ofNat 32 len))]) <|
  .ite .b (short len wide) (.block (copyLong len))

/-- The arguments of `core`: the buffer's address (at `esp + 24`) at
`esp + 8`, `sig` at `esp + 12`, `scratch` at `esp + 16`. -/
def args : List Instr :=
  [.mov .eax (.mem ⟨.esp, 24⟩), .store ⟨.esp, 8⟩ .eax,
    .mov .eax (.mem ⟨.esp, 16⟩), .store ⟨.esp, 12⟩ .eax,
    .mov .eax (.mem ⟨.esp, 20⟩), .store ⟨.esp, 16⟩ .eax]

/-- The conversion, then `core` with the buffer for the hash. -/
def hashed (len : Nat) (wide : Bool) (core : Prog isa) : Prog isa :=
  .seq (convert len wide) (.seq (.block args) core)

/-- `vg_ecdsa_<curve>_verify`, with the buffer in a frame on the stack. -/
def verifyHash (len : Nat) (wide : Bool) (core : Prog isa) : Prog isa :=
  Impl.StackScratch.X86.withStackScratch frameBytes slots (hashed len wide core)

end VG.Impl.Ecdsa.X86.VerifyHash
