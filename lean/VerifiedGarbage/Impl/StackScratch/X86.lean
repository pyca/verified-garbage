import VerifiedGarbage.TCB.X86.Isa

/-!
# A scratch buffer on the stack (x86)

`withStackScratch bytes n c` runs code `c`, written for a function whose
arguments take `n` four-byte slots on the stack followed by a scratch buffer
argument, without that argument: it allocates a frame of `bytes` bytes on the
stack and lays out in it what `c` expects to find at and above `esp` on
entry: a word standing for the return address, a copy of the function's
arguments, and the address of the buffer, which is the rest of the frame.

`withStackScratchWiped bytes n words c` is the same, but zeroes the first
`words` doublewords of the buffer after its code (`wipe`), for a function
whose working space may hold secrets that its caller would otherwise wipe.

`withTagScratch bytes n j c` is for a function one of whose arguments, in
slot `j` of its `n`, is a buffer of working space that also carries a 16-byte
tag, in or out, in its first 16 bytes: it runs `c` as a function whose
argument there is a pointer to the 16-byte tag alone. As `withStackScratch`,
it allocates a frame of `bytes` bytes and lays out in it a word standing for
the return address and a copy of the `n` argument slots; then the tag
pointer (at `esp + 4 + 4n`), and the buffer, which is the rest of the frame
(from `esp + 8 + 4n`). It copies the tag's 16 bytes into the buffer and
passes the buffer in slot `j` of the copy before the code (`tagSetup`), and
copies the buffer's first 16 bytes back to the tag after it (`tagOut`),
through `ecx` and `xmm0`, which hold no result (`eax` and `edx` do).
-/

namespace VG.Impl.StackScratch.X86

open VG.X86

/-- `mov eax, [esp + bytes + 4 + 4j]; mov [esp + 4 + 4j], eax`: copy argument
slot `j` from the caller's frame into this one. -/
def copyArg (bytes j : Nat) : List Instr :=
  [.mov .eax (.mem ⟨.esp, bytes + 4 + 4 * j⟩), .store ⟨.esp, 4 + 4 * j⟩ .eax]

/-- Copy the `n` argument slots, and pass the buffer, at `esp + 8 + 4n`, as
the next argument. -/
def setArgs (bytes n : Nat) : List Instr :=
  (List.range n).flatMap (copyArg bytes) ++
    [.mov .eax (.reg .esp), .alu .add .eax (.imm (BitVec.ofNat 32 (8 + 4 * n))),
      .store ⟨.esp, 4 + 4 * n⟩ .eax]

/-- `c`, with its scratch buffer in a frame of `bytes` bytes on the stack. -/
def withStackScratch (bytes n : Nat) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block (setArgs bytes n)) c) (.free bytes)

/-- `mov [esp + off + 4k], ecx` for each `k < words`. -/
def wipeStores (off words : Nat) : List Instr :=
  (List.range words).map fun k => .store ⟨.esp, off + 4 * k⟩ .ecx

/-- Zeroes the `words` doublewords at `esp + off`, through `ecx`. -/
def wipe (off words : Nat) : List Instr := .mov .ecx (.imm 0) :: wipeStores off words

/-- `withStackScratch`, zeroing the first `words` doublewords of the buffer
(at `esp + 8 + 4n`) after the code. -/
def withStackScratchWiped (bytes n words : Nat) (c : Prog isa) : Prog isa :=
  withStackScratch bytes n (.seq c (.block (wipe (8 + 4 * n) words)))

/-- `ecx :=` the tag pointer, from argument slot `j` of the caller's frame. -/
def loadTag (bytes j : Nat) : List Instr := [.mov .ecx (.mem ⟨.esp, bytes + 4 + 4 * j⟩)]

/-- Save the tag pointer (in `ecx`) at `esp + 4 + 4n`, and copy the tag's 16
bytes to the buffer at `esp + 8 + 4n`, through `xmm0`. -/
def tagIn (n : Nat) : List Instr :=
  [.store ⟨.esp, 4 + 4 * n⟩ .ecx, .movdquLoad .xmm0 ⟨.ecx, 0⟩, .movdquStore ⟨.esp, 8 + 4 * n⟩ .xmm0]

/-- Pass the buffer, at `esp + 8 + 4n`, in place of the tag pointer: in the
copy of argument slot `j`. -/
def pointTag (n j : Nat) : List Instr :=
  [.mov .eax (.reg .esp), .alu .add .eax (.imm (BitVec.ofNat 32 (8 + 4 * n))),
    .store ⟨.esp, 4 + 4 * j⟩ .eax]

/-- Copy the `n` argument slots, save the tag pointer (slot `j`), copy the
tag into the buffer and pass the buffer in the tag pointer's place. -/
def tagSetup (bytes n j : Nat) : List Instr :=
  (List.range n).flatMap (copyArg bytes) ++ loadTag bytes j ++ tagIn n ++ pointTag n j

/-- Copy the buffer's first 16 bytes back to the tag, whose pointer is at
`esp + 4 + 4n`, through `ecx` and `xmm0`. -/
def tagOut (n : Nat) : List Instr :=
  [.mov .ecx (.mem ⟨.esp, 4 + 4 * n⟩), .movdquLoad .xmm0 ⟨.esp, 8 + 4 * n⟩,
    .movdquStore ⟨.ecx, 0⟩ .xmm0]

/-- `c`, whose working space in argument slot `j` (of `n`) also carries a
16-byte tag, run with a pointer to the tag alone there, the working space in
a frame of `bytes` bytes on the stack, after a copy of the `n` argument slots
and the tag pointer. -/
def withTagScratch (bytes n j : Nat) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block (tagSetup bytes n j)) (.seq c (.block (tagOut n))))
    (.free bytes)

end VG.Impl.StackScratch.X86
