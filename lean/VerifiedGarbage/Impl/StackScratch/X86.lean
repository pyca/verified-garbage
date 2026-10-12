module

public import VerifiedGarbage.TCB.X86.Isa

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
-/

@[expose] public section

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

end VG.Impl.StackScratch.X86
