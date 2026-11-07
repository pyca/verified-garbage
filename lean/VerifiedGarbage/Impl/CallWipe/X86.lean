module

public import VerifiedGarbage.TCB.X86.Isa

/-!
# A call that wipes part of a buffer afterwards (x86, 32-bit)

`callWipe m j n name body zname zcode` calls the function `name`, whose code
is `body`, with the arguments its caller was given, which take `m` four-byte
slots on the stack, then zeroes the first `n` bytes of the buffer whose
address is in slot `j` by calling the zeroize function `zname`, whose code is
`zcode`, and returns what `name` returned, in `edx:eax`.

Its frame of `frameSize m` bytes holds, at `esp`, the arguments of each
call: first a copy of the caller's, then the buffer's address and `n`; and,
above them, `name`'s result across the second call. It reads the buffer's
address again from the caller's arguments, which `name` cannot write.
-/

@[expose] public section

namespace VG.Impl.CallWipe.X86

open VG.X86

/-- The argument slots the frame holds: the callee's, and at least the
zeroize function's two. -/
def argWords (m : Nat) : Nat := max m 2

/-- The frame: the argument slots and the two words of the result. -/
def frameSize (m : Nat) : Nat := 4 * argWords m + 8

/-- `mov eax, [esp + bytes + 4 + 4k]; mov [esp + 4k], eax`: copy argument
slot `k` from the caller's frame into this one. -/
def copyArg (bytes k : Nat) : List Instr :=
  [.mov .eax (.mem ⟨.esp, bytes + 4 + 4 * k⟩), .store ⟨.esp, 4 * k⟩ .eax]

/-- Copy the `m` argument slots. -/
def copyArgs (bytes m : Nat) : List Instr := (List.range m).flatMap (copyArg bytes)

/-- `mov [esp + 4M], eax; mov [esp + 4M + 4], edx; mov eax, [esp + bytes + 4 + 4j];
mov [esp], eax; mov eax, n; mov [esp + 4], eax`: keep the result, and pass
the buffer's address and `n` to the zeroize function. -/
def zeroArgs (m j n : Nat) : List Instr :=
  [.store ⟨.esp, 4 * argWords m⟩ .eax, .store ⟨.esp, 4 * argWords m + 4⟩ .edx,
    .mov .eax (.mem ⟨.esp, frameSize m + 4 + 4 * j⟩), .store ⟨.esp, 0⟩ .eax,
    .mov .eax (.imm (BitVec.ofNat 32 n)), .store ⟨.esp, 4⟩ .eax]

/-- `mov eax, [esp + 4M]; mov edx, [esp + 4M + 4]`: restore the result. -/
def restoreRet (m : Nat) : List Instr :=
  [.mov .eax (.mem ⟨.esp, 4 * argWords m⟩), .mov .edx (.mem ⟨.esp, 4 * argWords m + 4⟩)]

/-- A call of `name`, whose code is `body`, then of the zeroize function
`zname`, whose code is `zcode`, on the first `n` bytes of the buffer whose
address is in argument slot `j` of the `m`, returning `name`'s result. -/
def callWipe (m j n : Nat) (name : String) (body : Prog isa) (zname : String) (zcode : Prog isa) :
    Prog isa :=
  .frame (.alloc (frameSize m))
    (.seq (.block (copyArgs (frameSize m) m))
      (.seq (.call name body)
        (.seq (.block (zeroArgs m j n))
          (.seq (.call zname zcode) (.block (restoreRet m))))))
    (.free (frameSize m))

end VG.Impl.CallWipe.X86
