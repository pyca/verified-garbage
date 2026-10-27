module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentFilter
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentImport
public import VerifiedGarbage.Impl.RsaKeyGen.X86.FermatExponent
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowWord
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Result
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Setup

/-! # The public exponent's coprimality check at a run-time width

`CandidateExponent.code` without a copy per width: the candidate's length
`len = 8 w` is read from the header (byte 4), and its saved copy, array 5 at
`256 + 5 (len + 16)`, is addressed through a pointer computed from it. The
candidate itself, array 0, is at the fixed offset 256. The copies run over
`2 w` native words through pointers (`copy`), and the remainder's word
pointer and count (`Mod64.array`'s frame) and the 65537 filter's bounds are
computed from `len`. Only `len` and the public exponent choose branches and
loop counts.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.Impl.Mont.X86

/-- `r := edi + 256 + 5 (len + 16)`, the saved candidate (array 5), for
`len` at header byte 4; `t` is clobbered. -/
def savedPtr (r t : Reg) : List Instr :=
  [.mov r (.mem (sc 4)), .alu .add r (.imm 16), .mov t (.reg r), .alu .add r (.reg r),
    .alu .add r (.reg r), .alu .add r (.reg t), .alu .add r (.imm 256), .alu .add r (.reg .edi)]

/-- `[ebx] := [ebp]` (the mask `ecx` all ones), `esi` native words. -/
def copyLoop : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .ebp 0)), .alu .xor .eax (.mem (at_ .ebx 0)),
    .alu .and .eax (.reg .ecx), .alu .xor .eax (.mem (at_ .ebx 0)), .store (at_ .ebx 0) .eax,
    .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4), .alu .sub .esi (.imm 1)]) .ne

/-- `esi := 2 w`, the candidate's native words, and the mask `ecx` of a copy. -/
def copyCount : List Instr :=
  [.mov .esi (.mem (sc 4)), .shift .shr .esi 2, .mov .ecx (.imm (BitVec.allOnes 32))]

/-- `[ebx] := [ebx] − 1`. -/
def decrementAt : List Instr := [.mov .eax (.mem (at_ .ebx 0)), .alu .sub .eax (.imm 1), .store (at_ .ebx 0) .eax]

/-- The copy from array 0 to array 5. -/
def saveSetup : List Instr :=
  [.mov .ebp (.reg .edi), .alu .add .ebp (.imm 256)] ++ savedPtr .ebx .edx ++ copyCount

/-- The candidate saved into array 5 and decremented there. -/
def save : Prog isa :=
  .seq (.block saveSetup) (.seq copyLoop (.seq (.block (savedPtr .ebx .edx)) (.block decrementAt)))

/-- The copy from array 5 to array 0. -/
def restoreSetup : List Instr :=
  [.mov .ebx (.reg .edi), .alu .add .ebx (.imm 256)] ++ savedPtr .ebp .edx ++ copyCount

/-- The candidate restored from array 5 and incremented. -/
def restore : Prog isa :=
  .seq (.block restoreSetup) (.seq copyLoop (.block (VG.Impl.RsaKeyGen.X86.LowWord.increment 256)))

/-- The 65537 filter over array 5: its base in `edi` and its end in the
trial frame, the workspace pointer saved below them. -/
def fastArgs : List Instr :=
  savedPtr .eax .edx ++ [.mov .ecx (.mem (sc 4)), .store (at_ .esp 0) .edi, .mov .edi (.reg .eax),
    .alu .add .eax (.reg .ecx), .store (at_ .esp 4) .eax]

def fast : Prog isa :=
  .frame (.alloc 20)
    (.seq (.block fastArgs)
      (.seq (FermatExponent.code 4) (.block [.mov .edi (.mem (at_ .esp 0))]))) (.free 20)

/-- `Mod64.array` over array 5: the pointer to its top word, `len − 4` bytes
above its base, and its count of `len / 4` words. -/
def arrayInit : List Instr :=
  savedPtr .eax .edx ++ [.mov .edx (.mem (sc 4)), .alu .add .eax (.reg .edx), .alu .sub .eax (.imm 4),
    .store (Mod64.stack 0) .eax, .shift .shr .edx 2, .store (Mod64.stack 4) .edx] ++ Mod64.zeroRemainder

def array : Prog isa := .seq (.block arrayInit) (.loop (Mod64.arrayStep 128) .ne)

def general : Prog isa :=
  .seq (.frame (.alloc 20) array (.free 20))
    (.seq (.block (Gcd64.setup 128)) (.seq Gcd64.code (.seq restore (.block Gcd64.result))))

def filter : Prog isa :=
  .seq (.block ExponentFilter.parity) (.ite .e (.block [.mov .eax (.imm 0)])
    (.seq (.block (ExponentFilter.equal 1)) (.ite .e (.block [.mov .eax (.imm 1)])
      (.seq (.block (ExponentFilter.equal 65537)) (.ite .e fast general)))))

/-- `eax := [gcd(c − 1, e) = 1]`, with `c − 1` left in array 5. -/
def code : Prog isa := .seq save (.seq ExponentImport.code filter)

end VG.Impl.RsaKeyGen.X86.ExponentRt
