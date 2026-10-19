module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Sign
public import VerifiedGarbage.Impl.Bignum.X86.CopyBytes

/-! # Branchless implicit-rejection selection on i686

The local frame starts with eighty bytes for the checked private call's
arguments. Persistent values follow it. The candidate-length scan and
message selection use only public addresses and public loop counters;
secret values select bytes and lengths through masks.
-/

@[expose] public section
namespace VG.Impl.RsaPkcs1Enc.X86.Decrypt
open VG VG.X86

def frameBytes : Nat := 160

def oR : Nat := 80
def oI : Nat := 84
def oNB : Nat := 88
def oAL : Nat := 92
def oMK : Nat := 96
def oValidMask : Nat := 108
def oOKMask : Nat := 112
def oCut : Nat := 116

def sSt : Nat := 0
def sOuter : Nat := 96
def sMsg : Nat := 192
def sDH : Nat := 208
def sKDK : Nat := 240
def sCL : Nat := 272
def sAM : Nat := 528
def sD : Nat := 1552
def sHash : Nat := 3072

def stackAt (d : Nat) : MemOp := ⟨.esp, d⟩
def incoming (j : Nat) : MemOp := stackAt (frameBytes + 20 + 4 * j)

def copyArg (j i : Nat) : List Instr :=
  [.mov .eax (.mem (incoming j)), .store (stackAt (4 * i)) .eax]

def immArg (v i : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 v)), .store (stackAt (4 * i)) .eax]

def scratchArg (d i : Nat) : List Instr :=
  [.mov .eax (.mem (incoming 21)), .alu .add .eax (.imm (BitVec.ofNat 32 d)), .store (stackAt (4 * i)) .eax]

def privateInputSlot (j : Nat) : Nat :=
  match j with
  | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 9 | 7 => 4 | _ => j + 3

/-- All twenty cdecl arguments to checked private RSA. -/
def privArgs : List Instr :=
  (List.range 20).flatMap fun j => copyArg (privateInputSlot j) j

def dZero : List Instr :=
  [.store (stackAt oR) .eax, .mov .esi (.mem (incoming 21)), .alu .add .esi (.imm (BitVec.ofNat 32 sD)),
    .mov .ecx (.mem (incoming 4)), .mov .eax (.imm 0)]

def dCopy : List Instr :=
  [.mov .ebx (.mem (incoming 21)), .alu .add .ebx (.imm (BitVec.ofNat 32 sD)),
    .mov .eax (.mem (incoming 4)), .alu .add .ebx (.reg .eax),
    .mov .ecx (.mem (incoming 8)), .alu .sub .ebx (.reg .ecx), .mov .esi (.mem (incoming 7))]

structure Fns where
  initN : String
  initC : Prog isa
  updN : String
  updC : Prog isa
  finN : String
  finC : Prog isa
  hiN : String
  hiC : Prog isa
  hfN : String
  hfC : Prog isa

def callAfter (args : List Instr) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block args) (.call name code)

def shaInitArgs : List Instr := scratchArg sSt 0

def shaUpdArgs : List Instr := scratchArg sSt 0 ++ immArg 0 1 ++ immArg 0 2 ++ scratchArg sD 3 ++ copyArg 4 4 ++ scratchArg sHash 5

def shaFinArgs : List Instr := scratchArg sSt 0 ++ copyArg 4 1 ++ immArg 0 2 ++ scratchArg sDH 3 ++ scratchArg sHash 4

def macInitArgs (key : Nat) : List Instr :=
  scratchArg sSt 0 ++ scratchArg sOuter 1 ++ scratchArg key 2 ++ immArg 32 3 ++ scratchArg sHash 4

def kdkUpdArgs : List Instr := scratchArg sSt 0 ++ immArg 64 1 ++ immArg 0 2 ++ copyArg 9 3 ++ copyArg 4 4 ++ scratchArg sHash 5

def kdkFinArgs : List Instr := scratchArg sSt 0 ++ scratchArg sOuter 1 ++
  [.mov .eax (.mem (incoming 4)), .alu .add .eax (.imm 64), .store (stackAt 8) .eax] ++
  immArg 0 3 ++ scratchArg sKDK 4 ++ scratchArg sHash 5

def hashD (H : Fns) : Prog isa :=
  .seq (callAfter shaInitArgs H.initN H.initC) (.seq (callAfter shaUpdArgs H.updN H.updC)
    (callAfter shaFinArgs H.finN H.finC))

def kdkMac (H : Fns) : Prog isa :=
  .seq (callAfter (macInitArgs sDH) H.hiN H.hiC) (.seq (callAfter kdkUpdArgs H.updN H.updC)
    (callAfter kdkFinArgs H.hfN H.hfC))

/-- Write a public IRPRF label byte through EDI. -/
def putByte (d v : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 v)), .store8 ⟨.edi, d⟩ .al]

def putLabel (label : List Nat) : List Instr :=
  label.zipIdx.flatMap fun vi => putByte (vi.2 + 2) vi.1

def msgBytes (label : List Nat) (len : List Instr) : List Instr :=
  putByte 0 0 ++ [.store8 ⟨.edi, 1⟩ .bl] ++ putLabel label ++ len

def clLen : List Instr := putByte 8 8 ++ putByte 9 0

def amLen : List Instr :=
  [.mov .eax (.reg .edx), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .mov .ecx (.reg .eax), .shift .shr .ecx 8,
    .store8 ⟨.edi, 9⟩ .cl, .store8 ⟨.edi, 10⟩ .al]

def msgPtr : List Instr :=
  [.mov .edi (.mem (incoming 21)), .alu .add .edi (.imm (BitVec.ofNat 32 sMsg)),
    .mov .ebx (.mem (stackAt oI)), .mov .edx (.mem (incoming 4))]

def prfUpdArgs (len : Nat) : List Instr :=
  scratchArg sSt 0 ++ immArg 64 1 ++ immArg 0 2 ++ scratchArg sMsg 3 ++ immArg len 4 ++ scratchArg sHash 5

def prfFinArgs (len dst : Nat) : List Instr :=
  scratchArg sSt 0 ++ scratchArg sOuter 1 ++ immArg (64 + len) 2 ++ immArg 0 3 ++
  [.mov .eax (.mem (incoming 21)), .alu .add .eax (.imm (BitVec.ofNat 32 dst)),
    .mov .ecx (.mem (stackAt oI)), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .eax (.reg .ecx), .store (stackAt 16) .eax] ++ scratchArg sHash 5

def incr : List Instr :=
  [.mov .eax (.mem (stackAt oI)), .alu .add .eax (.imm 1), .store (stackAt oI) .eax,
    .alu .cmp .eax (.mem (stackAt oNB))]

def prfBody (H : Fns) (label : List Nat) (len : List Instr) (dst : Nat) : Prog isa :=
  .seq (.block msgPtr) (.seq (.block (msgBytes label len))
    (.seq (callAfter (macInitArgs sKDK) H.hiN H.hiC)
      (.seq (callAfter (prfUpdArgs (label.length + 4)) H.updN H.updC)
        (.seq (callAfter (prfFinArgs (label.length + 4) dst) H.hfN H.hfC) (.block incr)))))

def lengthLabel : List Nat := [0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68]
def messageLabel : List Nat := [0x6d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65]

def clInit : List Instr :=
  [.mov .eax (.imm 0), .store (stackAt oI) .eax, .mov .eax (.imm 8), .store (stackAt oNB) .eax]

def amInit : List Instr :=
  [.mov .eax (.imm 0), .store (stackAt oI) .eax, .mov .eax (.mem (incoming 4)),
    .alu .add .eax (.imm 31), .shift .shr .eax 5, .store (stackAt oNB) .eax]

def clLoop (H : Fns) : Prog isa := .seq (.block clInit) (.loop (prfBody H lengthLabel clLen sCL) .ne)
def amLoop (H : Fns) : Prog isa := .seq (.block amInit) (.loop (prfBody H messageLabel amLen sAM) .ne)

/-- Two's-complement negation, using baseline instructions. -/
def negate (r : Reg) : List Instr := [.alu .xor r (.imm (BitVec.allOnes 32)), .alu .add r (.imm 1)]

/-- Start the public search for `2^bitLength(k - 11) - 1`. -/
def maskInit : List Instr :=
  [.mov .ecx (.mem (incoming 4)), .alu .sub .ecx (.imm 11), .mov .eax (.imm 0)]

def maskBody : List Instr :=
  [.alu .add .eax (.reg .eax), .alu .add .eax (.imm 1), .mov .edx (.reg .eax),
    .alu .sub .edx (.reg .ecx), .shift .shr .edx 31, .alu .cmp .edx (.imm 0)]

def maskLoop : Prog isa := .loop (.block maskBody) .ne

/-- ESI points to CL, EBX is the candidate mask, EBP is k - 11,
EDI is the selected length, and ECX is the public candidate count. -/
def alInit : List Instr :=
  [.store (stackAt oMK) .eax, .mov .ebx (.reg .eax), .mov .ebp (.reg .ecx),
    .mov .esi (.mem (incoming 21)), .alu .add .esi (.imm (BitVec.ofNat 32 sCL)),
    .mov .edi (.imm 0), .mov .ecx (.imm 128)]

def alBody : List Instr :=
  [.movzx8 .eax ⟨.esi, 0⟩, .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .movzx8 .edx ⟨.esi, 1⟩,
    .alu .add .eax (.reg .edx), .alu .and .eax (.reg .ebx), .mov .edx (.reg .ebp),
    .alu .sub .edx (.reg .eax), .shift .shr .edx 31, .alu .sub .edx (.imm 1),
    .alu .xor .eax (.reg .edi), .alu .and .eax (.reg .edx), .alu .xor .edi (.reg .eax),
    .alu .add .esi (.imm 2), .alu .sub .ecx (.imm 1)]

def alLoop : Prog isa := .loop (.block alBody) .ne

def alPart : Prog isa := .seq (.block maskInit) (.seq maskLoop (.seq (.block alInit)
  (.seq alLoop (.block [.store (stackAt oAL) .edi]))))

/-- ESI traverses EM from byte two, EDI is its index, EBX records whether
any separator was found, and EBP records the first separator's index. -/
def scanInit : List Instr :=
  [.mov .esi (.mem (incoming 0)), .alu .add .esi (.imm 2),
    .mov .ecx (.mem (incoming 4)), .alu .sub .ecx (.imm 2),
    .mov .edi (.imm 2), .mov .ebx (.imm 0), .mov .ebp (.imm 0)]

def scanBody : List Instr :=
  [.movzx8 .eax ⟨.esi, 0⟩, .alu .sub .eax (.imm 1), .shift .shr .eax 31,
    .mov .edx (.reg .ebx), .alu .xor .edx (.imm 1), .alu .and .edx (.reg .eax)] ++
  negate .edx ++
  [.alu .and .edx (.reg .edi), .alu .or .ebp (.reg .edx), .alu .or .ebx (.reg .eax),
    .alu .add .edi (.imm 1), .alu .add .esi (.imm 1), .alu .sub .ecx (.imm 1)]

def scanLoop : Prog isa := .loop (.block scanBody) .ne

/-- Check the header, separator and PS length; select the real or
alternative length, and mask its release by the checked RSA status. -/
def validLoads : List Instr := [.mov .esi (.mem (incoming 0))]

def validCalc : List Instr :=
  [.movzx8 .eax ⟨.esi, 0⟩,
    .alu .sub .eax (.imm 1), .shift .shr .eax 31, .movzx8 .edx ⟨.esi, 1⟩,
    .alu .xor .edx (.imm 2), .alu .sub .edx (.imm 1), .shift .shr .edx 31,
    .alu .and .eax (.reg .edx), .alu .and .eax (.reg .ebx),
    .mov .edx (.reg .ebp), .alu .sub .edx (.imm 10), .shift .shr .edx 31,
    .alu .xor .edx (.imm 1), .alu .and .eax (.reg .edx)] ++ negate .eax ++
  [.store (stackAt oValidMask) .eax,
    .mov .edi (.mem (incoming 4)), .alu .sub .edi (.reg .ebp), .alu .sub .edi (.imm 1),
    .alu .xor .edi (.mem (stackAt oAL)), .alu .and .edi (.reg .eax), .alu .xor .edi (.mem (stackAt oAL)),
    .mov .edx (.mem (stackAt oR)), .alu .xor .edx (.imm 1), .alu .sub .edx (.imm 1), .shift .shr .edx 31] ++
  negate .edx ++
  [.store (stackAt oOKMask) .edx, .mov .ecx (.mem (incoming 4)), .alu .sub .ecx (.reg .edi),
    .store (stackAt oCut) .ecx, .alu .and .edi (.reg .edx)]

def mlLoad : List Instr := [.mov .eax (.mem (incoming 2))]
def mlStore : List Instr := [.store ⟨.eax, 0⟩ .edi, .mov .edx (.imm 0), .store ⟨.eax, 4⟩ .edx]

def validBlock : Prog isa := .seq (.block validLoads) (.seq (.block validCalc)
  (.seq (.block mlLoad) (.block mlStore)))

/-- All EM and AM bytes are visited, independent of the selected length. -/
def selInit : List Instr :=
  [.mov .esi (.mem (incoming 0)), .mov .edi (.mem (incoming 21)),
    .alu .add .edi (.imm (BitVec.ofNat 32 sAM)), .mov .ecx (.mem (incoming 4)),
    .mov .ebp (.imm 0), .mov .ebx (.mem (stackAt oValidMask))]

def selBody : List Instr :=
  [.movzx8 .eax ⟨.esi, 0⟩, .movzx8 .edx ⟨.edi, 0⟩, .alu .xor .eax (.reg .edx),
    .alu .and .eax (.reg .ebx), .alu .xor .eax (.reg .edx), .mov .edx (.reg .ebp),
    .alu .sub .edx (.mem (stackAt oCut)), .shift .shr .edx 31, .alu .sub .edx (.imm 1),
    .alu .and .edx (.mem (stackAt oOKMask)), .alu .and .eax (.reg .edx), .store8 ⟨.esi, 0⟩ .al,
    .alu .add .esi (.imm 1), .alu .add .edi (.imm 1), .alu .add .ebp (.imm 1), .alu .sub .ecx (.imm 1)]

def selLoop : Prog isa := .loop (.block selBody) .ne

def selPart : Prog isa := .seq (.block scanInit) (.seq scanLoop (.seq validBlock
  (.seq (.block selInit) (.seq selLoop (.block [.mov .eax (.mem (stackAt oR))])))))

/-- Checked private RSA, key derivation, IRPRF, and masked message selection. -/
def body (H : Fns) (privN : String) (priv : Prog isa) : Prog isa :=
  .seq (.block privArgs) (.seq (.call privN priv) (.seq (.block dZero)
    (.seq (.loop (.block VG.Impl.Bignum.X86.PublicFn.clearStep) .ne)
      (.seq (.block dCopy) (.seq VG.Impl.Bignum.X86.copyBytes
        (.seq (hashD H) (.seq (kdkMac H) (.seq (clLoop H) (.seq (amLoop H) (.seq alPart selPart))))))))))

def code (H : Fns) (privN : String) (priv : Prog isa) : Prog isa :=
  .frame (.push [.ebx, .ebp, .esi, .edi])
    (.seq (.frame (.alloc frameBytes) (body H privN priv) (.free frameBytes))
      (.block VG.Impl.RsaPkcs1Sig.X86.Sign.restore)) (.pop .ebx 4)

end VG.Impl.RsaPkcs1Enc.X86.Decrypt
