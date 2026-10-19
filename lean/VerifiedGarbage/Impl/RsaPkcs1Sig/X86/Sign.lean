module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Encode
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn

/-! # Checked PKCS #1 v1.5 signing on i686

A private frame holds the encoded digest and all twenty cdecl arguments of
the checked RSA call. The encoding is erased after that call. Invalid public
hash identifiers or lengths clear the output and return zero.
-/

@[expose] public section
namespace VG.Impl.RsaPkcs1Sig.X86.Sign
open VG VG.X86

def frameBytes : Nat := 1120
def emOffset : Nat := 96

def stackAt (d : Nat) : MemOp := ⟨.esp, d⟩
def incoming (i : Nat) : MemOp := stackAt (frameBytes + 20 + 4 * i)

def copyArgument (i j : Nat) : List Instr :=
  [.mov .eax (.mem (incoming i)), .store (stackAt (4 * j)) .eax]

def localArgument (d j : Nat) : List Instr :=
  [.mov .eax (.reg .esp), .alu .add .eax (.imm (BitVec.ofNat 32 d)), .store (stackAt (4 * j)) .eax]

def encArgs : List Instr :=
  [.mov .edi (.reg .esp), .alu .add .edi (.imm (BitVec.ofNat 32 emOffset)),
    .mov .ecx (.mem (incoming 3)), .mov .edx (.mem (incoming 6)),
    .mov .esi (.mem (incoming 7)), .mov .ebp (.mem (incoming 8))]

def callArgs : List Instr :=
  (List.range 6).flatMap (fun j => copyArgument j j) ++ localArgument emOffset 6 ++ copyArgument 3 7 ++
    (List.range 12).flatMap (fun j => copyArgument (j + 9) (j + 8))

def zeroOut : Prog isa :=
  .seq (.block [.mov .esi (.mem (incoming 0)), .mov .ecx (.mem (incoming 1)), .mov .eax (.imm 0)])
    (.loop (.block VG.Impl.Bignum.X86.PublicFn.clearStep) .ne)

/-- Keep the checked RSA status in EAX while erasing the encoded digest. -/
def wipe : Prog isa :=
  .seq (.block [.mov .ebx (.reg .eax), .mov .eax (.imm 0), .mov .esi (.reg .esp),
    .alu .add .esi (.imm (BitVec.ofNat 32 emOffset)), .mov .ecx (.mem (incoming 3))])
    (.seq (.loop (.block VG.Impl.Bignum.X86.PublicFn.clearStep) .ne)
      (.block [.mov .eax (.reg .ebx)]))

def afterEnc (privName : String) (priv : Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .eax (.imm 0)])
    (.ite .e zeroOut (.seq (.block callArgs) (.seq (.call privName priv) wipe)))

def body (privName : String) (priv : Prog isa) : Prog isa :=
  .seq (.block encArgs) (.seq encode (afterEnc privName priv))

def restore : List Instr :=
  [.mov .edi (.mem (stackAt 0)), .mov .ebp (.mem (stackAt 8)), .mov .esi (.mem (stackAt 4))]

def code (privName : String) (priv : Prog isa) : Prog isa :=
  .frame (.push [.ebx, .ebp, .esi, .edi])
    (.seq (.frame (.alloc frameBytes) (body privName priv) (.free frameBytes)) (.block restore)) (.pop .ebx 4)

end VG.Impl.RsaPkcs1Sig.X86.Sign
