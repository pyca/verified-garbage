module

public import VerifiedGarbage.Impl.Rsa.X86.PrivChecked
public import VerifiedGarbage.Spec.RsaPkcs1Sig

/-! # EMSA-PKCS1-v1_5 encoding on baseline i686

EDI points to the output, ECX is its byte length, EDX identifies the hash,
ESI points to the digest, and EBP is its byte length. EBX holds the prefix
and padding counts; EAX carries bytes and the final status. Encoding returns
one on success, or zero without writing if the public lengths are invalid.
-/

@[expose] public section
namespace VG.Impl.RsaPkcs1Sig.X86
open VG VG.X86 Spec.RsaPkcs1Sig

def hashes : List Hash :=
  [.md5, .sha1, .sha224, .sha256, .sha384, .sha512, .sha512_224, .sha512_256,
    .sha3_224, .sha3_256, .sha3_384, .sha3_512]

def dispatch (c : Nat → Hash → Prog isa) (d : Prog isa) : List Hash → Nat → Prog isa
  | [], _ => d
  | h :: hs, i => .seq (.block [.alu .cmp .edx (.imm (BitVec.ofNat 32 i))])
      (.ite .e (c i h) (dispatch c d hs (i + 1)))

def lens (h : Hash) : Prog isa :=
  .block [.mov .ebx (.imm (BitVec.ofNat 32 (h.prefix.length + h.len))),
    .mov .eax (.imm (BitVec.ofNat 32 h.len))]

def putByte (b : Byte) : List Instr :=
  [.mov .eax (.imm (b.setWidth 32)), .store8 ⟨.edi, 0⟩ .al, .alu .add .edi (.imm 1)]

def putBytes (bs : List Byte) : List Instr := bs.flatMap putByte

def prefixBytes (h : Hash) : Prog isa := .block (putBytes h.prefix)

def headTail : List Instr :=
  [.mov .eax (.reg .ecx), .alu .sub .eax (.reg .ebx), .alu .sub .eax (.imm 3),
    .mov .ebx (.reg .eax), .mov .eax (.imm 0xff)]

def head : List Instr := putBytes [0x00, 0x01] ++ headTail

def psStep : List Instr :=
  [.store8 ⟨.edi, 0⟩ .al, .alu .add .edi (.imm 1), .alu .sub .ebx (.imm 1)]

def psLoop : Prog isa := .loop (.block psStep) .ne

def copyStep : List Instr :=
  [.movzx8 .eax ⟨.esi, 0⟩, .store8 ⟨.edi, 0⟩ .al, .alu .add .esi (.imm 1),
    .alu .add .edi (.imm 1), .alu .sub .ebp (.imm 1)]

def copyLoop : Prog isa := .loop (.block copyStep) .ne

def write : Prog isa :=
  .seq (.block head) (.seq psLoop (.seq (.block (putByte 0x00))
    (.seq (dispatch (fun _ h => prefixBytes h) (.block []) hashes 0)
      (.seq copyLoop (.block [.mov .eax (.imm 1)])))))

def fail : Prog isa := .block [.mov .eax (.imm 0)]

def encodeHash (h : Hash) : Prog isa :=
  .seq (lens h) (.seq (.block [.alu .cmp .ebp (.reg .eax)])
    (.ite .ne fail
      (.seq (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 11), .alu .cmp .ecx (.reg .eax)])
        (.ite .b fail write))))

def encode : Prog isa := dispatch (fun _ h => encodeHash h) fail hashes 0

/-- OR all byte differences into EBP, using the core's verified byte loop. -/
def compare : Prog isa :=
  .seq (.block [.mov .ebp (.imm 0)]) VG.Impl.Rsa.X86.PrivChecked.compareBytes

end VG.Impl.RsaPkcs1Sig.X86
