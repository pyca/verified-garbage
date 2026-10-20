module
public import VerifiedGarbage.Impl.Pbkdf2.Stream.X86

/-! # Hash a fixed-width seed through the verified streaming functions

ESI holds the seed, EDI the digest destination, and EBP the hash workspace.
The first 512 bytes are callee scratch; the streaming state starts at byte
512. Callees preserve the pointers in EBX, ESI, EDI and EBP. Finalization
writes directly to the candidate or contribution buffer.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)

def hashHead : List Instr :=
  [.mov .ebx (.reg .ebp), .alu .add .ebx (.imm 512)]

def hashUpdateArgs (len : Nat) : List Instr :=
  [.mov .edx (.reg .esi), .mov .ecx (.imm (BitVec.ofNat 32 len)), .mov .eax (.imm 0)]

def hashFinalizeArgs (len : Nat) : List Instr :=
  [.mov .edx (.reg .edi), .mov .eax (.imm (BitVec.ofNat 32 len)), .mov .ecx (.imm 0)]

def seedHash (H : Hash) (len : Nat) : Prog isa :=
  .seq (.block hashHead)
    (.seq (H.callInit .ebx)
      (.seq (.block (hashUpdateArgs len))
        (.seq (.frame (.push [.ebp, .ecx, .edx, .eax, .eax, .ebx])
          (.call H.updN H.updC) (.pop .eax 6))
          (.seq (.block (hashFinalizeArgs len))
            (.frame (.push [.ebp, .edx, .ecx, .eax, .ebx])
              (.call H.finN H.finC) (.pop .eax 5))))))
end VG.Impl.Dsa.X86.Generation
