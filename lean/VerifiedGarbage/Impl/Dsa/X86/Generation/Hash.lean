module

public import VerifiedGarbage.Impl.Pbkdf2.Stream.X86

/-! # Hash seed bytes with the existing streaming SHA implementations

The caller supplies state in `ebx`, seed pointer in `esi`, seed length in
`edi`, scratch in `ebp`, and a digest address held in its own frame. No
compression, padding or digest serialization is duplicated here.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_)

/-- Initialize and absorb the seed. The four callee-saved pointers survive both calls. -/
def hashAbsorb (H : Hash) : Prog isa :=
  .seq (H.callInit .ebx)
    (.seq (.block [.mov .edx (.reg .esi), .mov .ecx (.reg .edi), .mov .eax (.imm 0)])
      (.frame (.push [.ebp, .ecx, .edx, .eax, .eax, .ebx])
        (.call H.updN H.updC) (.pop .eax 6)))

/-- Finalize after loading the digest pointer into `edx`. -/
def hashFinish (H : Hash) : Prog isa :=
  .seq (.block [.mov .eax (.reg .edi), .mov .ecx (.imm 0)])
    (.frame (.push [.ebp, .edx, .ecx, .eax, .ebx]) (.call H.finN H.finC) (.pop .eax 5))

/-- Hash the seed and leave its digest at a public offset in scratch. -/
def seedHash (H : Hash) (digestOffset : Nat) : Prog isa :=
  .seq (hashAbsorb H)
    (.seq (.block [.mov .edx (.reg .ebp), .alu .add .edx (.imm (BitVec.ofNat 32 digestOffset))])
      (hashFinish H))

end VG.Impl.Dsa.X86.Generation
