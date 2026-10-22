module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.QCandidate
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CheckCandidate
public import VerifiedGarbage.Impl.Dsa.Generation.Layout

/-! Hash and test a subgroup candidate while retaining the caller's workspace pointer. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)

/-- The existing hash state and scratch fit in the reserved hash area. -/
def subgroupHashScratch : Nat := Dsa.Generation.Layout.hash + 256
def subgroupHashDigest : Nat := subgroupHashScratch + 512

def subgroupArguments (seedLen : Nat) : List Instr :=
  [.mov .ebx (.reg .edi), .alu .add .ebx (.imm (BitVec.ofNat 32 Dsa.Generation.Layout.hash)),
   .mov .ebp (.reg .edi), .alu .add .ebp (.imm (BitVec.ofNat 32 subgroupHashScratch)),
   .mov .edi (.imm (BitVec.ofNat 32 seedLen))]

def subgroupCandidate (H : Hash) (seedLen : Nat) : Prog isa :=
  .frame (.push [.edi])
    (.seq (.block (subgroupArguments seedLen))
      (qCandidate H 512 (Dsa.Generation.Layout.q - subgroupHashScratch))) (.pop .edi 1)

def subgroup (H : Hash) (name : String) (code : Prog isa) (seedLen : Nat) : Prog isa :=
  .seq (subgroupCandidate H seedLen) (checkCandidate name code 4 H.D Dsa.Generation.Layout.q)

end VG.Impl.Dsa.X86.Generation
