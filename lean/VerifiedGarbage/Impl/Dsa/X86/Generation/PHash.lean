module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Subgroup
public import VerifiedGarbage.Impl.Dsa.X86.Generation.SeedAdd
public import VerifiedGarbage.Impl.Bignum.X86.CopyBytes

/-! Reuse wrapped seed addition, streaming SHA, and byte copying for modulus contributions. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)

/-- Search metadata borrows the final-output buffer until packing begins. The
primality workspace excludes this buffer, so every witness round preserves it. -/
def seedPointer : Nat := Dsa.Generation.Layout.packed + 512
def candidateOffset : Nat := Dsa.Generation.Layout.packed + 528

def pSeedArguments (j : Nat) : List Instr :=
  [.mov .esi (.mem (sc seedPointer)), .mov .ebx (.reg .edi),
   .alu .add .ebx (.imm (BitVec.ofNat 32 Dsa.Generation.Layout.wrappedSeed)),
   .mov .edx (.mem (sc candidateOffset)), .alu .add .edx (.imm (BitVec.ofNat 32 j))]

/-- Copy an unchanged digest to a persistent buffer before restoring the workspace pointer. -/
def hashDigest (H : Hash) (seedLen destination : Nat) : Prog isa :=
  .frame (.push [.edi])
    (.seq (.block (subgroupArguments seedLen))
      (.seq (seedHash H 512)
        (.seq (.block (qArguments 512 (destination - subgroupHashScratch) H.D))
          VG.Impl.Bignum.X86.copyBytes))) (.pop .edi 1)

def pSeed (len j : Nat) : Prog isa :=
  .seq (.block (pSeedArguments j)) (seedAdd len)

def useWrappedSeed : List Instr :=
  [.mov .esi (.reg .edi), .alu .add .esi (.imm (BitVec.ofNat 32 Dsa.Generation.Layout.wrappedSeed))]

def pHashOne (H : Hash) (len count j : Nat) : Prog isa :=
  .seq (pSeed len j) (.seq (.block useWrappedSeed)
    (hashDigest H len (Dsa.Generation.Layout.hashes + (count - j) * H.D)))

def pHashPrefix (H : Hash) (len count : Nat) : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (pHashPrefix H len count k) (pHashOne H len count k)

def pHashes (H : Hash) (len count : Nat) : Prog isa := pHashPrefix H len count (count + 1)

end VG.Impl.Dsa.X86.Generation
