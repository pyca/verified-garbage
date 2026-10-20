module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedAdd
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.WitnessCut
public import VerifiedGarbage.Impl.RsaOaep.X86_64

/-! # Native hash contributions for DSA parameter generation

In addition to the streaming hash slots, frame words 1–4 hold the original
seed pointer, current search offset, wrapped-seed buffer, and concatenated
hash buffer. The wrapped seed and concatenated hashes lie outside the
hash function's first 8192 scratch bytes.

Contribution j is placed at (count-j)*len, so the highest-index digest is
first in memory. The p-candidate shaper consumes the final L/8 bytes.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs)

def seedInputArgs (j : Nat) : List Instr :=
  [.mov .rsi (.mem (sp 8)), .mov .rdi (.mem (sp 24)),
   .mov .rax (.mem (sp 16)), .alu .add .rax (.imm j)]

def useWrappedSeed : List Instr :=
  [.mov .rax (.mem (sp 24)), .store (sp sLab) .rax]

def hashCopyArgs (len count j : Nat) : List Instr :=
  [.mov .rsi (.mem (sp sScr)), .alu .add .rsi (.imm oDig),
   .mov .rdi (.mem (sp 32)), .alu .add .rdi (.imm (BitVec.ofNat 32 ((count - j) * len))),
   .mov32 .rcx (.imm len), .mov32 .rdx (.imm (8 * len))]

def pSeedHash (H : Stream) (len j : Nat) : Prog isa :=
  .seq (.block (seedInputArgs j)) (.seq (seedAdd len) (hashLabel H oDig))

def pHashOne (H : Stream) (len count j : Nat) : Prog isa :=
  .seq (pSeedHash H len j)
    (.seq (.block (hashCopyArgs len count j)) Ffdh.X86_64.ParameterCandidate.witnessCut)

def pHashPrefix (H : Stream) (len count : Nat) : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (pHashPrefix H len count k) (pHashOne H len count k)

def pHashes (H : Stream) (len count : Nat) : Prog isa :=
  pHashPrefix H len count (count + 1)

end VG.Impl.Dsa.X86_64.Generation
