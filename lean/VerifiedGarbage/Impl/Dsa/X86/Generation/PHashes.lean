module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Frame
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PHash
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PShape

/-! # Assemble p-candidate contributions in descending significance

Each hash writes its final digest directly to the concatenation buffer.
The final shaper selects only the low pLen bytes, including q160's partial
high contribution.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Pbkdf2.Stream.X86

def pContributionArgs (len count j : Nat) : List Instr :=
  [.mov .esi (.mem (frameSlot 1)), .mov .edi (.mem (frameSlot 3)),
   .mov .eax (.mem (frameSlot 2)), .alu .add .eax (.imm (BitVec.ofNat 32 j)),
   .mov .edx (.mem (frameSlot 4)), .alu .add .edx (.imm (BitVec.ofNat 32 ((count - j) * len))),
   .mov .ebp (.mem (frameSlot 14))]

def pHashOne (H : Hash) (len count j : Nat) : Prog isa :=
  .seq (.block (pContributionArgs len count j)) (pSeedHash H len)

def pHashPrefix (H : Hash) (len count : Nat) : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (pHashPrefix H len count k) (pHashOne H len count k)

def pHashes (H : Hash) (len count : Nat) : Prog isa := pHashPrefix H len count (count + 1)

def pShapeFromFrameArgs (len count pLen : Nat) : List Instr :=
  [.mov .esi (.mem (frameSlot 4)), .alu .add .esi (.imm (BitVec.ofNat 32 ((count + 1) * len - pLen))),
   .mov .edi (.mem (frameSlot 5)), .alu .add .edi (.imm (BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.shaped))]

def pHashesShape (H : Hash) (len count pLen : Nat) : Prog isa :=
  .seq (pHashes H len count) (.seq (.block (pShapeFromFrameArgs len count pLen)) (pShape pLen))
end VG.Impl.Dsa.X86.Generation
