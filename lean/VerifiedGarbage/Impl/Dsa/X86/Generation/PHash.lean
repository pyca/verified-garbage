module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.SeedAdd
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Hash

/-! # Hash a wrapped seed directly into one p-candidate contribution

ESI is the original seed, EDI the wrapped-seed buffer, EAX the addition,
EDX the destination digest, and EBP the hash workspace.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Pbkdf2.Stream.X86

def pHashArgs : List Instr := [.mov .esi (.reg .edi), .mov .edi (.reg .edx)]

def pSeedHash (H : Hash) (len : Nat) : Prog isa :=
  .seq (seedAdd len) (.seq (.block pHashArgs) (seedHash H len))
end VG.Impl.Dsa.X86.Generation
