module
public import VerifiedGarbage.Impl.MlKem.AArch64.KeyGen
@[expose] public section
namespace VG.Impl.MlKem.AArch64.FixedHashCallers
open VG VG.AArch64 VG.Impl.MlKem.AArch64

abbrev HashFn := Reg→Nat→Nat→Nat→Nat→List Piece→List Piece→Prog isa

def kgGUsing (hash : HashFn) : Prog isa :=
 hash .x28 KG.ST KG.WK 72 6 [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩]
  [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩]
def kgAUsing (hash : HashFn) (L : KemLay) : Prog isa :=
 .seq (.block L.kgPrologue) (kgGUsing hash)
end VG.Impl.MlKem.AArch64.FixedHashCallers
