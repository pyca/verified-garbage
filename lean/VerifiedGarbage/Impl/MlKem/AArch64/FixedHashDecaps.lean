module
public import VerifiedGarbage.Impl.MlKem.AArch64.Optimized
@[expose] public section
namespace VG.Impl.MlKem.AArch64.FixedHashDecaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64

def deStartUsing (h : Reg → Nat → Nat → Nat → Nat → List Piece → List Piece → Prog isa)
    (L : KemLay) : Prog isa :=
 seqs [.block (L.kemPrologue 3 [0,1,2,3]),Optimized.decryptM L,
 h .x28 KEM.ST KEM.WK 72 6 [⟨.x28,KEM.MB,32⟩,⟨.x25,768*L.k+32,32⟩]
 [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩],.block (copy32 .x25 (768*L.k) .x28 KEM.SB)]

end VG.Impl.MlKem.AArch64.FixedHashDecaps
