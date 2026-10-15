module
public import VerifiedGarbage.Impl.MlKem.AArch64.OptimizedUsing
@[expose] public section
namespace VG.Impl.MlKem.AArch64.FixedHashDecaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64

def deStartUsing (h : Reg → Nat → Nat → Nat → Nat → List Piece → List Piece → Prog isa)
    (L : KemLay) : Prog isa :=
 seqs [.block (L.kemPrologue 3 [0,1,2,3]),Optimized.decryptM L,
 h .x28 KEM.ST KEM.WK 72 6 [⟨.x28,KEM.MB,32⟩,⟨.x25,768*L.k+32,32⟩]
 [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩],.block (copy32 .x25 (768*L.k) .x28 KEM.SB)]

def deRestUsing (h : Reg → Nat → Nat → Nat → Nat → List Piece → List Piece → Prog isa)
    (callee : Impl.Sha3.AArch64.Callee) (L : KemLay) : Prog isa :=
 seqs [Optimized.encryptRest callee L .x25 (384*L.k) .x28 KEM.MB .x28 (KEM.CB L),
  h .x28 KEM.ST KEM.WK 136 0x1f [⟨.x25,768*L.k+64,32⟩,⟨.x26,0,L.ctLen⟩] [⟨.x28,KEM.JB,32⟩],
  L.deCmp,.block (deSel ++ L.kemEpilogue)]

def deRestPrfUsing (h : Reg → Nat → Nat → Nat → Nat → List Piece → List Piece → Prog isa)
    (prf : Nat→Nat→Prog isa) (L : KemLay) : Prog isa :=
 seqs [Optimized.encryptRestUsing prf L .x25 (384*L.k) .x28 KEM.MB .x28 (KEM.CB L),
  h .x28 KEM.ST KEM.WK 136 0x1f [⟨.x25,768*L.k+64,32⟩,⟨.x26,0,L.ctLen⟩] [⟨.x28,KEM.JB,32⟩],
  L.deCmp,.block (deSel ++ L.kemEpilogue)]

def decapsUsing (hash : Reg → Nat → Nat → Nat → Nat → List Piece → List Piece → Prog isa)
    (prf : Nat→Nat→Prog isa) (L : KemLay) : Prog isa :=
 .seq (deStartUsing hash L) (.seq (Paired.matrix L false) (deRestPrfUsing hash prf L))

end VG.Impl.MlKem.AArch64.FixedHashDecaps
