module
public import VerifiedGarbage.Impl.MlKem.AArch64.KeyGen
public import VerifiedGarbage.Impl.MlKem.AArch64.Optimized
@[expose] public section
namespace VG.Impl.MlKem.AArch64.FixedHashCallers
open VG VG.AArch64 VG.Impl.MlKem.AArch64

abbrev HashFn := Reg→Nat→Nat→Nat→Nat→List Piece→List Piece→Prog isa

def kgGUsing (hash : HashFn) : Prog isa :=
 hash .x28 KG.ST KG.WK 72 6 [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩]
  [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩]
def kgAUsing (hash : HashFn) (L : KemLay) : Prog isa :=
 .seq (.block L.kgPrologue) (kgGUsing hash)
def kgEndUsing (hash : HashFn) (L : KemLay) : Prog isa :=
 .seq (.block (copy32 .x28 KG.SB .x26 (384*L.k) ++ copy32 .x28 KG.SB .x27 (768*L.k)))
 (.seq (hash .x28 KG.ST KG.WK 136 6 [⟨.x26,0,L.ekLen⟩] [⟨.x27,768*L.k+32,32⟩])
 (.block (copy32 .x25 32 .x27 (768*L.k+64) ++
  [mov .x0 .x24,.ldr .x .x30 .x28 (KG.SV L+40),.ldr .x .x24 .x28 (KG.SV L),
   .ldr .x .x25 .x28 (KG.SV L+8),.ldr .x .x26 .x28 (KG.SV L+16),
   .ldr .x .x27 .x28 (KG.SV L+24),.ldr .x .x28 .x28 (KG.SV L+32)])))
def enAUsing (hash : HashFn) (L : KemLay) : Prog isa :=
 .seq (.block (L.kemPrologue 4 [0,2,3,4] ++ copy32 .x1 0 .x28 KEM.MB))
 (.seq (hash .x28 KEM.ST KEM.WK 136 6 [⟨.x25,0,L.ekLen⟩] [⟨.x28,KEM.HB,32⟩])
 (.seq (hash .x28 KEM.ST KEM.WK 72 6 [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩]
   [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩])
 (.block (copy32 .x25 (384*L.k) .x28 KEM.SB))))
def kgRestUsing (hash : HashFn) (L : KemLay) : Prog isa :=
 .seq (Noise.noiseAllWith Ntt16.Readonly.nttAtWith L true) (seqs (
  ((List.range L.k).map fun j=>kgEnc (KG.sOff L j) .x27 (384*j)) ++
  ((List.range L.k).map (Optimized.kgRow L)) ++ [kgEndUsing hash L]))
def keyGenUsing (hash : HashFn) (L : KemLay) : Prog isa :=
 .seq (kgAUsing hash L) (.seq (Paired.matrix L true) (kgRestUsing hash L))

end VG.Impl.MlKem.AArch64.FixedHashCallers
