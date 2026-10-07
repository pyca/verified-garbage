import VerifiedGarbage.Impl.Weierstrass.X86_64.Naf

/-! Public lookup of the cached Z² and Z³ belonging to an odd multiple. -/
namespace VG.Impl.Weierstrass.X86_64.Naf
open VG VG.X86_64 VG.Impl.Mont.X86_64

/-- For odd magnitude `a` in `r8`, select cache entry `(a-1)/2`, 64 bytes each. -/
def cacheAddress (tbl : Nat) : List Instr :=
  [.mov .rax (.reg .r8),.alu .sub .rax (.imm 1),.shift .shl .rax 5,
   .mov .rdx (.reg .rdi),.alu .add .rdx (.imm (BitVec.ofNat 32 tbl)),
   .alu .add .rdx (.reg .rax)]

def cacheRead (tbl dst : Nat) : List Instr :=
  cacheAddress tbl ++ copyPieces 4 (fun i => tblAt (16*i)) (fun i => sc (dst+16*i))

/-- The coordinates and powers use the same odd magnitude, retained in `r8`. -/
def cachedEntry (K : WinCfg) (tbl dst : Nat) : List Instr :=
  publicEntry K ++ cacheRead tbl dst

def signedCachedEntry (K : WinCfg) (tbl dst : Nat) : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 128)]) <|
    .ite .b (.block (cachedEntry K tbl dst)) (.block (
      [.mov32 .rax (.imm 256),.alu .sub .rax (.reg .r8),.mov .r8 (.reg .rax)] ++
      cachedEntry K tbl dst ++ VG.Impl.Mont.X86_64.sub K.M K.E.y K.zero K.E.y))

end VG.Impl.Weierstrass.X86_64.Naf
