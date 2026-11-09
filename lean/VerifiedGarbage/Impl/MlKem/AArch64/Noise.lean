module

public import VerifiedGarbage.Impl.MlKem.AArch64.Paired

/-! # Paired SHAKE256 noise generation

Generate two independent 128-byte PRF outputs before CBD sampling. The
extra noise polynomials occupy the otherwise unused end of the caller's
scratch allocation. Key generation transforms both secret and error
polynomials; encryption transforms only the ephemeral secret.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64

def noiseOff (L : KemLay) (n : Nat) : Nat := L.scl - 1024*L.k + 1024*n
def initCore (sb n : Nat) : List Instr :=
 [.vop (.movi0 .v0)] ++
 ((List.range 25).map fun i => .strq .v0 .x19 (16*i)) ++
 ((List.range 4).flatMap fun i => [.ldr .x .x6 .x28 (sb+8*i), .vop (.dup .d2 .v0 .x6), .strq .v0 .x19 (16*i)]) ++
 [.movz .x .x6 (BitVec.ofNat 16 (n+0x1f00)) 0,.movz .x .x7 (BitVec.ofNat 16 (n+1+0x1f00)) 0,
 .vop (.dup .d2 .v0 .x6),.vop (.ins .d2 .v0 1 .x7),.strq .v0 .x19 64,
 .movz .x .x6 0x8000 3,.vop (.dup .d2 .v0 .x6),.strq .v0 .x19 256]

def noiseInit (_L : KemLay) (kg : Bool) (n : Nat) : List Instr :=
 let ss := if kg then KG.SS else KEM.SS
 let sb := if kg then KG.SG else KEM.RB
 ptrTo .x2 .x28 ss ++ (Paired.saved.zipIdx.map fun (r,i) => .str .x r .x2 (1800+8*i)) ++
 [mov .x19 .x2] ++ initCore sb n ++
 [.addImm .x .x20 .x19 400,.addImm .x .x21 .x19 528]
def squeezePair : Prog isa :=
 .seq (VG.Impl.Sha3.AArch64.Neon.X2.call true .x19 .x19 1536)
  (.block (VG.Impl.Sha3.AArch64.Neon.X2.squeeze 16 .x19 .x20 .x21))

end VG.Impl.MlKem.AArch64.Noise
