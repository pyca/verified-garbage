module

public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Backend
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejBounded
public import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Encode
public import VerifiedGarbage.Impl.MlDsa.X86_64.KeyGen.Prims
import VerifiedGarbage.Impl.MlDsa.X86_64.KeyGen.KeyGen

/-!
# ML-DSA key generation on x86-64, with this library's primitives

`keyGen` (`KeyGen.lean`) called with the x86-64 implementations of the
primitives it calls (`Arith/`, `Sample/`, `Round/`, `Pack/`), with the
polynomial arithmetic of a `Backend` (`primsWith`).
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86_64.KeyGen

open VG.X86_64

/-- The x86-64 implementations of the primitives key generation calls. -/
def prims : Prims where
  ntt := Arith.ntt
  add := Arith.add
  rejNtt := Sample.rejNTTShort
  rejBounded := Sample.rejBoundedShort
  power2Round := Round.power2Round
  simpleBitPack := Pack.simpleBitPack
  bitPack := Pack.bitPack
  rej4 := Sample.Rej4.rejNTT4
  dotInv4 := Arith.dotInvSse2 4
  dotInv5 := Arith.dotInvSse2 5
  dotInv7 := Arith.dotInvSse2 7

/-- The primitives, with the polynomial arithmetic of `B`. -/
def primsWith (B : Arith.Backend) : Prims :=
  { prims with
    ntt := B.ntt
    add := B.add
    rej4 := B.rej4
    dotInv4 := B.dotInv4
    dotInv5 := B.dotInv5
    dotInv7 := B.dotInv7
    sfx := B.sfx }

end VG.Impl.MlDsa.X86_64.KeyGen
