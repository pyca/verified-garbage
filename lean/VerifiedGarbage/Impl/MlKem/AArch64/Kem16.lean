module

public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashDecaps
public import VerifiedGarbage.Impl.MlKem.AArch64.AddSubW
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec12W
public import VerifiedGarbage.Impl.MlKem.AArch64.DotW
public import VerifiedGarbage.Impl.MlKem.AArch64.Widen16
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls

/-! # AArch64 ML-KEM with 16-bit coefficients

The paired whole-KEM functions, with the hashing of `FixedHashCallers` and
`FixedHashDecaps` and the `Hybrid` matrix (hashing `ek` in encapsulation,
`z ‖ c`, copied to `scratch`, in decapsulation), with the matrix,
the noise and the products stored with 16-bit coefficients, in the first half of each 1024-byte slot of `scratch`:
the sampler and the CBD write halfwords (`w16`), the transforms are
`Ntt16.Readonly.nttAtWithW` and `nttInvAtWithW`, the dot products `DotW.dotW`
and the sums `AddSubW.addW`, and keys are encoded and decoded by
`Codec12W`. Compression still reads 32-bit coefficients: each row of `u` and
`v` is widened (`Widen16.widen`) into `PP` first, and `v` adds the decoded
message there with `vg_mlkem_add`. Decapsulation's decryption stays 32-bit.
-/

@[expose] public section
namespace VG.Impl.MlKem.AArch64.Kem16
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM
open VG.Impl.MlKem.AArch64.Noise (noiseOff noiseAllWith)
open VG.Impl.MlKem.AArch64.Ntt16.Readonly (nttAtWithW nttInvAtWithW)

/-- `f ← f + g`, both stored with 16 bits in `scratch`. -/
def addWAt (f g : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 f ++ ptrTo .x1 .x28 g)) AddSubW.addW

/-- The polynomial at `f`, stored with 16 bits, at `g` with 32. -/
def widenAt (f g : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 f ++ ptrTo .x1 .x28 g)) Widen16.widen

/-- `ByteDecode₁₂` of the 384 bytes at `b + o` into `off`, with 16 bits. -/
def dec12WAt (b : Reg) (o off : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 b o ++ ptrTo .x1 .x28 off)) Codec12W.decW

/-- `ByteEncode₁₂` of the polynomial at `off`, stored with 16 bits, into `b + o`. -/
def enc12WAt (off : Nat) (b : Reg) (o : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 b o)) Codec12W.encW

/-- The fused dot product into `out`, of terms in `scratch`. -/
def dotAt (out : Nat) (terms : List (Nat × Nat)) : Prog isa := DotW.dotW .x28 .x28 .x28 out terms

/-- Row `i` of `u`: `NTT⁻¹(Σⱼ Âⱼᵢ ∘ ŷⱼ) + e₁[i]`, widened, compressed and encoded. -/
def uRow (L : KemLay) (ct : Reg) (co i : Nat) : Prog isa :=
  seqs [dotAt (TP L) ((List.range L.k).map fun j => (aOff L j i, yOff L j)),
    nttInvAtWithW (TP L) NS, addWAt (TP L) (noiseOff L i), widenAt (TP L) (PP L),
    L.ceLAt (PP L) L.du ct (co + 32 * L.du * i)]

/-- `v = NTT⁻¹(t̂ ∘ ŷ) + e₂ + Decompress₁(m)`, compressed and encoded, with `t̂` decoded
from the key into the first row of the matrix. -/
def vRest (prf : Nat → Nat → Prog isa) (L : KemLay) (ek : Reg) (eo : Nat) (m : Reg) (mo : Nat)
    (ct : Reg) (co : Nat) : Prog isa :=
  seqs (((List.range L.k).map fun j => dec12WAt ek (eo + 384 * j) (aOff L 0 j)) ++
    [dotAt (TP L) ((List.range L.k).map fun j => (aOff L 0 j, yOff L j)),
    nttInvAtWithW (TP L) NS, prf (2 * L.k) (EP L), addWAt (TP L) (EP L), widenAt (TP L) (PP L),
    ddAt m mo 1 (EP L), addAt (PP L) (EP L), L.ceLAt (PP L) L.dv ct (co + 32 * L.du * L.k)])

/-- The noise, `u` and `v`. -/
def encryptRest (prf : Nat → Nat → Prog isa) (L : KemLay) (ek : Reg) (eo : Nat) (m : Reg)
    (mo : Nat) (ct : Reg) (co : Nat) : Prog isa :=
  .seq (noiseAllWith nttAtWithW L false) (seqs (((List.range L.k).map (uRow L ct co)) ++
    [vRest prf L ek eo m mo ct co]))

/-- Encapsulation after the matrix. -/
def enRest (prf : Nat → Nat → Prog isa) (L : KemLay) : Prog isa :=
  .seq (encryptRest prf L .x25 0 .x28 MB .x27 0) (.block L.kemEpilogue)

/-- The encapsulation, hashing `ek` during the matrix (`Hybrid.matrixH`). -/
def encaps (hash : FixedHashCallers.HashFn) (prf : Nat → Nat → Prog isa) (L : KemLay) : Prog isa :=
  .seq (Hybrid.startH L) (.seq (Hybrid.matrixH L (Hybrid.ekSrc L) true) (.seq (Hybrid.tailH hash) (enRest prf L)))

/-- Copy the `n` words at `sb + so` to `db + do`. -/
def copyN (n : Nat) (sb : Reg) (so : Nat) (db : Reg) (dO : Nat) : List Instr :=
  (List.range n).flatMap fun k => [.ldr .x .x9 sb (so + 8 * k), .str .x .x9 db (dO + 8 * k)]

/-- `J`'s message `z ‖ c`, copied to `scratch` just below `c'`'s buffer (`CB`),
absorbed with SHAKE256's suffix `0x1f` by the matrix's first pairs. -/
def jSrc (L : KemLay) : Hybrid.HSrc := ⟨.x28, CB L - 32, 32 + L.ctLen, 0x1f⟩

/-- The all-zero third state, `z` (from `dk`) and `c` to `scratch`. -/
def startJ (L : KemLay) : List Instr :=
  zeroState .x28 ST ++ copy32 .x25 (768 * L.k + 64) .x28 (CB L - 32) ++
    copyN (L.ctLen / 8) .x26 0 .x28 (CB L)

/-- `K̄ = J(z ‖ c)`, the first 32 bytes of the third state, into `JB`. -/
def tailJ : List Instr := copy32 .x28 ST .x28 JB

/-- Decapsulation after the matrix and `J`: re-encryption and the selection. -/
def deRest (prf : Nat → Nat → Prog isa) (L : KemLay) : Prog isa :=
  seqs [encryptRest prf L .x25 (384 * L.k) .x28 MB .x28 (CB L), L.deCmp, .block (deSel ++ L.kemEpilogue)]

/-- The decapsulation, hashing `z ‖ c` during the matrix (`Hybrid.matrixH`). -/
def decaps (hash : FixedHashCallers.HashFn) (prf : Nat → Nat → Prog isa) (L : KemLay) : Prog isa :=
  .seq (FixedHashDecaps.deStartUsing hash L) (.seq (.block (startJ L))
    (.seq (Hybrid.matrixH L (jSrc L) true) (.seq (.block tailJ) (deRest prf L))))

/-- Row `i` of `t̂ = Â ∘ ŝ + ê`, encoded into the public and private keys. -/
def kgRow (L : KemLay) (i : Nat) : Prog isa :=
  seqs [dotAt (KG.TP L) ((List.range L.k).map fun j => (KG.aOff L i j, KG.sOff L j)),
    addWAt (KG.TP L) (noiseOff L i), enc12WAt (KG.TP L) .x26 (384 * i),
    enc12WAt (KG.TP L) .x27 (384 * L.k + 384 * i)]

/-- Key generation after the matrix. -/
def kgRest (hash : FixedHashCallers.HashFn) (L : KemLay) : Prog isa :=
  .seq (noiseAllWith nttAtWithW L true) (seqs (
    ((List.range L.k).map fun j => enc12WAt (KG.sOff L j) .x27 (384 * j)) ++
    ((List.range L.k).map (kgRow L)) ++ [FixedHashCallers.kgEndUsing hash L]))

/-- The key generation. -/
def keyGen (hash : FixedHashCallers.HashFn) (L : KemLay) : Prog isa :=
  .seq (FixedHashCallers.kgAUsing hash L) (.seq (Paired.matrix L true true) (kgRest hash L))

end VG.Impl.MlKem.AArch64.Kem16
