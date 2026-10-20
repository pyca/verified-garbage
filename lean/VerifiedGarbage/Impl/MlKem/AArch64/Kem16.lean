module

public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashDecaps
public import VerifiedGarbage.Impl.MlKem.AArch64.AddSubW
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec12W
public import VerifiedGarbage.Impl.MlKem.AArch64.DotW
public import VerifiedGarbage.Impl.MlKem.AArch64.Widen16
public import VerifiedGarbage.Impl.MlKem.AArch64.Decaps
public import VerifiedGarbage.Impl.MlKem.AArch64.NoiseWith
import VerifiedGarbage.Impl.MlKem.AArch64.Encaps

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

/-- `ek`, absorbed into the third state for `H(ek)` (SHA3-256) in key generation. -/
def kgSrc (L : KemLay) : Hybrid.HSrc := ⟨.x26, 0, L.ekLen, 6⟩

/-- The rows of `Â` the first `p` pairs complete. -/
def rowsBy (L : KemLay) (p : Nat) : Nat := min L.k (2 * p / L.k)

/-- The blocks of `pad(ek)` absorbed before pair `p`: each pair absorbs the next
blocks the rows before it have encoded, up to one per main squeeze. -/
def hashedBy (L : KemLay) : Nat → Nat
  | 0 => 0
  | p + 1 => hashedBy L p + min 3 (384 * rowsBy L p / 136 - hashedBy L p)

/-- Pair `p` of the matrix, absorbing the blocks of `ek` it can. -/
def kgPair (L : KemLay) (p : Nat) : Prog isa :=
  Hybrid.pairM KG.SB KG.SS KG.AH L (kgSrc L) (2 * p) (hashedBy L p)
    (hashedBy L (p + 1) - hashedBy L p) true

/-- Rows `a` to `b - 1` of `t̂`. -/
def kgRows (L : KemLay) (a b : Nat) : List (Prog isa) := (List.range' a (b - a)).map (kgRow L)

/-- The matrix, each row of `t̂` as soon as its entries are sampled. -/
def kgMatrixRows (L : KemLay) : List (Prog isa) :=
  ((List.range (L.k * L.k / 2)).flatMap fun p => kgPair L p :: kgRows L (rowsBy L p) (rowsBy L (p + 1))) ++
    (if L.k * L.k % 2 = 1 then Paired.lastSample L true true :: kgRows L (rowsBy L (L.k * L.k / 2)) L.k
      else [])

/-- The single-state permutation of the third state, at `ST`, with its working space at `WK`. -/
def kgPerm (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 KG.ST ++ ptrTo .x1 .x28 KG.WK)) (.call c.name c.code)

/-- `ρ` into both keys, the blocks of `pad(ek)` the matrix did not absorb, each
followed by the permutation `c`, `H(ek)` and `z` into `dk`, and the epilogue. -/
def kgTail (c : Impl.Sha3.AArch64.Callee) (L : KemLay) : Prog isa :=
  seqs ([.block (copy32 .x28 KG.SB .x26 (384 * L.k) ++ copy32 .x28 KG.SB .x27 (768 * L.k))] ++
    ((List.range' (hashedBy L (L.k * L.k / 2)) (Hybrid.blocks (kgSrc L) - hashedBy L (L.k * L.k / 2))).map
      fun b => .seq (.block (Hybrid.absorbBlock (kgSrc L) b)) (kgPerm c)) ++
    [.block (copy32 .x28 KG.ST .x27 (768 * L.k + 32) ++ copy32 .x25 32 .x27 (768 * L.k + 64) ++
      [mov .x0 .x24, .ldr .x .x30 .x28 (KG.SV L + 40), .ldr .x .x24 .x28 (KG.SV L),
        .ldr .x .x25 .x28 (KG.SV L + 8), .ldr .x .x26 .x28 (KG.SV L + 16),
        .ldr .x .x27 .x28 (KG.SV L + 24), .ldr .x .x28 .x28 (KG.SV L + 32)])])

/-- The noise, `ŝ` into `dk`, and the all-zero third state. -/
def kgPre (L : KemLay) : Prog isa :=
  seqs ([noiseAllWith nttAtWithW L true] ++ ((List.range L.k).map fun j => enc12WAt (KG.sOff L j) .x27 (384 * j)) ++
    [.block (zeroState .x28 KG.ST)])

/-- The key generation, hashing `ek` during the matrix: `G`, the noise, `ŝ` into `dk`,
the all-zero third state, the matrix with each row of `t̂` after its entries
(`kgMatrixRows`), and the rest of `H(ek)` (`kgTail`). -/
def keyGenH (hash : FixedHashCallers.HashFn) (c : Impl.Sha3.AArch64.Callee) (L : KemLay) : Prog isa :=
  seqs [FixedHashCallers.kgAUsing hash L, kgPre L, seqs (kgMatrixRows L), kgTail c L]

end VG.Impl.MlKem.AArch64.Kem16
