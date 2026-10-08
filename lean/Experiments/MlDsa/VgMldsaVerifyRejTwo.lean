import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
import VerifiedGarbage.Impl.MlDsa.AArch64.Call
import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Frag
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.KeyGen
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
import VerifiedGarbage.Variants.Keccak.AArch64.Sha3
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt4
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
namespace RootPair

open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.MlDsa.AArch64.Sample
namespace ExpRej

-- These zero only the existing output range; rnSetup reinitializes x3/x4.
def zeroWide : Prog isa := .block <|
  [.movz .x .x9 0 0] ++ (List.range 128).map (fun i => .str .x .x9 .x26 (8*i))

def zeroNeon : Prog isa := .block <|
  [.vop (.movi0 .v0)] ++ (List.range 64).map (fun i => .strq .v0 .x26 (16*i))

def zero (v : Nat) : Prog isa := if v==0 then zeroWide else zeroNeon

def setup (pairs : Bool := false) : List Instr :=
  [.addImm .x .x2 .x25 840,mov .x3 .x26,.movz .x .x4 256 0,
   .movz .x .x5 (if pairs then 168 else 336) 0] ++ movQ .x9 ++
  [.movz .x .x10 65535 0,.movk .x .x10 127 1]

-- Stop consuming chunks once the output is full; x4 retains the exact
-- accept count, including on exhaustion/failure.
def stopWhenFull : Prog isa :=
  .ite (.zero .x .x4) (.block [.movz .x .x5 0 0]) (.block [])

-- Last load consumes the first padding byte at scratch+1848, within
-- the2048-byte scratch contract. The high byte is masked away.
def wideChunk : List Instr :=
  [.ldr .w .x11 .x2 0,.logic .and .x .x11 .x11 .x10,
   .addImm .x .x2 .x2 3,.subImm .x .x5 .x5 1]

def wideLoop : Prog isa := .seq (.block (setup false)) <|
  .loop (.seq (.block (wideChunk++rnAccept)) stopWhenFull) (.nonzero .x .x5)

-- Two3-byte candidates in one64-bit word; at most two masked padding
-- bytes are read, still inside the private scratch buffer.
def pairFirst : List Instr :=
  [.ldr .x .x6 .x2 0,.logic .and .x .x11 .x6 .x10] ++ rnAccept

def pairSecond : List Instr :=
  [.lsr .x .x11 .x6 24,.logic .and .x .x11 .x11 .x10] ++ rnAccept

def pairBody : Prog isa := .seq (.block pairFirst) <|
  .seq (.ite (.zero .x .x4) (.block []) (.block pairSecond)) <|
  .seq (.block [.addImm .x .x2 .x2 6,.subImm .x .x5 .x5 1]) stopWhenFull

def pairLoop : Prog isa :=
  .seq (.block (setup true)) (.loop pairBody (.nonzero .x .x5))

-- Bulk eight candidates while at least eight output slots remain. This
-- removes interior fullness branches and uses exactly three aligned loads.
def bulkExtract (i : Nat) : List Instr :=
  (match i with
   | 0 => [mov .x11 .x6]
   | 1 => [.lsr .x .x11 .x6 24]
   | 2 => [.extr .x .x11 .x7 .x6 48]
   | 3 => [.lsr .x .x11 .x7 8]
   | 4 => [.lsr .x .x11 .x7 32]
   | 5 => [.extr .x .x11 .x8 .x7 56]
   | 6 => [.lsr .x .x11 .x8 16]
   | _ => [.lsr .x .x11 .x8 40]) ++
  [.logic .and .x .x11 .x11 .x10] ++ rnAccept

def bulkBody : List Instr :=
  [.ldr .x .x6 .x2 0,.ldr .x .x7 .x2 8,.ldr .x .x8 .x2 16] ++
  (List.range 8).flatMap bulkExtract ++
  [.addImm .x .x2 .x2 24,.subImm .x .x5 .x5 8,
   .subs .x .x16 .x4 .x12,.cselc .x .x16 .x5 .x0 .hs]

def wideMulLoop : Prog isa :=
  .loop (.block (wideChunk++rnAccept++[.mul .x .x16 .x4 .x5])) (.nonzero .x .x16)

def bulkLoop : Prog isa :=
  .seq (.block (setup false++[.movz .x .x0 0 0,.movz .x .x12 8 0])) <|
   .seq (.loop (.block bulkBody) (.nonzero .x .x16)) <|
    .seq (.block [.mul .x .x16 .x4 .x5]) <|
     .ite (.zero .x .x16) (.block []) wideMulLoop

def mulLoop : Prog isa := .seq (.block (setup false)) wideMulLoop

-- Compact alternatives avoid inflating the sampler text by64stores.
def zeroNeonLoop : Prog isa :=
  .seq (.block [.vop (.movi0 .v0),mov .x3 .x26,.movz .x .x4 16 0]) <|
   .loop (.block [.strq .v0 .x3 0,.strq .v0 .x3 16,.strq .v0 .x3 32,
    .strq .v0 .x3 48,.addImm .x .x3 .x3 64,.subImm .x .x4 .x4 1]) (.nonzero .x .x4)

def parser (v : Nat) : Prog isa :=
  if v==0 then rnLoop else if v==1 then wideLoop else if v==2 then pairLoop else
    if v==3 then bulkLoop else mulLoop

def zeroFor (z : Nat) : Prog isa :=
  if z==0 then zeroPoly else if z==1 then zeroWide else if z==2 then zeroNeon else zeroNeonLoop

def sample (v z k : Nat) : Prog isa :=
  .seq (.block [.addImm .x .x25 .x19 (1008*k),.addImm .x .x26 .x21 (1024*k)]) <|
    .seq (zeroFor z) <| .seq (parser v) <|
      .block (retZ++[.logic .and .x .x27 .x27 .x0])

def rej4With (squeeze : Prog isa) (v z : Nat) : Prog isa :=
  .seq (.block (Rej4.init++Rej4.setup)) <|
   .seq (.loop squeeze (.nonzero .x .x28)) <|
    .seq (.block [.movz .x .x27 1 0]) <|
     .seq (sample v z 0) <| .seq (sample v z 1) <|
      .seq (sample v z 2) <| .seq (sample v z 3) (.block Rej4.epi)

def rejWith (c : Impl.Sha3.AArch64.Callee) (v z : Nat) : Prog isa :=
  .seq (.block (pro .x2 .x1 (.movz .x .x27 0 0) (.movz .x .x4 34 0))) <|
    .seq (spongeWith c 168 1008) <|
      .seq (zeroFor z) <| .seq (parser v) (.block (retZ++epi))
end ExpRej


namespace ExpRejFiveParse


-- Four remaining-output counters; disjoint from buffers and ABI saves.
def counts : Nat := 7904

def initCounts : List Instr := [.movz .x .x4 256 0] ++
  (List.range 2).map (fun k => .str .x .x4 .x19 (counts+8*k))

-- Reconstitute squeeze pointers after parsing borrowed x25/x26/x27.
def squeezeSetup (off n : Nat) : List Instr :=
  [mov .x22 .x19,.addImm .x .x23 .x19 400,
   .addImm .x .x24 .x19 840,.addImm .x .x25 .x19 1848,
   .addImm .x .x26 .x19 2856,.addImm .x .x27 .x19 3864] ++
  (if off==0 then [] else [.addImm .x .x24 .x24 off,.addImm .x .x25 .x25 off,
    .addImm .x .x26 .x26 off,.addImm .x .x27 .x27 off]) ++
  [.movz .x .x28 n 0]

def squeezeN (squeeze : Prog isa) (off n : Nat) : Prog isa :=
  .seq (.block (squeezeSetup off n)) (.loop squeeze (.nonzero .x .x28))

def setup (k off n : Nat) : List Instr :=
  [.addImm .x .x2 .x19 (840+1008*k),.addImm .x .x2 .x2 off,
   .addImm .x .x3 .x21 (1024*k),.ldr .x .x4 .x19 (counts+8*k),
   .movz .x .x6 256 0,.sub .x .x6 .x6 .x4,.lsl .x .x6 .x6 2,
   .add .x .x3 .x3 .x6,.movz .x .x5 n 0] ++ movQ .x9 ++ [.movz .x .x10 127 0]

def imm64 (r : Reg) (n : Nat) : List Instr :=
 [.movz .x r (BitVec.ofNat 16 n) 0] ++ (List.range 3).map
 (fun i => .movk .x r (BitVec.ofNat 16 (n / 2^(16*(i+1)))) (i+1))

def vectorSetup : List Instr :=
 imm64 .x6 0xff050403ff020100 ++ imm64 .x7 0xff0b0a09ff080706 ++
 [.vop (.dup .d2 .v3 .x6),.vop (.ins .d2 .v3 1 .x7),
 .movz .x .x10 65535 0,.movk .x .x10 127 1,
 .vop (.dup .s4 .v4 .x10),.vop (.dup .s4 .v5 .x9),
 .movz .x .x12 1 0,.movk .x .x12 1 2,.movz .x .x17 4 0,
 .movz .x .x0 0 0]

def guard : List Instr := [.subs .x .x16 .x4 .x17,.cselc .x .x16 .x5 .x0 .hs]

def vectorTry : List Instr :=
 [.ldrq .v0 .x2 0,.vop (.tbl .v1 .v0 .v3),.vop (.logic .and .v1 .v1 .v4),
 .vop (.sub .s4 .v2 .v1 .v5),.vop (.shift .ushr .s4 .v2 .v2 31),
 .umov .x .x6 .v2 0,.umov .x .x7 .v2 1,.logic .and .x .x6 .x6 .x7,
 .logic .eor .x .x6 .x6 .x12]

def vectorAccept : List Instr := [.strq .v1 .x3 0,.addImm .x .x3 .x3 16,
 .subImm .x .x4 .x4 4]

def vectorReject : List Instr := (List.range 4).flatMap
 (fun i => [.umov .w .x11 .v1 i] ++ rnAccept)

def vectorBody : Prog isa := .seq (.block vectorTry) <|
 .seq (.ite (.zero .x .x6) (.block vectorAccept) (.block vectorReject)) <|
 .block ([.addImm .x .x2 .x2 12,.subImm .x .x5 .x5 4]++guard)

def parse (_v : Nat) : Prog isa :=
 .seq (.block (vectorSetup++guard)) <|
 .seq (.ite (.zero .x .x16) (.block [])
   (.loop vectorBody (.nonzero .x .x16))) <|
 .seq (.block [.mul .x .x16 .x4 .x5]) <|
 .ite (.zero .x .x16) (.block []) ExpRej.wideMulLoop

def segment (v k off n : Nat) : Prog isa :=
 .seq (.block (setup k off n)) <| .seq (parse v) <|
 .block [.str .x .x4 .x19 (counts+8*k)]

def batch (v off n : Nat) : Prog isa :=
 .seq (segment v 0 off n) (segment v 1 off n)

def zeros : Prog isa := .block <| [.vop (.movi0 .v0)] ++
 (List.range 128).map (fun i => .strq .v0 .x21 (16*i))

def flags : List Instr := [.ldr .x .x27 .x19 counts] ++
 (List.range 1).flatMap (fun k => [.ldr .x .x6 .x19 (counts+8*(k+1)),
 .logic .orr .x .x27 .x27 .x6])

def rej4With (squeeze : Prog isa) (v : Nat) : Prog isa :=
 .seq (.block (Rej4.pro ++ Rej4.zeroStates ++ Rej4.absorbPair 0 ++ initCounts)) <|
 .seq (squeezeN squeeze 0 3) <| .seq zeros <| .seq (batch v 0 168) <|
 .seq (squeezeN squeeze 504 2) <| .seq (batch v 504 112) <|
 .seq (.block flags) <|
 .seq (.ite (.zero .x .x27) (.block [])
 (.seq (squeezeN squeeze 840 1) <| .seq (batch v 840 56) (.block flags))) <|
 .block ([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63]++Rej4.epi)
end ExpRejFiveParse



def rootRej2 : Prog isa := ExpRejFiveParse.rej4With (.seq (Impl.Sha3.AArch64.Neon.Pair.progWith true .x22 .x24 .x25) (.block Rej4.advance)) 0

end RootPair
open VG VG.AArch64
namespace CommitHash
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Impl.MlDsa.AArch64.Call
-- ABI: mu=x0 (64 bytes), w1=x1 (768/1024 bytes), out=x2 (32/48/64), scratch=x3(128).
def save : List Instr := (List.range 8).map (fun i => .strq (vreg (8+i)) .x3 (16*i))
def restore : List Instr := (List.range 8).map (fun i => .ldrq (vreg (8+i)) .x3 (16*i))
def first : List Instr :=
 (List.range 4).flatMap (fun i => [.ldrq (vreg (2*i)) .x0 (16*i),
 .vop (.ext (vreg (2*i+1)) (vreg (2*i)) (vreg (2*i)) 8)]) ++
 (List.range 4).flatMap (fun i => [.ldrq (vreg (8+2*i)) .x1 (16*i),
 .vop (.ext (vreg (9+2*i)) (vreg (8+2*i)) (vreg (8+2*i)) 8)]) ++
 [.ldr .x .x6 .x1 64,.vop (.dup .d2 .v16 .x6)] ++
 (List.range 8).map (fun i => .vop (.movi0 (vreg (17+i))))
def absorbPair (i : Nat) : List Instr := [.ldrq .v25 .x5 (16*i),
 .vop (.ext .v26 .v25 .v25 8),.vop (.logic .eor (vreg (2*i)) (vreg (2*i)) .v25),
 .vop (.logic .eor (vreg (2*i+1)) (vreg (2*i+1)) .v26)]
def full : List Instr := (List.range 8).flatMap absorbPair ++
 [.ldr .x .x6 .x5 128,.vop (.dup .d2 .v25 .x6),.vop (.logic .eor .v16 .v16 .v25),
 .addImm .x .x5 .x5 136]
def tail (wlen : Nat) : List Instr :=
 (if wlen==768 then absorbPair 0 else []) ++
 [.movz .x .x6 31 0,.vop (.dup .d2 .v25 .x6),
 .vop (.logic .eor (if wlen==768 then .v2 else .v0) (if wlen==768 then .v2 else .v0) .v25),
 .movz .x .x6 0x8000 3,.vop (.dup .d2 .v25 .x6),.vop (.logic .eor .v16 .v16 .v25)]
def output (n : Nat) : List Instr := (List.range (n/16)).flatMap (fun i =>
 [.vop (.perm .zip1 .d2 .v25 (vreg (2*i)) (vreg (2*i+1))),.strq .v25 .x2 (16*i)])
def hash (wlen olen : Nat) : Prog isa :=
 .seq (.block (save++first++[.addImm .x .x5 .x1 72,.movz .x .x4 (if wlen==768 then 6 else 8) 0])) <|
 .seq (.loop (.seq (.block (rounds++[.subImm .x .x4 .x4 1]))
  (.ite (.zero .x .x4) (.block []) (.block full))) (.nonzero .x .x4)) <|
 .block (tail wlen++rounds++output olen++restore)
def hashAt (wlen olen : Nat) (mu w out scratch : Ptr) : Prog isa :=
 callAt ("vg_mldsa_commit_hash"++toString olen) (hash wlen olen)
 [(.x0,.ptr mu),(.x1,.ptr w),(.x2,.ptr out),(.x3,.ptr scratch)]
end CommitHash

open VG VG.AArch64
namespace CombDot
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call

def product (j : Nat) : List Instr :=
 [.ldrq .v0 .x1 (1024*j),.ldrq .v1 .x2 (1024*j)] ++
 (if j=0 then [.vop (.umull false .v2 .v0 .v1),.vop (.umull true .v3 .v0 .v1)]
 else [.vop (.umlal false .v2 .v0 .v1),.vop (.umlal true .v3 .v0 .v1)])
def dot (n : Nat) : Prog isa :=
 .seq (.block (consts ++ [.movz .x .x12 64 0])) <|
 .loop (.block ((List.range n).flatMap product ++
 [.vop (.perm .uzp1 .s4 .v4 .v2 .v3),.vop (.mul .v4 .v4 .v17),
 .vop (.umlal false .v2 .v4 .v16),.vop (.umlal true .v3 .v4 .v16),
 .vop (.perm .uzp2 .s4 .v0 .v2 .v3)] ++ csub .v0 .v4 ++
 [.strq .v0 .x0 0,.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,
 .addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1])) (.nonzero .x .x12)
def dotAt (n : Nat) (h f g : Ptr) : Prog isa :=
 callAt ("vg_mldsa_dot" ++ toString n) (dot n) [(.x0,.ptr h),(.x1,.ptr f),(.x2,.ptr g)]
end CombDot
open VG VG.AArch64
namespace WindowMask
open VG.Impl.MlDsa.AArch64.Call
-- Fixed-address four-vector mask per iteration. The sampler returns w0 in {0,1}.
def maskN (a : Ptr) (count : Nat) : Prog isa :=
 .seq (.block ([.movz .x .x8 0 0,.sub .w .x8 .x8 .x0,.vop (.dup .s4 .v0 .x8)] ++
  lea .x1 a.1 a.2 ++ [.movz .x .x2 (BitVec.ofNat 16 (count/16)) 0])) <|
 .loop (.block ((List.range 4).flatMap (fun i =>
  [.ldrq .v1 .x1 (16*i),.vop (.logic .and .v1 .v1 .v0),.strq .v1 .x1 (16*i)]) ++
  [.addImm .x .x1 .x1 64,.subImm .x .x2 .x2 1])) (.nonzero .x .x2)
def mask4 (a : Ptr) : Prog isa := maskN a 1024
def sampled (call : Prog isa) (a : Ptr) : Prog isa :=
 .seq call (.seq (.block and24) (maskN a 256))
end WindowMask


/-!
# ML-DSA on AArch64: `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

`keyGen P p (seed = x0, pk = x1, sk = x2, scratch = x3) -> w0`:
`ML-DSA.KeyGen_internal(ξ)` (FIPS 204 Algorithm 6) of the parameter set
`p`, with `ξ` at `seed`, as calls of the primitives `P` and of the SHA-3
sponge functions (`Frag.lean`). It keeps `seed` in `x25`, `pk` in `x26`,
`sk` in `x27` and `scratch` in `x28`, and the AND of the results of the
samplers in `x24`.

The layout of `scratch` (in bytes): the Keccak state at 0 and the sponge
functions' working space at 200, the saved registers at 840; `k` and `ℓ`
at 896 (`oKL`); `(ρ, ρ′, K)` at 1024 (`oHX`, 128 bytes); the seed of
`RejNTTPoly` at 1152 (`oSA`, 34 bytes) and of `RejBoundedPoly` at 1216
(`oSB`, 66 bytes); the working space of the primitives at 2048 (2048 bytes);
and polynomials of 1024 bytes from 4096 (`oP j`): `Â[r, s]` is polynomial
`rℓ + s`, `s₁[j]` (then `ŝ₁[j]`) polynomial `kℓ + j`, `s₂[i]` polynomial
`kℓ + ℓ + i`, and `t`, `t₁` and `t₀` the three after them.

1. `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)`, and `ρ` and `ρ′` to the seeds.
2. `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)` and `s₁ ‖ s₂ = RejBoundedPoly(ρ′ ‖ r ‖ 0)`
   (`ExpandA`, `ExpandS`). After each, `x24 ← x24 ∧ result`, and the
   polynomial is ANDed with `-result` (`mask`): it is zero if the sampler
   failed, so that every polynomial is reduced, and small, whatever the
   samplers return, without a branch.
3. `ρ` and `K` to `sk`; `s₁` and `s₂`, `BitPack`ed, to `sk`; `ŝ₁ = NTT(s₁)`.
4. For each row `i`: `t = NTT⁻¹(Σⱼ Â[i, j] ŝ₁[j]) + s₂[i]`, `Power2Round`, and
   `t₁` `SimpleBitPack`ed to `pk`, `t₀` `BitPack`ed to `sk`; `ρ` to `pk`.
5. `tr = H(pk, 64)` to `sk`; return `x24`.

Every address and branch depends only on the pointers, but for what the
samplers leak (`ρ` and which half-bytes `RejBoundedPoly` rejects).
-/

namespace WindowKeygen
open VG.Impl.MlDsa.AArch64.KeyGen

variable (c : Impl.Sha3.AArch64.Callee)

open VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Impl.MlKem.AArch64 (copy32)
open VG.Spec.MlDsa (Params bitlen)

/-! ## The layout of the working space -/

def oKL : Nat := 896
def oHX : Nat := 1024
def oSA : Nat := 1152
def oSA4 : Nat := 1408
def oSB : Nat := 1216
def oSS : Nat := 2048
/-- Polynomial `j`. -/
def oP (j : Nat) : Nat := 4096 + 1024 * j

/-- `Â[r, s]`, entry `e = rℓ + s`. -/
abbrev aP (e : Nat) : Ptr := sc (oP e)
/-- `s₁ ‖ s₂`, entry `r`. -/
abbrev sP (p : Params) (r : Nat) : Ptr := sc (oP (p.k * p.ℓ + r))
abbrev tP (p : Params) : Ptr := sc (oP (p.k * p.ℓ + p.ℓ + p.k))
abbrev t1P (p : Params) : Ptr := sc (oP (p.k * p.ℓ + p.ℓ + p.k + 1))
abbrev t0P (p : Params) : Ptr := sc (oP (p.k * p.ℓ + p.ℓ + p.k + 2))

/-- The eight KiB four-way sampler scratch follows the live polynomials. -/
def oR4 (p : Params) : Nat := oP (p.k*p.ℓ+p.ℓ+p.k+3)

/-- The length of a packed polynomial of `s₁` or `s₂`, `32 · bitlen (2η)`. -/
def lenS (p : Params) : Nat := 32 * bitlen (2 * p.η)
/-- Where `t₀` starts in `sk`. -/
def oT0 (p : Params) : Nat := 128 + lenS p * (p.ℓ + p.k)

/-! ## The pieces -/

/-- `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)`, `ρ` to the seed of `RejNTTPoly`, and
`ρ′ ‖ 0` to that of `RejBoundedPoly`. -/
def seedsWith (p : Params) : Prog isa :=
  .seq (.block (setB (sc oKL) p.k ++ setB (sc (oKL + 1)) p.ℓ))
    (.seq ((shake256With c) [⟨.x25, 0, 32⟩, ⟨.x28, oKL, 2⟩] [⟨.x28, oHX, 128⟩])
      (.block (copy32 .x28 oHX .x28 oSA ++ copy32 .x28 (oHX + 32) .x28 oSB ++
        copy32 .x28 (oHX + 64) .x28 (oSB + 32) ++ setB (sc (oSB + 65)) 0)))

/-- `Â[e / ℓ, e % ℓ] = RejNTTPoly(ρ ‖ e % ℓ ‖ e / ℓ)`. -/
def expA (P : Prims) (p : Params) (e : Nat) : Prog isa :=
  .seq (.block (setB (sc (oSA + 32)) (e % p.ℓ) ++ setB (sc (oSA + 33)) (e / p.ℓ)))
    (WindowMask.sampled (rejNttAt P (sc oSS) (sc oSA) (aP e)) (aP e))

/-- Copy rho to one 34-byte seed, allowing the unaligned seed stride. -/
def copySeed4 (j : Nat) : List Instr :=
  lea .x10 .x28 (oSA4+34*j) ++ Impl.MlKem.AArch64.copy32 .x28 oSA .x10 0

def setSR (p : Params) (e j : Nat) : List Instr :=
  setB (sc (oSA4+34*j+32)) ((e+j)%p.ℓ) ++ setB (sc (oSA4+34*j+33)) ((e+j)/p.ℓ)

def seedSlot4 (p : Params) (e j : Nat) : Prog isa :=
  .seq (.block (copySeed4 j)) (.block (setSR p e j))

def expA4 (P : Prims) (p : Params) (g : Nat) : Prog isa :=
  .seq (seqR (seedSlot4 p (4*g)) 0 4)
    (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (aP (4*g)))
      (.seq (.block and24) (WindowMask.mask4 (aP (4*g)))))

def expAll (P : Prims) (p : Params) : Prog isa :=
  .seq (seqR (expA4 P p) 0 (p.k*p.ℓ/4))
    (if P.suffix == "_sha3" && p.k*p.ℓ%4 == 2 then
      .seq (seqR (seedSlot4 p (4*(p.k*p.ℓ/4))) 0 2)
       (.seq (callAt "vg_mldsa_rej_ntt_poly2_sha3" RootPair.rootRej2
        [(.x0,.ptr (sc oSA4)),(.x1,.ptr (aP (4*(p.k*p.ℓ/4)))),(.x2,.ptr (sc (oR4 p)))])
        (.seq (.block and24) (WindowMask.maskN (aP (4*(p.k*p.ℓ/4))) 512)))
     else seqR (expA P p) (4*(p.k*p.ℓ/4)) (p.k*p.ℓ%4))

/-- Entry `r` of `s₁ ‖ s₂`: `RejBoundedPoly(ρ′ ‖ r ‖ 0)`. -/
def expS (P : Prims) (p : Params) (r : Nat) : Prog isa :=
  .seq (.block (setB (sc (oSB + 64)) r))
    (WindowMask.sampled (rejBoundedAt P (sc oSS) (sc oSB) p.η (sP p r)) (sP p r))

/-- `ρ` to `pk` and `sk`, and `K` to `sk`. -/
def copies : List Instr :=
  copy32 .x28 oHX .x26 0 ++ copy32 .x28 oHX .x27 0 ++ copy32 .x28 (oHX + 96) .x27 32

/-- Entry `r` of `s₁ ‖ s₂`, packed to `sk`. -/
def packS (P : Prims) (p : Params) (r : Nat) : Prog isa :=
  bitPackAt P (sP p r) p.η p.η (.x27, 128 + lenS p * r) (lenS p)

/-- `ŝ₁[j] = NTT(s₁[j])`. -/
def nttS (P : Prims) (p : Params) (j : Nat) : Prog isa := nttAt P (sc oSS) (sP p j)

/-- Row `i`: `t = NTT⁻¹(Σⱼ Â[i, j] ŝ₁[j]) + s₂[i]`, and its `t₁` to `pk` and `t₀` to `sk`. -/
def row (P : Prims) (p : Params) (i : Nat) : Prog isa :=
  .seq (mulAt P (tP p) (aP (p.ℓ * i)) (sP p 0))
    (.seq (seqR (fun j => mulAddAt P (tP p) (aP (p.ℓ * i + j)) (sP p j)) 1 (p.ℓ - 1))
    (.seq (invNttAt P (sc oSS) (tP p)) (.seq (addAt P (tP p) (sP p (p.ℓ + i)))
    (.seq (power2RoundAt P (tP p) (t1P p) (t0P p))
    (.seq (simpleBitPackAt P (t1P p) 1023 (.x26, 32 + 320 * i) 320)
      (bitPackAt P (t0P p) 4095 4096 (.x27, oT0 p + 416 * i) 416))))))

/-- `tr = H(pk, 64)` to `sk`. -/
def trHashWith (p : Params) : Prog isa := (shake256With c) [⟨.x26, 0, p.pkLen⟩] [⟨.x27, 64, 64⟩]

/-- Everything after the samplers. -/
def restWith (P : Prims) (p : Params) : Prog isa :=
  .seq (.block copies) (.seq (seqR (packS P p) 0 (p.ℓ + p.k)) (.seq (seqR (nttS P p) 0 p.ℓ)
    (.seq (seqR (row P p) 0 p.k) ((trHashWith c) p))))

/-- `vg_mldsa*_keygen` for the parameter set `p`, calling the primitives `P`. -/
def keyGenWith (P : Prims) (p : Params) : Prog isa :=
  .seq (.block pro) (.seq ((seedsWith c) p) (.seq (expAll P p)
    (.seq (seqR (expS P p) 0 (p.ℓ + p.k)) (.seq ((restWith c) P p) (.block epi)))))

def seeds := seedsWith .scalar
def trHash := trHashWith .scalar
def rest := restWith .scalar
def keyGen := keyGenWith .scalar

end WindowKeygen


/-!
# ML-DSA on AArch64: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

`verify P p (pk = x0, mu = x1, sig = x2, scratch = x3) -> w0`:
`ML-DSA.Verify_internal(pk, M′, σ)` (FIPS 204 Algorithm 8) with the message
representative `μ` given (`verifyMu`), for the parameter set `p`, as calls of
the primitives `P` and of the SHA-3 sponge functions (`KeyGen/Frag.lean`).
It keeps `pk` in `x25`, `mu` in `x26`, `sig` in `x27` and `scratch` in
`x28`, and its result so far in `x24`.

The layout of `scratch` (in bytes) is that of key generation where they
share a buffer: the Keccak state at 0 and the sponge functions' working
space at 200, the saved registers at 840; the recomputed commitment hash
`c̃′` at 1024 (`oCT`, at most 64 bytes); the seed of `RejNTTPoly` at 1152
(`oSA`, 34 bytes); the working space of the primitives at 2048 (2048
bytes); and polynomials of 1024 bytes from 4096 (`oP j`): `Â[r, s]` is
polynomial `rℓ + s`, and after them come `w1Encode(w′₁)` (at most 1024
bytes), the hint `h` (`k` polynomials), `z` (`ℓ`), `c`, two temporaries, `w′`
and `w′₁`.

1. `h ← HintBitUnpack` of the last `ω + k` bytes of `σ`
   (`vg_mldsa_hint_bit_unpack`); `x24` is its result, and it returns 0 at
   once if the hint is malformed.
2. `z[i] = BitUnpack` of the `i`-th piece of `σ`, and
   `x24 ← x24 ∧ (‖z[i]‖∞ < γ₁ - β)`; it returns 0 if one of them is not.
3. `ρ` (`pk[0 : 32]`) to the seed, `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)`
   (key generation's `expA`), and `c = SampleInBall(c̃)`. Each sampler's
   result is ANDed into `x24`, and its output masked with it (`sampled`):
   a sampler that fails leaves its output unspecified, and masking makes it
   reduced (zero) without a branch on the result, which is not a function
   of the inputs when it fails.
4. `ẑ[i] = NTT(z[i])`, `ĉ = NTT(c)`; for each row `r`:
   `w′ = NTT⁻¹(Σₛ Â[r, s] ẑ[s] - ĉ · NTT(t₁[r] · 2ᵈ))`, `w′₁ = UseHint(h[r], w′)`,
   and its `SimpleBitPack` to `w1Encode(w′₁)`.
5. `c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)`, and `x24 ← 0` unless `c̃′ = c̃`, without
   a branch.

It returns `x24`. Every address and branch depends only on the pointers,
the public key and the signature (which the function may leak), and not on
the results of the samplers.
-/

namespace WindowVerify

variable (c : Impl.Sha3.AArch64.Callee)

open VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlKem.AArch64 (copy32)
open VG.Spec.MlDsa (Params bitlen q)

section
variable (p : Params)

/-- The length of a packed `z[i]`, `32(1 + bitlen (γ₁ - 1))` bytes. -/
def lenZ : Nat := 32 * (1 + bitlen (p.γ₁ - 1))

/-- The offset of the hint in the signature. -/
def oHint : Nat := p.ctildeLen + lenZ p * p.ℓ

/-- The bound `(q - 1)/(2γ₂) - 1` of the coefficients of `w₁`. -/
def w1Max : Nat := (q - 1) / (2 * p.γ₂) - 1

/-- The length of a packed `w₁[i]`, `32 · bitlen b`. -/
def w1Len : Nat := 32 * bitlen (w1Max p)

/-! ## The layout of the working space -/

/-- `c̃′`. -/
def oCT : Nat := 1024

/-- The polynomial `j` after `Â`. -/
abbrev vP (j : Nat) : Ptr := sc (oP (p.k * p.ℓ + j))

/-- `w1Encode(w′₁)` (at most 1024 bytes), first, so that its offset is below 2¹⁶, which the sponge takes. -/
abbrev bP : Ptr := vP p 0
abbrev hP (r : Nat) : Ptr := vP p (1 + r)
abbrev zP (i : Nat) : Ptr := vP p (1 + p.k + i)
abbrev cP : Ptr := vP p (1 + p.k + p.ℓ)
abbrev tmP : Ptr := vP p (1 + p.k + p.ℓ + 1)
abbrev tm2P : Ptr := vP p (1 + p.k + p.ℓ + 2)
abbrev wP : Ptr := vP p (1 + p.k + p.ℓ + 3)
abbrev w1P : Ptr := vP p (1 + p.k + p.ℓ + 4)

end

/-! ## The comparison -/

/-- One byte of `a ⊕ b` ORed into `x10`. -/
def cmpBody : List Instr :=
  [.ldrb .x9 .x0 0, .ldrb .x11 .x1 0, .logic .eor .x .x9 .x9 .x11, .logic .orr .x .x10 .x10 .x9,
    .addImm .x .x0 .x0 1, .addImm .x .x1 .x1 1, .subImm .x .x2 .x2 1]

/-- `x24 ← 0` unless the `n` bytes at `a` and `b` are equal, without a
branch: `x10` is the OR of the XORs of their bytes, so 0 exactly when they
are equal, and `(x10 - 1) >> 63` then 1, and 0 otherwise. -/
def cmpAnd (a b : Ptr) (n : Nat) : Prog isa :=
  .seq (.block (glue [(.x0, .ptr a), (.x1, .ptr b), (.x2, .imm n)] ++ ([.movz .x .x10 0 0] : List Instr)))
    (.seq (.loop (.block cmpBody) (.nonzero .x .x2))
      (.block [.subImm .x .x10 .x10 1, .lsr .x .x10 .x10 63, .logic .and .w .x24 .x24 .x10]))

/-! ## The pieces -/

section
variable (P : Prims) (p : Params)

/-- `h`, and `x24 ←` the result. -/
def hint : Prog isa :=
  .seq (hintUnpackAt P (.x27, oHint p) (p.ω + p.k) p.ω (hP p 0) (256 * p.k)) (.block and24)

/-- `z[i]`, and `x24 ← x24 ∧ (‖z[i]‖∞ < γ₁ - β)`. -/
def zOne (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.x27, p.ctildeLen + lenZ p * i) (lenZ p) (p.γ₁ - 1) p.γ₁ (zP p i))
    (.seq (normLtAt P (zP p i) (p.γ₁ - p.β)) (.block and24))

/-- `ρ` to the seed, `Â`, and `c`. -/
def samples : Prog isa :=
  .seq (.block (copy32 .x25 0 .x28 oSA)) (.seq (WindowKeygen.expAll P p)
    (WindowMask.sampled (ballAt P (sc oSS) (.x27, 0) p.ctildeLen p.τ (cP p)) (cP p)))

/-- `Σₛ Â[r, s] ẑ[s]` to `w′`. -/
def dot (r : Nat) : Prog isa :=
  let _ := P
  CombDot.dotAt p.ℓ (wP p) (aP (p.ℓ*r)) (zP p 0)

/-- Row `r` of `w′`, `w′₁`, packed to `w1Encode(w′₁)`. -/
def row (r : Nat) : Prog isa :=
  .seq (dot P p r) (.seq (unpackT1At P (.x25, 32 + 320 * r) (tmP p)) (.seq (nttAt P (sc oSS) (tmP p))
    (.seq (mulAt P (tm2P p) (cP p) (tmP p)) (.seq (subAt P (wP p) (tm2P p)) (.seq (invNttAt P (sc oSS) (wP p))
      (.seq (useHintAt P (hP p r) (wP p) p.γ₂ (w1P p))
        (simpleBitPackAt P (w1P p) (w1Max p) ((bP p).1, (bP p).2 + w1Len p * r) (w1Len p))))))))

/-- The NTTs of `z` and `c`, the rows, the hash and the comparison. -/
def computeWith (_c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  .seq (seqR (fun i => nttAt P (sc oSS) (zP p i)) 0 p.ℓ) (.seq (nttAt P (sc oSS) (cP p))
    (.seq (seqR (row P p) 0 p.k)
    (.seq (CommitHash.hashAt (p.k * w1Len p) p.ctildeLen (.x26,0) (bP p) (sc oCT) (sc 0))
      (cmpAnd (sc oCT) (.x27, 0) p.ctildeLen))))

def bodyWith : Prog isa :=
  .seq (hint P p) (ifOk (.seq (seqR (zOne P p) 0 p.ℓ) (ifOk (.seq (samples P p) ((computeWith c) P p)))))

/-- `vg_mldsa*_verify` for the parameter set `p`, calling the primitives `P`. -/
def verifyWith : Prog isa := .seq (.block pro) (.seq ((bodyWith c) P p) (.block epi))

end

def compute := computeWith .scalar
def body := bodyWith .scalar
def verify := verifyWith .scalar

end WindowVerify

def main : IO Unit := do
 for (suffix,callee) in [("sha3",VG.Variants.Keccak.AArch64.Sha3.variant.callee)] do
  let prims := VG.Impl.MlDsa.AArch64.KeyGen.primsWith callee
  for (name,p) in [("44",Spec.MlDsa.mlDsa44),("65",Spec.MlDsa.mlDsa65),("87",Spec.MlDsa.mlDsa87)] do
   let code := printer.function (WindowVerify.verifyWith callee prims p)
   IO.FS.writeFile ("/tmp/rej2-vg-commithash-verify"++name++"-mask-dot-"++suffix++".body") (String.join (code.map (Rust.line printer.call)))