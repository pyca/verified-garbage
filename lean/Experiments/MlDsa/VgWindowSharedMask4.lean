import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
import VerifiedGarbage.Impl.MlDsa.AArch64.Call
import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Variants.Keccak.AArch64.Sha3
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst
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


namespace CombCopy
open VG.Impl.MlDsa.AArch64.Call
-- Disjoint source/destination regions as in copyChk; handle all lengths, including zero.
def copy (dst src : Ptr) (n : Nat) : Prog isa :=
 .seq (.block (lea .x0 dst.1 dst.2 ++ lea .x1 src.1 src.2)) <|
 .seq (if n/8=0 then .block [] else
  .seq (.block (movV .x2 (n/8)))
   (.loop (.block [.ldr .x .x9 .x1 0,.str .x .x9 .x0 0,
    .addImm .x .x0 .x0 8,.addImm .x .x1 .x1 8,.subImm .x .x2 .x2 1]) (.nonzero .x .x2)))
  (.block ((List.range (n%8)).flatMap fun j => [.ldrb .x9 .x1 j,.strb .x9 .x0 j]))
end CombCopy
/-!
# ML-DSA on AArch64: `vg_mldsa{44,65,87}_sign`

`sign(sk = x0, mu = x1, rnd = x2, sig = x3, scratch = x4) -> w0`:
`ML-DSA.Sign_internal(sk, M′, rnd)` (FIPS 204 Algorithm 7) with the message
representative `μ` given (`Spec.MlDsa.signMu`), for the parameter set `p`,
as calls of the primitives `P` and the sponge functions (`Frag.lean`). It
keeps `scratch` in `x28`, `sk` in `x25`, `mu` in `x26`, `rnd` in `x27` and
`sig` in `x23`, and saves its caller's values of them (and of `x24` and
`x30`) in `scratch`.

1. `ρ` (the first 32 bytes of `sk`) to `RS`, the seed of `RejNTTPoly`, and
   `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)` for the `kℓ` entries, with `w24` the
   AND of the results. If one failed (`w24 = 0`), it returns 0 at once.
2. `ŝ₁`, `ŝ₂` and `t̂₀`: the `NTT` of the `BitUnpack` of their pieces of
   `sk`; and `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`.
3. The rejection sampling loop, at most 814 iterations (`minBounds.sign`),
   with the counter `κ` at `KAP`: the commitment (`y ← ExpandMask(ρ″, κ)`,
   `ŷ = NTT(y)`, `w = NTT⁻¹(Â ŷ)`, and `c̃ = H(μ ‖ w1Encode(HighBits(w)), λ/4)`
   at `CT`), then `c = SampleInBall(c̃)` and, if it succeeded, every validity
   check of the iteration, combined without a branch into `w24`: the norms
   of `z = y + NTT⁻¹(ĉ ŝ₁)`, of `r₀ = LowBits(w - NTT⁻¹(ĉ ŝ₂))` and of
   `ct₀ = NTT⁻¹(ĉ t̂₀)`, and the number of 1s of the hint
   `h = MakeHint(-ct₀, w - cs₂ + ct₀)`. The loop ends when `SampleInBall`
   fails (with `w24 = 0`), when the checks pass (`w24 = 1`), or after 814
   iterations.
4. If `w24 = 1`: `c̃`, the `BitPack` of `z` and `HintBitPack(h)` to `sig`.

Only the calls of `vg_mldsa_rej_ntt_poly` (whose seeds are `ρ` and two
indices), and the branch on their results, depend on `ρ`; only the calls of
`vg_mldsa_sample_in_ball`, and the branch on their results, on `c̃`; only
the branch on the validity checks on whether they passed, and only the call
of `vg_mldsa_hint_bit_pack` on the hint of the signature. Every other
address and branch depends only on the pointers.
-/

namespace WindowUnpack
open VG.Impl.MlKem.AArch64 (movImm mov)
open VG.Impl.MlDsa.AArch64.Pack

def vector (r : VReg) (vals : List Nat) : List Instr :=
 movImm .x9 (BitVec.ofNat 64 vals[0]!) ++ [.vop (.dup .s4 r .x9)] ++
 ((List.range 3).flatMap fun i => movImm .x9 (BitVec.ofNat 64 vals[i+1]!) ++ [.vop (.ins .s4 r (i+1) .x9)])
def byteIndices (r : VReg) (xs : List Nat) : List Instr :=
 let lo := ((List.range 8).map fun i => xs[i]! * 2^(8*i)).foldl (·+·) 0
 let hi := ((List.range 8).map fun i => xs[i+8]! * 2^(8*i)).foldl (·+·) 0
 movImm .x9 (BitVec.ofNat 64 lo) ++ [.vop (.dup .d2 r .x9)] ++
 movImm .x9 (BitVec.ofNat 64 hi) ++ [.vop (.ins .d2 r 1 .x9)]
def idxRegs : List VReg := [.v16,.v17,.v18,.v19]
def outRegs : List VReg := [.v4,.v5,.v6,.v7]
-- Sixteen fields consume exactly 2*d bytes. Last vector overlaps earlier bytes.
def indices (d group : Nat) : List Nat :=
 (List.range 16).map fun k =>
  let byte := k%4
  let field := 4*group+k/4
  let off := d*field/8+byte
  let n := if d=10 then 2 else 3
  if byte>=n then 255
  else if off< (if d=10 then 16 else 32) then off
  else off + (if d=10 then 12 else 48-2*d)
def init (d : Nat) : List Instr :=
 (List.range 4).flatMap (fun i => byteIndices idxRegs[i]! (indices d i)) ++
 vector .v23 ((List.range 4).map fun i => 2^((if d=20 then 4 else 6)-(d*i%8))) ++
 vector .v22 [2^d-1,2^d-1,2^d-1,2^d-1] ++
 (if d=10 then [] else vector .v20 [qNat,qNat,qNat,qNat] ++
  vector .v21 [2^(d-1),2^(d-1),2^(d-1),2^(d-1)]) ++ [.movz .x .x11 16 0]
def one (d i : Nat) : List Instr :=
 let r := outRegs[i]!
 [.vop (.tblN false (if d=10 then 2 else 3) r .v0 idxRegs[i]!),
  .vop (.mul r r .v23),.vop (.shift .ushr .s4 r r (if d=20 then 4 else 6)),
  .vop (.logic .and r r .v22)] ++
 (if d=10 then [.vop (.shift .shl .s4 r r 13)] else
  [.vop (.sub .s4 r .v21 r),.vop (.shift .sshr .s4 .v24 r 31),
   .vop (.logic .and .v24 .v24 .v20),.vop (.add .s4 r r .v24)]) ++ [.strq r .x4 (16*i)]
def body (d : Nat) : List Instr :=
 [.ldrq .v0 .x0 0] ++
 (if d=10 then [.addImm .x .x9 .x0 4,.ldrq .v1 .x9 0]
  else [.ldrq .v1 .x0 16,.addImm .x .x9 .x0 (2*d-16),.ldrq .v2 .x9 0]) ++
 (List.range 4).flatMap (one d) ++
 [.addImm .x .x0 .x0 (2*d),.addImm .x .x4 .x4 64,.subImm .x .x11 .x11 1]
def unpack (d : Nat) : Prog isa := .seq (.block (init d)) (.loop (.block (body d)) (.nonzero .x .x11))
def bitUnpack : Prog isa := sel .x1 640 (unpack 20) (sel .x1 576 (unpack 18) VG.Impl.MlDsa.AArch64.Pack.bitUnpack)
def unpackT1 : Prog isa := .seq (.block [mov .x4 .x1]) (unpack 10)
end WindowUnpack


namespace CombMask4
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
def saved : List Reg := [.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28]
def pro : List Instr :=
 (List.range 10).map (fun i => .str .x (saved[i]!) .x3 (7968+8*i)) ++
 (List.range 8).flatMap (fun i => [.umov .x .x8 (vreg (8+i)) 0,.str .x .x8 .x3 (8048+8*i)]) ++
 [.str .w .x1 .x3 7904,mov .x19 .x3,mov .x20 .x0,mov .x21 .x2]
def epi : List Instr :=
 (List.range 8).flatMap (fun i => [.ldr .x .x8 .x19 (8048+8*i),.vop (.ins .d2 (vreg (8+i)) 0 .x8)]) ++
 (List.range 9).map (fun i => .ldr .x (saved[i+1]!) .x19 (7976+8*i)) ++
 [.ldr .x .x19 .x19 7968]
def seedWord (j : Nat) : List Instr :=
 [.ldr .x .x6 .x3 (8*j),.ldr .x .x7 .x4 (8*j),.vop (.dup .d2 .v0 .x6),
  .vop (.ins .d2 .v0 1 .x7),.strq .v0 .x2 (16*j)]
def lastWord (r n : Reg) : List Instr :=
 [.ldrb r n 64,.ldrb .x8 n 65,.lsl .x .x8 .x8 8,.add .x r r .x8]
def absorb (p : Nat) : List Instr :=
 [.addImm .x .x2 .x19 (400*p),.addImm .x .x3 .x20 (132*p),.addImm .x .x4 .x3 66] ++
 (List.range 8).flatMap seedWord ++ lastWord .x6 .x3 ++ lastWord .x7 .x4 ++
 [.movz .x .x9 31 1,.add .x .x6 .x6 .x9,.add .x .x7 .x7 .x9,
  .vop (.dup .d2 .v0 .x6),.vop (.ins .d2 .v0 1 .x7),.strq .v0 .x2 128,
  .movz .x .x9 0x8000 3,.vop (.dup .d2 .v0 .x9),.strq .v0 .x2 256]
def setup : List Instr :=
 [mov .x22 .x19,.addImm .x .x23 .x19 400,.addImm .x .x24 .x19 840,
  .addImm .x .x25 .x19 1520,.addImm .x .x26 .x19 2200,.addImm .x .x27 .x19 2880,
  .movz .x .x28 5 0]
def squeeze (a b : Reg) : List Instr :=
 (List.range 8).flatMap (fun i =>
 [.vop (.perm .trn1 .d2 .v26 (vreg (2*i)) (vreg (2*i+1))),
 .vop (.perm .trn2 .d2 .v27 (vreg (2*i)) (vreg (2*i+1))),
 .strq .v26 a (16*i),.strq .v27 b (16*i)]) ++
 [.umov .x .x6 .v16 0,.umov .x .x7 .v16 1,.str .x .x6 a 128,.str .x .x7 b 128]
def pair (p a b : Reg) : Prog isa :=
 .seq (.block (Impl.Sha3.AArch64.Neon.Pair.load p)) <|
 .seq (Impl.Sha3.AArch64.Neon.Pair.roundsProg true 24) <|
 .block (Impl.Sha3.AArch64.Neon.Pair.store p ++ squeeze a b)
-- Process each independent pair with its Keccak state resident for allfive blocks.
def residentPair (p a b : Reg) : Prog isa :=
 .seq (.block (Impl.Sha3.AArch64.Neon.Pair.load p ++ [.movz .x .x28 5 0])) <|
 .seq (.loop (.seq (Impl.Sha3.AArch64.Neon.Pair.roundsProg true 24)
  (.block (squeeze a b ++ [.addImm .x a a 136,.addImm .x b b 136,.subImm .x .x28 .x28 1]))) (.nonzero .x .x28)) <|
 .block (Impl.Sha3.AArch64.Neon.Pair.store p)
def unpack (c k : Nat) : Prog isa :=
 .seq (.block [.addImm .x .x0 .x19 (840+680*k),.addImm .x .x4 .x21 (1024*k),.movz .x .x11 16 0]) <|
 .loop (.block (WindowUnpack.body c)) (.nonzero .x .x11)
def unpack4 (c : Nat) : Prog isa :=
 .seq (.block (WindowUnpack.init c)) <|
 .seq (unpack c 0) <| .seq (unpack c 1) <| .seq (unpack c 2) (unpack c 3)
def prog : Prog isa :=
 .seq (.block (pro ++ Rej4.zeroStates ++ absorb 0 ++ absorb 1 ++ setup)) <|
 .seq (.seq (residentPair .x22 .x24 .x25) (residentPair .x23 .x26 .x27)) <|
 .seq (.block [.ldr .w .x27 .x19 7904,.lsr .x .x9 .x27 18]) <|
 .seq (.ite (.zero .x .x9) (unpack4 18) (unpack4 20)) (.block epi)
end CombMask4
/-!
# ML-DSA on AArch64: `vg_mldsa{44,65,87}_sign`

`sign(sk = x0, mu = x1, rnd = x2, sig = x3, scratch = x4) -> w0`:
`ML-DSA.Sign_internal(sk, M′, rnd)` (FIPS 204 Algorithm 7) with the message
representative `μ` given (`Spec.MlDsa.signMu`), for the parameter set `p`,
as calls of the primitives `P` and the sponge functions (`Frag.lean`). It
keeps `scratch` in `x28`, `sk` in `x25`, `mu` in `x26`, `rnd` in `x27` and
`sig` in `x23`, and saves its caller's values of them (and of `x24` and
`x30`) in `scratch`.

1. `ρ` (the first 32 bytes of `sk`) to `RS`, the seed of `RejNTTPoly`, and
   `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)` for the `kℓ` entries, with `w24` the
   AND of the results. If one failed (`w24 = 0`), it returns 0 at once.
2. `ŝ₁`, `ŝ₂` and `t̂₀`: the `NTT` of the `BitUnpack` of their pieces of
   `sk`; and `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`.
3. The rejection sampling loop, at most 814 iterations (`minBounds.sign`),
   with the counter `κ` at `KAP`: the commitment (`y ← ExpandMask(ρ″, κ)`,
   `ŷ = NTT(y)`, `w = NTT⁻¹(Â ŷ)`, and `c̃ = H(μ ‖ w1Encode(HighBits(w)), λ/4)`
   at `CT`), then `c = SampleInBall(c̃)` and, if it succeeded, every validity
   check of the iteration, combined without a branch into `w24`: the norms
   of `z = y + NTT⁻¹(ĉ ŝ₁)`, of `r₀ = LowBits(w - NTT⁻¹(ĉ ŝ₂))` and of
   `ct₀ = NTT⁻¹(ĉ t̂₀)`, and the number of 1s of the hint
   `h = MakeHint(-ct₀, w - cs₂ + ct₀)`. The loop ends when `SampleInBall`
   fails (with `w24 = 0`), when the checks pass (`w24 = 1`), or after 814
   iterations.
4. If `w24 = 1`: `c̃`, the `BitPack` of `z` and `HintBitPack(h)` to `sig`.

Only the calls of `vg_mldsa_rej_ntt_poly` (whose seeds are `ρ` and two
indices), and the branch on their results, depend on `ρ`; only the calls of
`vg_mldsa_sample_in_ball`, and the branch on their results, on `c̃`; only
the branch on the validity checks on whether they passed, and only the call
of `vg_mldsa_hint_bit_pack` on the hint of the signature. Every other
address and branch depends only on the pointers.
-/

namespace CombRound
open VG.Impl.MlDsa.AArch64.Round
open VG.Impl.MlDsa.AArch64.Arith (movW)

def vc (d : VReg) (n : Nat) : List Instr :=
  movW .x9 (BitVec.ofNat 32 n) ++ [.vop (.dup .s4 d .x9)]
def constants (g : Nat) : List Instr :=
  vc .v16 8380417 ++ vc .v17 127 ++ vc .v18 (dMul g) ++
  vc .v19 (2^(dShift g-1)) ++ vc .v20 (dMod g) ++ vc .v21 (2*g) ++
  vc .v22 1 ++ [.vop (.movi0 .v23)]
def hf (g : Nat) (d a : VReg) : List Instr :=
  [.vop (.add .s4 d a .v17), .vop (.shift .ushr .s4 d d 7),
   .vop (.mul d d .v18), .vop (.add .s4 d d .v19),
   .vop (.shift .ushr .s4 d d (dShift g))]
def hb (g : Nat) (d a : VReg) : List Instr := hf g d a ++
  [.vop (.sub .s4 .v7 d .v20), .vop (.shift .sshr .s4 .v7 .v7 31),
   .vop (.logic .and d d .v7)]
def csub (d : VReg) (modulus : VReg := .v16) : List Instr :=
  [.vop (.sub .s4 .v7 d modulus), .vop (.umin d d .v7)]
def cadd (d : VReg) : List Instr :=
  [.vop (.shift .sshr .s4 .v7 d 31), .vop (.logic .and .v7 .v7 .v16),
   .vop (.add .s4 d d .v7)]
def loop (ptrs : List Reg) (body : Nat → List Instr) : Prog isa :=
  .seq (.block [.movz .x .x10 16 0])
   (.loop (.block (([0,16,32,48].flatMap body) ++
     ptrs.map (fun r => .addImm .x r r 64) ++ [.subImm .x .x10 .x10 1])) (.nonzero .x .x10))
def bits (low : Bool) : Prog isa :=
  zext .x1 <| onGamma .x1 .x3 fun g => .seq (.block (constants g)) <|
   loop [.x0,.x2] fun off => [.ldrq .v0 .x0 off] ++ hb g .v1 .v0 ++
     (if low then [.vop (.mls .v0 .v1 .v21)] ++ cadd .v0 ++ [.strq .v0 .x2 off]
      else [.strq .v1 .x2 off])
def power2Round : Prog isa :=
  .seq (.block (vc .v16 8380417 ++ vc .v17 4095)) <|
   loop [.x0,.x1,.x2] fun off => [.ldrq .v0 .x0 off,
    .vop (.add .s4 .v1 .v0 .v17), .vop (.shift .ushr .s4 .v1 .v1 13),
    .vop (.shift .shl .s4 .v2 .v1 13), .vop (.sub .s4 .v0 .v0 .v2)] ++
    cadd .v0 ++ [.strq .v1 .x1 off,.strq .v0 .x2 off]
def normLt : Prog isa :=
 .seq (.block (vc .v16 8380417 ++ [.vop (.dup .s4 .v17 .x1), .vop (.movi0 .v31)])) <|
 .seq (loop [.x0] fun off => [.ldrq .v0 .x0 off,
   .vop (.sub .s4 .v1 .v16 .v0), .vop (.umin .v0 .v0 .v1),
   .vop (.umin .v1 .v0 .v17), .vop (.cmeq .s4 .v1 .v1 .v17),
   .vop (.logic .orr .v31 .v31 .v1)]) <|
 .block [.umov .w .x0 .v31 0,.umov .w .x9 .v31 1,.logic .orr .w .x0 .x0 .x9,
   .umov .w .x9 .v31 2,.logic .orr .w .x0 .x0 .x9,
   .umov .w .x9 .v31 3,.logic .orr .w .x0 .x0 .x9,
   .addImm .w .x0 .x0 1]
def makeHint : Prog isa :=
 zext .x2 <| .seq (onGamma .x2 .x4 fun g =>
  .seq (.block (constants g ++ [.vop (.movi0 .v31)])) <|
  loop [.x0,.x1,.x3] fun off => [.ldrq .v0 .x1 off,.ldrq .v2 .x0 off] ++
   hb g .v1 .v0 ++ [.vop (.add .s4 .v0 .v0 .v2)] ++ csub .v0 ++ hb g .v3 .v0 ++
   [.vop (.cmeq .s4 .v3 .v3 .v1), .vop (.not .v3 .v3),
    .vop (.shift .ushr .s4 .v3 .v3 31), .strq .v3 .x3 off,
    .vop (.add .s4 .v31 .v31 .v3)]) <|
 .block [.umov .w .x0 .v31 0,.umov .w .x9 .v31 1,.add .w .x0 .x0 .x9,
   .umov .w .x9 .v31 2,.add .w .x0 .x0 .x9,
   .umov .w .x9 .v31 3,.add .w .x0 .x0 .x9]
def useHint : Prog isa :=
 zext .x2 <| onGamma .x2 .x4 fun g => .seq (.block (constants g)) <|
 loop [.x0,.x1,.x3] fun off => [.ldrq .v0 .x1 off,.ldrq .v2 .x0 off] ++ hf g .v1 .v0 ++
 [.vop (.mul .v3 .v1 .v21), .vop (.sub .s4 .v3 .v3 .v0),
  .vop (.shift .ushr .s4 .v3 .v3 31), .vop (.shift .shl .s4 .v3 .v3 1),
  .vop (.sub .s4 .v3 .v3 .v22), .vop (.cmeq .s4 .v2 .v2 .v23),
  .vop (.logic .bic .v3 .v3 .v2), .vop (.add .s4 .v1 .v1 .v3),
  .vop (.add .s4 .v1 .v1 .v20)] ++ csub .v1 .v20 ++ csub .v1 .v20 ++ [.strq .v1 .x3 off]
end CombRound

namespace CombHintReuse
open VG VG.AArch64
-- r=x0, gamma=x1, high=x2, low=x3; supports high==r.
def decompose : Prog isa :=
 VG.Impl.MlDsa.AArch64.Round.zext .x1 <|
 VG.Impl.MlDsa.AArch64.Round.onGamma .x1 .x4 fun g =>
 .seq (.block (CombRound.constants g)) <|
 CombRound.loop [.x0,.x2,.x3] fun off => [.ldrq .v0 .x0 off] ++
 CombRound.hb g .v1 .v0 ++ [.vop (.mls .v0 .v1 .v21)] ++ CombRound.cadd .v0 ++
 [.strq .v1 .x2 off,.strq .v0 .x3 off]
-- canonical lowSum=x0, high=x1, gamma=x2, hints=x3. The low sum is bounded
-- by two gamma once all norm checks pass; otherwise the attempt is discarded.
def hint : Prog isa :=
 VG.Impl.MlDsa.AArch64.Round.zext .x2 <|
 .seq (VG.Impl.MlDsa.AArch64.Round.onGamma .x2 .x4 fun g =>
  .seq (.block (CombRound.vc .v16 g ++ CombRound.vc .v17 (8380417-g) ++
    [.vop (.movi0 .v18),.vop (.movi0 .v31)])) <|
  CombRound.loop [.x0,.x1,.x3] fun off =>
   [.ldrq .v0 .x0 off,.ldrq .v1 .x1 off,
    .vop (.sub .s4 .v2 .v16 .v0),.vop (.sub .s4 .v3 .v0 .v17),
    .vop (.logic .and .v2 .v2 .v3),.vop (.shift .sshr .s4 .v2 .v2 31),
    .vop (.cmeq .s4 .v3 .v0 .v17),.vop (.cmeq .s4 .v4 .v1 .v18),
    .vop (.logic .bic .v3 .v3 .v4),.vop (.logic .orr .v2 .v2 .v3),
    .vop (.shift .ushr .s4 .v2 .v2 31),.strq .v2 .x3 off,
    .vop (.add .s4 .v31 .v31 .v2)]) <|
 .block [.umov .w .x0 .v31 0,.umov .w .x9 .v31 1,.add .w .x0 .x0 .x9,
  .umov .w .x9 .v31 2,.add .w .x0 .x0 .x9,.umov .w .x9 .v31 3,.add .w .x0 .x0 .x9]
end CombHintReuse
namespace CombFusedCheck
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Round
open CombRound
def testNorm : List Instr :=
 [.vop (.sub .s4 .v2 .v16 .v0),.vop (.umin .v2 .v0 .v2),
 .vop (.umin .v2 .v2 .v24),.vop (.cmeq .s4 .v2 .v2 .v24),.vop (.logic .orr .v31 .v31 .v2)]
def finish : Prog isa := .block [
 .umov .w .x0 .v31 0,.umov .w .x9 .v31 1,.logic .orr .w .x0 .x0 .x9,
 .umov .w .x9 .v31 2,.logic .orr .w .x0 .x0 .x9,.umov .w .x9 .v31 3,
 .logic .orr .w .x0 .x0 .x9,.addImm .w .x0 .x0 1]
-- canonical inout=x0, canonical addend=x1, bound=w2; return bool w0.
def addNorm : Prog isa :=
 .seq (.block (vc .v16 8380417 ++ [.vop (.dup .s4 .v24 .x2),.vop (.movi0 .v31)])) <|
 .seq (loop [.x0,.x1] fun off => [.ldrq .v0 .x0 off,.ldrq .v1 .x1 off,
 .vop (.add .s4 .v0 .v0 .v1)] ++ csub .v0 ++ [.strq .v0 .x0 off] ++ testNorm) finish
-- inout=x0 (canonical input, high output), subtrahend=x1, low=x2, gamma=w3, bound=w4.
def subLowNorm : Prog isa :=
 zext .x3 <| onGamma .x3 .x5 fun g =>
 .seq (.block (constants g ++ [.vop (.dup .s4 .v24 .x4),.vop (.movi0 .v31)])) <|
 .seq (loop [.x0,.x1,.x2] fun off => [.ldrq .v0 .x0 off,.ldrq .v1 .x1 off,
 .vop (.add .s4 .v0 .v0 .v16),.vop (.sub .s4 .v0 .v0 .v1)] ++ csub .v0 ++
 hb g .v1 .v0 ++ [.strq .v1 .x0 off,.vop (.mls .v0 .v1 .v21)] ++ cadd .v0 ++
 [.strq .v0 .x2 off] ++ testNorm) finish
end CombFusedCheck

namespace CombFusedCheck
-- low→hint=x0, ct0=x1, high=x2, gamma=w3; return u64: low32=count, bit32=normflag.
def hintNorm : Prog isa :=
 .seq (.block (CombRound.vc .v16 8380417 ++
 [.vop (.dup .s4 .v24 .x3),.vop (.dup .s4 .v17 .x3),
 .vop (.sub .s4 .v18 .v16 .v17),.vop (.movi0 .v23),.vop (.movi0 .v30),.vop (.movi0 .v31)])) <|
 .seq (CombRound.loop [.x0,.x1,.x2] fun off =>
 [.ldrq .v0 .x1 off,.ldrq .v3 .x0 off,.ldrq .v4 .x2 off] ++ testNorm ++
 [.vop (.add .s4 .v0 .v0 .v3)] ++ CombRound.csub .v0 ++
 [.vop (.sub .s4 .v2 .v17 .v0),.vop (.sub .s4 .v3 .v0 .v18),
 .vop (.logic .and .v2 .v2 .v3),.vop (.shift .sshr .s4 .v2 .v2 31),
 .vop (.cmeq .s4 .v3 .v0 .v18),.vop (.cmeq .s4 .v4 .v4 .v23),
 .vop (.logic .bic .v3 .v3 .v4),.vop (.logic .orr .v2 .v2 .v3),
 .vop (.shift .ushr .s4 .v2 .v2 31),.strq .v2 .x0 off,.vop (.add .s4 .v30 .v30 .v2)]) <|
 .block [.umov .w .x1 .v31 0,.umov .w .x9 .v31 1,.logic .orr .w .x1 .x1 .x9,
 .umov .w .x9 .v31 2,.logic .orr .w .x1 .x1 .x9,.umov .w .x9 .v31 3,.logic .orr .w .x1 .x1 .x9,.addImm .w .x1 .x1 1,
 .umov .w .x0 .v30 0,.umov .w .x9 .v30 1,.add .w .x0 .x0 .x9,
 .umov .w .x9 .v30 2,.add .w .x0 .x0 .x9,.umov .w .x9 .v30 3,.add .w .x0 .x0 .x9,
 .lsl .x .x1 .x1 32,.logic .orr .x .x0 .x0 .x1]
end CombFusedCheck

namespace CombSignMask4
open VG.Impl.MlDsa.AArch64.Sign

variable (c : Impl.Sha3.AArch64.Callee)

open VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Spec.MlDsa (Params bitlen q)

/-! ## The constants of a parameter set -/

section
variable (p : Params)

/-- `λ/4`, the length of `c̃`. -/
abbrev cLen : Nat := p.ctildeLen
/-- The bound `(q - 1)/(2γ₂) - 1` of the coefficients of `w₁`. -/
abbrev w1Max : Nat := (q - 1) / (2 * p.γ₂) - 1
/-- The length of the encoding of a polynomial of `w₁`. -/
abbrev w1Len : Nat := 32 * bitlen (w1Max p)
/-- The length of the encoding of a polynomial of `z`. -/
abbrev zLen : Nat := 32 * (1 + bitlen (p.γ₁ - 1))
/-- The length of the encoding of a polynomial of `s₁` or `s₂`. -/
abbrev sLen : Nat := 32 * bitlen (2 * p.η)

/-- The offsets of `s₁[r]`, `s₂[i]` and `t₀[i]` in `sk`. -/
abbrev skS1 (r : Nat) : Nat := 128 + sLen p * r
abbrev skS2 (i : Nat) : Nat := 128 + sLen p * p.ℓ + sLen p * i
abbrev skT0 (i : Nat) : Nat := 128 + sLen p * (p.ℓ + p.k) + 416 * i

/-- The offsets of `z[r]` and of the hint in `sig`. -/
abbrev sigZ (r : Nat) : Nat := cLen p + zLen p * r
abbrev sigH : Nat := cLen p + zLen p * p.ℓ

/-! ## The polynomials of the working space

`ĉ` (0), four temporaries (1–4), then `h` (`k`), `y` (`ℓ`), `ŷ` (`ℓ`),
`w` (`k`), `ŝ₁` (`ℓ`), `ŝ₂` (`k`), `t̂₀` (`k`) and `Â` (`kℓ`, row by row). -/

abbrev pS (i : Nat) : Ptr := sc (oP i)
abbrev cP : Ptr := pS 0
abbrev t1P : Ptr := pS 1
abbrev t2P : Ptr := pS 2
abbrev t3P : Ptr := pS 3
abbrev t4P : Ptr := pS 4
abbrev hP (i : Nat) : Ptr := pS (5 + i)
abbrev yP (r : Nat) : Ptr := pS (5 + p.k + r)
abbrev yhP (r : Nat) : Ptr := pS (5 + p.k + p.ℓ + r)
abbrev wP (i : Nat) : Ptr := pS (5 + p.k + 2 * p.ℓ + i)
abbrev s1P (r : Nat) : Ptr := pS (5 + 2 * p.k + 2 * p.ℓ + r)
abbrev s2P (i : Nat) : Ptr := pS (5 + 2 * p.k + 3 * p.ℓ + i)
abbrev t0P (i : Nat) : Ptr := pS (5 + 3 * p.k + 3 * p.ℓ + i)
abbrev aP (i j : Nat) : Ptr := pS (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * i + j)

end

/-! ## The pieces -/

section
variable (P : Prims) (p : Params)

/-- `Â[e / ℓ, e % ℓ] = RejNTTPoly(ρ ‖ e % ℓ ‖ e / ℓ)`, with `ρ` at `RS`. -/
def sampleE (e : Nat) : Prog isa :=
  .seq (.block (setB (sc (oRS + 32)) (e % p.ℓ) ++ setB (sc (oRS + 33)) (e / p.ℓ))) (rejAt P (aP p (e / p.ℓ) (e % p.ℓ)))

/-- Scratch for the four simultaneous SHAKE streams, after the matrix. -/
def oR4 : Nat := oP (5+4*p.k+3*p.ℓ+p.k*p.ℓ)

def seedSlot4 (e j : Nat) : Prog isa :=
  .seq (.block (lea .x10 .x28 (oRS4+34*j) ++ Impl.MlKem.AArch64.copy32 .x28 oRS .x10 0))
    (.block (setB (sc (oRS4+34*j+32)) ((e+j)%p.ℓ) ++ setB (sc (oRS4+34*j+33)) ((e+j)/p.ℓ)))

def sample4 (g : Nat) : Prog isa :=
  .seq (seqR (seedSlot4 p (4*g)) 0 4)
    (.seq (callAt ("vg_mldsa_rej_ntt_poly4"++P.suffix) P.rej4
      [(.x0,.ptr (sc oRS4)),(.x1,.ptr (pS (5+4*p.k+3*p.ℓ+4*g))),(.x2,.ptr (sc (oR4 p)))]) (.block and24))

def sampleAll : Prog isa :=
  .seq (seqR (sample4 P p) 0 (p.k*p.ℓ/4)) (seqR (sampleE P p) (4*(p.k*p.ℓ/4)) (p.k*p.ℓ%4))

/-- `ρ` to four seed slots, and matrix expansion in batches of four. -/
def expandA : Prog isa :=
  .seq (.block (Impl.MlKem.AArch64.copy32 .x25 0 .x28 oRS)) (sampleAll P p)

/-- `ŝ₁[r]`. -/
def decS1 (r : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.x25, skS1 p r) (sLen p) p.η p.η (s1P p r)) (nttAt P (s1P p r))

/-- `ŝ₂[i]`. -/
def decS2 (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.x25, skS2 p i) (sLen p) p.η p.η (s2P p i)) (nttAt P (s2P p i))

/-- `t̂₀[i]`. -/
def decT0 (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.x25, skT0 p i) 416 4095 4096 (t0P p i)) (nttAt P (t0P p i))

/-- `ŝ₁`, `ŝ₂`, `t̂₀`, and `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`. -/
def decodeWith : Prog isa :=
  .seq (seqR (decS1 P p) 0 p.ℓ) (.seq (seqR (decS2 P p) 0 p.k) (.seq (seqR (decT0 P p) 0 p.k)
    ((shakeAtWith c) [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, oMS, 64⟩)))

/-! ### An iteration -/

/-- The two bytes of `κ + r` to `MS + 64`, through `x9`. -/
def setKappa (r : Nat) : List Instr :=
  [.ldr .x .x9 .x28 oKAP, .addImm .x .x9 .x9 r, .strb .x9 .x28 (oMS + 64), .lsr .x .x9 .x9 8,
    .strb .x9 .x28 (oMS + 65)]

/-- `y[r]` and `ŷ[r] = NTT(y[r])`. -/
def maskR (r : Nat) : Prog isa :=
  .seq (.block (setKappa r)) (.seq (maskAt P p.γ₁ (yP p r)) (.seq (CombCopy.copy (yhP p r) (yP p r) 1024) (nttAt P (yhP p r))))

/-- `w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])`. -/
def rowW (i : Nat) : Prog isa :=
  .seq (CombDot.dotAt p.ℓ (wP p i) (aP p i 0) (yhP p 0)) (invNttAt P (wP p i))

/-- `w1Encode(HighBits(w[i]))` to `W1 + i · w1Len`. -/
def w1R (i : Nat) : Prog isa :=
  .seq (highBitsAt P (wP p i) p.γ₂ t1P) (simpleBitPackAt P t1P (w1Max p) (sc (oW1 + w1Len p * i)) (w1Len p))

def mask4Seed (g j : Nat) : Prog isa :=
 .seq (CombCopy.copy (sc (1632+66*j)) (sc oMS) 64) <|
 .block [.ldr .x .x9 .x28 oKAP,.addImm .x .x9 .x9 (4*g+j),
  .strb .x9 .x28 (1632+66*j+64),.lsr .x .x9 .x9 8,.strb .x9 .x28 (1632+66*j+65)]
def mask4Group (g : Nat) : Prog isa :=
 .seq (seqR (mask4Seed g) 0 4) <|
 .seq (.block (glue [(.x0,.ptr (sc 1632)),(.x1,.imm p.γ₁),
   (.x2,.ptr (yP p (4*g))),(.x3,.ptr (sc (oR4 p)))])) <|
 .seq CombMask4.prog <|
 seqR (fun j => .seq (CombCopy.copy (yhP p j) (yP p j) 1024) (nttAt P (yhP p j))) (4*g) 4

/-- `y`, `ŷ`, `w`, `w₁` and `c̃ = H(μ ‖ w1Encode(w₁), λ/4)` to `CT`. -/
def commitWith (_c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  .seq (.seq (seqR (mask4Group P p) 0 (p.ℓ/4)) (seqR (maskR P p) (4*(p.ℓ/4)) (p.ℓ%4))) (.seq (seqR (rowW P p) 0 p.k) (.seq (seqR (w1R P p) 0 p.k)
    (CommitHash.hashAt (p.k * w1Len p) (cLen p) (.x26,0) (sc oW1) (sc oCT) (sc 0))))

/-- `z[r] = y[r] + NTT⁻¹(ĉ ŝ₁[r])` (in `y[r]`), and its norm. -/
def zR (r : Nat) : Prog isa :=
 .seq (mulAt P t1P cP (s1P p r)) <| .seq (invNttAt P t1P) <|
 .seq (callAt "vg_mldsa_add_norm" CombFusedCheck.addNorm
  [(.x0,.ptr (yP p r)),(.x1,.ptr t1P),(.x2,.imm (p.γ₁-p.β))]) (.block and24)

def r0R (i : Nat) : Prog isa :=
 .seq (mulAt P t1P cP (s2P p i)) <| .seq (invNttAt P t1P) <|
 .seq (callAt "vg_mldsa_sub_low_norm" CombFusedCheck.subLowNorm
  [(.x0,.ptr (wP p i)),(.x1,.ptr t1P),(.x2,.ptr (hP i)),(.x3,.imm p.γ₂),(.x4,.imm (p.γ₂-p.β))]) (.block and24)
def hR (i : Nat) : Prog isa :=
 .seq (mulAt P t3P cP (t0P p i)) <| .seq (invNttAt P t3P) <|
 .seq (callAt "vg_mldsa_hint_norm" CombFusedCheck.hintNorm
 [(.x0,.ptr (hP i)),(.x1,.ptr t3P),(.x2,.ptr (wP p i)),(.x3,.imm p.γ₂)])
 (.block ([.lsr .x .x1 .x0 32,.logic .and .w .x24 .x24 .x1] ++ onesAdd))

/-- `x24 ← x24 ∧ (ONES ≤ ω)`: `ONES - (ω + 1)` is negative exactly then. -/
def onesOk : List Instr :=
  [.ldr .x .x9 .x28 oONES, .subImm .x .x9 .x9 (p.ω + 1), .lsr .x .x9 .x9 63, .logic .and .w .x24 .x24 .x9]

/-- `KAP ← KAP + ℓ`, through `x9`. -/
def kapAdd : List Instr := [.ldr .x .x9 .x28 oKAP, .addImm .x .x9 .x9 p.ℓ, .str .x .x9 .x28 oKAP]

/-- The validity checks of an iteration, combined into `x24`; then, if they
passed, `CNT ← 1` (the loop ends with `w24 = 1`), and otherwise `κ ← κ + ℓ`. -/
def checks : Prog isa :=
  .seq (nttAt P cP) (.seq (.block ([.movz .x .x24 1 0] ++ setQ (sc oONES) 0))
    (.seq (seqR (zR P p) 0 p.ℓ) (.seq (seqR (r0R P p) 0 p.k) (.seq (seqR (hR P p) 0 p.k)
      (.seq (.block (onesOk p)) (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p))))))))

/-- `CNT ← CNT - 1`, left in `x9`, which the loop tests. -/
def cntDec : List Instr := [.ldr .x .x9 .x28 oCNT, .subImm .x .x9 .x9 1, .str .x .x9 .x28 oCNT]

/-- An iteration: the commitment, `SampleInBall`, and the checks if it
succeeded (and otherwise `x24 ← 0`, `CNT ← 1`); then `CNT ← CNT - 1`. -/
def iterWith : Prog isa :=
  .seq ((commitWith c) P p) (.seq (ballAt P (cLen p) p.τ cP)
    (.seq (.ite (.nonzero .w .x0) (checks P p) (.block ([.movz .x .x24 0 0] ++ setQ (sc oCNT) 1)))
      (.block cntDec)))

/-- The rejection sampling loop: `κ ← 0`, `CNT ← 814`, and iterations while
`CNT ≠ 0`. -/
def signLoopWith : Prog isa :=
  .seq (.block (setQ (sc oKAP) 0 ++ setQ (sc oCNT) 814)) (.loop ((iterWith c) P p) (.nonzero .x .x9))

/-! ### The signature -/

/-- `BitPack(z[r], γ₁ - 1, γ₁)` to `sig`. -/
def packZ (r : Nat) : Prog isa := bitPackAt P (yP p r) (p.γ₁ - 1) p.γ₁ (.x23, sigZ p r) (zLen p)

/-- `c̃`, `z` and `HintBitPack(h)` to `sig`. -/
def output : Prog isa :=
  .seq (CombCopy.copy (.x23, 0) (sc oCT) (cLen p)) (.seq (seqR (packZ P p) 0 p.ℓ)
    (hintBitPackAt P (hP 0) (256 * p.k) p.ω (.x23, sigH p) (p.ω + p.k)))

/-- Once `Â` is sampled: the private key, the loop, and the signature if the
loop succeeded. -/
def restWith : Prog isa := .seq ((decodeWith c) P p) (.seq ((signLoopWith c) P p) (ifOk (output P p)))

end

/-- `vg_mldsa{44,65,87}_sign` for the parameter set `p`, with the primitives `P`. -/
def signWith (P : Prims) (p : Params) : Prog isa :=
  .seq (.block pro) (.seq (expandA P p) (.seq (ifOk ((restWith c) P p)) (.block epi)))

def decode := decodeWith .scalar
def commit := commitWith .scalar
def iter := iterWith .scalar
def signLoop := signLoopWith .scalar
def rest := restWith .scalar
def sign := signWith .scalar

end CombSignMask4



namespace WindowShared
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
local instance : Inhabited (Prog isa) := ⟨.block []⟩
def symbol := "vg_keccak_resident_sha3_internal"
def resident : Prog isa := .block rounds
partial def straight : Prog isa → Option (List Instr)
 | .block xs => some xs
 | .seq a b => do return (←straight a)++(←straight b)
 | _ => none
partial def splitBlock (xs : List Instr) : Prog isa :=
 if rounds.isPrefixOf xs then .seq (.call symbol resident) (splitBlock (xs.drop rounds.length))
 else match xs with
 | [] => .block []
 | x::rest => .seq (.block [x]) (splitBlock rest)
partial def rewrite (c : Prog isa) : Prog isa :=
 match straight c with
 | some xs => splitBlock xs
 | none => match c with
   | .seq a b => .seq (rewrite a) (rewrite b)
   | .ite q a b => .ite q (rewrite a) (rewrite b)
   | .loop b q => .loop (rewrite b) q
   | .frame i b j => .frame i (rewrite b) j
   | _ => c
def wrap (c : Prog isa) : Prog isa := .frame (.push .x30) (rewrite c) (.pop .x30)
def emit (path : String) (c : Prog isa) : IO Unit := do
 IO.FS.writeFile path (String.join ((printer.function (wrap c)).map (Rust.line printer.call)))
end WindowShared

def main : IO Unit := WindowShared.emit "/tmp/vg-window-shared-mask4.body" (CombMask4.prog)
