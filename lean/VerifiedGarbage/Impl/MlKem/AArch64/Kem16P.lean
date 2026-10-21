module

public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16

/-! # ML-KEM with the noise's PRF outputs in the matrix's idle Keccak lanes

`Kem16.encaps` and `Kem16.decaps`, with the outputs of `PRF₂` (the noise of
the encryption) computed in Keccak states the matrix leaves idle, rather than
in permutations of their own after it:

* the third state of the `vg_keccak_f1600_x3_sha3` calls of the pairs after
  those hashing `ek` (`z ‖ c`): each main squeeze computes `PRF₂(r, N)` from a
  fresh third state (`slotPrf`), and copies its first 128 bytes to buffer `N`;
* the second state of the singleton (`lastP`), which `Paired.lastSample`
  spends on the same stream as the first: each of its three main squeezes
  computes `PRF₂(r, N)` there (`reinitB`), whose 168-byte squeeze lands in
  buffer `N`.

`r` must be known before these pairs: encapsulation computes `G(m ‖ H(ek))`
right after the pairs hashing `ek` (`gAt`), decapsulation before the matrix
as before. The buffers (`bufOff`), 168 bytes apart, are in `TP` and `PP`,
which nothing uses until the rows of `u`. After the matrix, `noiseP` samples
`SamplePolyCBD₂` of each buffer into its polynomial (and transforms `ŷ`), and
`PRF₂` with its own permutation computes the outputs no lane took; `v` takes
`e₂` from `EP` when a lane computed it.
-/

@[expose] public section
namespace VG.Impl.MlKem.AArch64.Kem16P
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM
open VG.Impl.MlKem.AArch64.Kem16
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
open VG.Impl.MlKem.AArch64.Ntt16.Readonly (nttAtWithW nttInvAtWithW)

/-- The number of PRF outputs the encryption needs: `ŷ`, `e₁` and `e₂`. -/
def prfs (L : KemLay) : Nat := 2 * L.k + 1

/-- The pairs of the matrix. -/
def pairs (L : KemLay) : Nat := L.k * L.k / 2

/-- Whether the matrix ends with a singleton. -/
def single (L : KemLay) : Bool := L.k * L.k % 2 = 1

/-- The PRF outputs the idle lanes compute: three per pair after the first
`hp`, and three in the singleton, at most `prfs`. -/
def placed (L : KemLay) (hp : Nat) : Nat :=
  min (prfs L) (3 * (pairs L - hp) + if single L then 3 else 0)

/-- Buffer `N`: 168 bytes from `TP` on. -/
def bufOff (L : KemLay) (N : Nat) : Nat := TP L + 168 * N

/-- Where `CBD(PRF₂(r, N))` goes: `ŷ[N]`, `e₁[N - k]`, or `e₂` at `EP`. -/
def target (L : KemLay) (N : Nat) : Nat :=
  if N < L.k then yOff L N else if N < 2 * L.k then noiseOff L (N - L.k) else EP L

/-! ## A PRF in the third state -/

/-- `PRF₂(r, N)`'s padded block into the zeroed third state at `ST`:
`r`, then `N` and the suffix `0x1f`, and the final bit `0x80` of byte 135. -/
def prfBlock (N : Nat) : List Instr :=
  zeroState .x28 KEM.ST ++
    (List.range 4).flatMap (fun k => [.ldr .x .x9 .x28 (RB + 8 * k), .str .x .x9 .x28 (KEM.ST + 8 * k)]) ++
    [.movz .x .x9 (BitVec.ofNat 16 (N + 0x1f00)) 0, .str .x .x9 .x28 (KEM.ST + 32),
      .movz .x .x9 0x8000 3, .str .x .x9 .x28 (KEM.ST + 128)]

/-- The first 128 bytes of the third state to buffer `N`, through `x2`. -/
def prfOut (L : KemLay) (N : Nat) : List Instr :=
  ptrTo .x2 .x28 (bufOff L N) ++
    (List.range 16).flatMap fun k => [.ldr .x .x9 .x28 (KEM.ST + 8 * k), .str .x .x9 .x2 (8 * k)]

/-- A main squeeze computing `PRF₂(r, N)` in the third state. -/
def slotPrf (L : KemLay) (N : Nat) : Prog isa :=
  .seq (.block (prfBlock N)) (.seq Hybrid.x3call (.block (Hybrid.squeezeTail ++ prfOut L N)))

/-- Main squeeze `k` of a pair whose first `m` squeezes compute `PRF₂(r, N₀)`, …. -/
def stepP (L : KemLay) (N₀ m k : Nat) : Prog isa :=
  if k < m then slotPrf L (N₀ + k) else Hybrid.plainStep

/-- A pair (`Paired.pair`) whose first `m` main squeezes compute `PRF₂(r, N₀)`, …. -/
def pairP (L : KemLay) (a N₀ m : Nat) : Prog isa :=
  seqs [.block (Paired.init SB SS a (a+1) L.k),
    .seq (stepP L N₀ m 0) (.seq (stepP L N₀ m 1) (stepP L N₀ m 2)),
    .block Rej8.rejConsts,
    Paired.reject 400 (AH+1024*a) .x22 true,
    .block [.str .x .x3 .x19 1680,.str .x .x4 .x19 1688],
    Paired.reject 904 (AH+1024*(a+1)) .x23 true,
    .block [.str .x .x3 .x19 1696,.str .x .x4 .x19 1704,.logic .and .x .x6 .x22 .x23],
    .ite (.zero .x .x6) (Paired.extraPair true) (.block []),
    .block ((Paired.saved.zipIdx.reverse.map fun (r,i) => .ldr .x r .x19 (1800+8*i)))]

/-! ## PRFs in the singleton's second state -/

/-- The second state of the pair at `x19` set to `PRF₂(r, N)`'s padded block. -/
def reinitB (N : Nat) : List Instr :=
  .movz .x .x9 0 0 :: (List.range 25).map (fun w => .str .x .x9 .x19 (16 * w + 8)) ++
    (List.range 4).flatMap (fun k => [.ldr .x .x9 .x28 (RB + 8 * k), .str .x .x9 .x19 (16 * k + 8)]) ++
    [.movz .x .x9 (BitVec.ofNat 16 (N + 0x1f00)) 0, .str .x .x9 .x19 (16 * 4 + 8),
      .movz .x .x9 0x8000 3, .str .x .x9 .x19 (16 * 16 + 8)]

/-- A main squeeze of the singleton, whose second state computes `PRF₂(r, N)`
into the buffer at `x21`. -/
def stepB (N : Nat) : Prog isa := .seq (.block (reinitB N)) Hybrid.plainStep

/-- The singleton (`Paired.lastSample`), its second state computing
`PRF₂(r, N₀)`, `PRF₂(r, N₀ + 1)` and `PRF₂(r, N₀ + 2)` into buffers `N₀`, …. -/
def lastP (L : KemLay) (N₀ : Nat) : Prog isa :=
  let a := L.k*L.k-1
  seqs [.block (Paired.init SB SS a a L.k ++ ptrTo .x21 .x28 (bufOff L N₀)),
    .seq (stepB N₀) (.seq (stepB (N₀ + 1)) (stepB (N₀ + 2))),
    .block Rej8.rejConsts,
    Paired.reject 400 (AH+1024*a) .x22 true,
    .ite (.zero .x .x22) (Paired.fullSample L false (L.k*L.k-1) true) (.block []),
    .block (Paired.saved.zipIdx.reverse.map fun (r,i) => .ldr .x r .x19 (1800+8*i))]

/-! ## The matrix -/

/-- The PRF outputs pair `i` computes, after the first `hp`. -/
def pairCount (L : KemLay) (hp i : Nat) : Nat := min 3 (placed L hp - 3 * (i - hp))

/-- The matrix: the first `hp` pairs hash the message `S` (`Hybrid.pair3`),
then `between` (which computes `r`), then pairs and the singleton compute the
first `placed` PRF outputs. -/
def matrixP (L : KemLay) (S : Hybrid.HSrc) (between : Prog isa) : Prog isa :=
  let hp := Hybrid.hashPairs S
  seqs (((List.range (pairs L)).filter (· < hp)).map (fun i => Hybrid.pair3 L S (2*i) i true) ++
    [between] ++
    ((List.range (pairs L)).filter (hp ≤ ·)).map (fun i =>
      if pairCount L hp i = 0 then Paired.pair L false (2*i) true else pairP L (2*i) (3*(i-hp)) (pairCount L hp i)) ++
    (if single L then
      [if placed L hp ≥ 3 * (pairs L - hp) + 3 then lastP L (3 * (pairs L - hp)) else Paired.lastSample L false true]
      else []))

/-! ## The noise and the encryption -/

/-- `SamplePolyCBD₂` of buffer `N` into its polynomial, transformed for `ŷ`. -/
def outBuf (L : KemLay) (N : Nat) : Prog isa :=
  seqs [.block (ptrTo .x0 .x28 (bufOff L N) ++ ptrTo .x1 .x28 (target L N)), Noise.cbdCall,
    if N < L.k then nttAtWithW (target L N) NS else .block []]

/-- The noise: the buffers of the `n` PRF outputs the matrix computed, then
`PRF₂` and `SamplePolyCBD₂` for the rest of `ŷ` and `e₁`. -/
def noiseP (prf : Nat → Nat → Prog isa) (L : KemLay) (n : Nat) : Prog isa :=
  seqs (((List.range (min n (prfs L))).map (outBuf L)) ++
    ((List.range (2 * L.k)).filter (n ≤ ·)).map fun N =>
      .seq (prf N (target L N)) (if N < L.k then nttAtWithW (target L N) NS else .block []))

/-- `v`, with `e₂` at `EP` already if `e2` (`Kem16.vRest`). -/
def vRestP (prf : Nat → Nat → Prog isa) (L : KemLay) (e2 : Bool) (ek : Reg) (eo : Nat) (m : Reg) (mo : Nat)
    (ct : Reg) (co : Nat) : Prog isa :=
  seqs (((List.range L.k).map fun j => dec12WAt ek (eo + 384 * j) (aOff L 0 j)) ++
    [dotAt (TP L) ((List.range L.k).map fun j => (aOff L 0 j, yOff L j)),
    nttInvAtWithW (TP L) NS, if e2 then .block [] else prf (2 * L.k) (EP L), addWAt (TP L) (EP L),
    widenAt (TP L) (PP L),
    ddAt m mo 1 (EP L), addAt (PP L) (EP L), L.ceLAt (PP L) L.dv ct (co + 32 * L.du * L.k)])

/-- The noise, `u` and `v` (`Kem16.encryptRest`), the first `n` PRF outputs in their buffers. -/
def encryptRestP (prf : Nat → Nat → Prog isa) (L : KemLay) (n : Nat) (ek : Reg) (eo : Nat) (m : Reg)
    (mo : Nat) (ct : Reg) (co : Nat) : Prog isa :=
  .seq (noiseP prf L n) (seqs (((List.range L.k).map (uRow L ct co)) ++
    [vRestP prf L (decide (prfs L ≤ n)) ek eo m mo ct co]))

/-! ## Encapsulation and decapsulation -/

/-- `H(ek)` into `HB`, and `G(m ‖ H(ek))` into `key` and `RB` (`Hybrid.tailH`). -/
abbrev gAt (hash : FixedHashCallers.HashFn) : Prog isa := Hybrid.tailH hash

/-- The encapsulation: the pairs hashing `ek`, `G`, the pairs and singleton
computing PRF outputs, then the noise, `u`, `v` and the epilogue. -/
def encaps (hash : FixedHashCallers.HashFn) (prf : Nat → Nat → Prog isa) (L : KemLay) : Prog isa :=
  .seq (Hybrid.startH L) (.seq (matrixP L (Hybrid.ekSrc L) (gAt hash))
    (.seq (encryptRestP prf L (placed L (Hybrid.hashPairs (Hybrid.ekSrc L))) .x25 0 .x28 MB .x27 0)
      (.block L.kemEpilogue)))

end VG.Impl.MlKem.AArch64.Kem16P
