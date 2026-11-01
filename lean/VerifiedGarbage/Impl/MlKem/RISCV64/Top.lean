module

public import VerifiedGarbage.Impl.MlKem.RISCV64.Sample
public import VerifiedGarbage.Impl.MlKem.RISCV64.Ntt
public import VerifiedGarbage.Impl.MlKem.RISCV64.Codec
public import VerifiedGarbage.Impl.MlKem.RISCV64.Compress
public import VerifiedGarbage.Spec.MlKem

/-!
# ML-KEM on RISC-V: key generation, encapsulation, decapsulation

As on PPC64LE (`Impl/MlKem/PPC64LE/Top.lean`): the top-level functions of
ML-KEM-768 and ML-KEM-1024, for any parameter set `K : KemLay`, are
sequences of calls of the verified primitives and SHA-3 functions, on
buffers at fixed offsets in `scratch` and in the arguments. Every argument,
the calls' and ours, is in a register. The pointers are kept in callee-saved
registers, which the callees preserve (the sponge functions and
`vg_mlkem_sample_ntt` save and restore those they use): `s11` is `scratch`
throughout, and `s7`–`s10` the other buffers; `s6` and `s5` count loops,
`s4` is the return value: 1, or 0 once a `SampleNTT` has not finished
within 280 iterations, and `s3` is the pointer `key` of decapsulation (a
pointer loaded from memory would be secret to the taint analysis, which
takes all of memory to be). They save our caller's `s3`–`s11` and our return
address in `scratch`, so the only stack they use is that of their callees
(1168 bytes).

`scratch` holds, at these offsets:

* `0`: the Keccak state;
* `920`: the 64 bytes of `G`, `ρ ‖ σ` or `K ‖ r`, so `σ` (or `r`) is at
  `952`, the seed of `PRF`, followed by its counter `N`; `992`: `H(ek)`;
  `1024`: the message: a copy of `m` in encapsulation, `m'` in
  decapsulation; `1056`: the 128 bytes of a `PRF`; `1184`: the byte `k` of
  `G(d ‖ k)`; `1216`: `K̄`; `1248`: the seed `ρ ‖ j ‖ i` of `SampleNTT`;
  `1288`: our caller's `s3`–`s11` and our return address;
* `2048 + 1024 j` for `j < 3k + 5`: polynomials (`oPoly`), then the working
  space of `vg_mlkem_sample_ntt` (2048 bytes), that of the NTTs and
  `vg_mlkem_multiply_ntts` (1024 bytes), then the ciphertext `c'` of
  decapsulation's re-encryption; `24576`: a copy of the ciphertext `c` of
  decapsulation.

An immediate is 12 bits, so the addresses of polynomials, all multiples of
1024 past `scratch`, are a shift of a small number (`polyAddr`, `slotAt`),
and the offsets into `dk` past `384k` are taken from `dk + 384k`.

Every address is a pointer plus a constant or a counter, every branch is on
a counter, on whether a `SampleNTT` finished (a function of the public seed
`ρ` and two indices), or on nothing secret; decapsulation compares `c` and
`c'` by the OR of the XORs of their bytes, and selects `K'` or `K̄` by a
mask, in constant time.
-/

@[expose] public section

namespace VG.Impl.MlKem.RISCV64

open VG.RISCV64
open VG.Impl.Sha3.RISCV64.Stream (mov)

/-! ## The layout of `scratch` -/

abbrev oG : Nat := 920
abbrev oSigma : Nat := 952
abbrev oHek : Nat := 992
abbrev oMsg : Nat := 1024
abbrev oPrf : Nat := 1056
abbrev oK : Nat := 1184
abbrev oKbar : Nat := 1216
abbrev oSeed : Nat := 1248
abbrev oSave : Nat := 1288
/-- The polynomial `k`. -/
abbrev oPoly (k : Nat) : Nat := 2048 + 1024 * k
/-- The copy of the ciphertext, the polynomial slot 22. -/
abbrev oCin : Nat := oPoly 22

/-! ## Building blocks -/

/-- `d ← s11 + oPoly j`, as `s11 + 1024 (j + 2)`. -/
def polyAddr (d : Reg) (j : Nat) : List Instr := [.li d (j + 2), .shift .sll .d d d 10, .add d .s11 d]

/-- `d ← s11 + oPoly j + 1024 c`: polynomial `c` of an array of them from
polynomial `j`. -/
def slotAt (d c : Reg) (j : Nat) : List Instr := [.addi d c (j + 2), .shift .sll .d d d 10, .add d .s11 d]

/-- `d ← b + m c`, through `t0`. -/
def atMul (d b c : Reg) (m : Nat) : List Instr := [.li .t0 m, .mul .t0 c .t0, .add d b .t0]

/-- The counter `c` incremented, and `t0 = c - n`: zero when it reaches `n`. -/
def count (c : Reg) (n : Nat) : List Instr := [.addi c c 1, .addi .t0 c (-(n : Int))]

/-- A buffer: `off` bytes past the pointer in `base`, of `len` bytes. -/
structure Piece where
  base : Reg
  off : Nat
  len : Nat

/-- The position: 0 at `first`, or the position the previous call returned. -/
def posArg (first : Bool) : Instr := if first then .li .a2 0 else mov .a2 .a0

/-- The arguments of `absorb` or `squeeze`: the Keccak state, the rate, the
position, the piece `p` and its length. -/
def spongeArgs (rate : Nat) (first : Bool) (p : Piece) : List Instr :=
  [posArg first, mov .a0 .s11, .li .a1 rate, .addi .a3 p.base p.off, .li .a4 p.len]

def callAbsorb : Prog isa := .call Spec.Sha3.absorbApi.name Impl.Sha3.RISCV64.Stream.absorb
def callPad : Prog isa := .call Spec.Sha3.padApi.name Impl.Sha3.RISCV64.Stream.pad
def callSqueeze : Prog isa := .call Spec.Sha3.squeezeApi.name Impl.Sha3.RISCV64.Stream.squeeze

/-- Absorb the pieces `ps`. -/
def absorbs (rate : Nat) : Bool → List Piece → Prog isa
  | _, [] => .block []
  | first, p :: ps => .seq (.block (spongeArgs rate first p)) (.seq callAbsorb (absorbs rate false ps))

/-- Squeeze into the pieces `ps`. -/
def squeezes (rate : Nat) : Bool → List Piece → Prog isa
  | _, [] => .block []
  | first, p :: ps => .seq (.block (spongeArgs rate first p)) (.seq callSqueeze (squeezes rate false ps))

/-- The hash of the message `ins` (pieces, absorbed after one another) into
`outs`, with the rate `rate` and the domain-separation suffix `sfx`. -/
def hash (rate sfx : Nat) (ins outs : List Piece) : Prog isa :=
  .seq (.block (zeroState .s11)) <|
  .seq (absorbs rate true ins) <|
  .seq (.block [mov .a2 .a0, mov .a0 .s11, .li .a1 rate, .li .a3 sfx])
    (.seq callPad (squeezes rate true outs))

def copyBody : List Instr :=
  [.load .b .a3 .a0 0, .store .b .a3 .a1 0, .addi .a0 .a0 1, .addi .a1 .a1 1, .addi .a2 .a2 (-1)]

/-- Copy `len` bytes from `sb + so` to `db + dO`. -/
def copy (sb : Reg) (so : Nat) (db : Reg) (dO len : Nat) : Prog isa :=
  .seq (.block [.addi .a0 sb so, .addi .a1 db dO, .li .a2 len]) (.loop (.block copyBody) (.nonzero .a2))

def zeroBody : List Instr := [.store .w .a1 .a0 0, .addi .a0 .a0 4, .addi .a2 .a2 (-1)]

/-- The polynomial `j` of `scratch` set to zero. -/
def zeroPoly (j : Nat) : Prog isa :=
  .seq (.block (polyAddr .a0 j ++ [.li .a1 0, .li .a2 256])) (.loop (.block zeroBody) (.nonzero .a2))

/-! ## The primitives -/

def callAdd : Prog isa := .call "vg_mlkem_add" add
def callSub : Prog isa := .call "vg_mlkem_sub" sub
def callMul : Prog isa := .call "vg_mlkem_multiply_ntts" multiplyNTTs
def callNtt : Prog isa := .call "vg_mlkem_ntt" ntt
def callNttInv : Prog isa := .call "vg_mlkem_inv_ntt" nttInv
def callCbd2 : Prog isa := .call "vg_mlkem_cbd2" cbd2
def callEncode12 : Prog isa := .call "vg_mlkem_encode12" encode12
def callDecode12 : Prog isa := .call "vg_mlkem_decode12" decode12
def callCompress : Prog isa := .call "vg_mlkem_compress_encode" compressEncode
def callDecompress : Prog isa := .call "vg_mlkem_decode_decompress" decodeDecompress
def callSample : Prog isa := .call "vg_mlkem_sample_ntt" sampleNTT

/-- The indices of the seed: `ρ ‖ j ‖ i` for `Â[i, j]`, with `i` in `s6` and
`j` in `s5`, or `ρ ‖ i ‖ j` for `Â[j, i]` (`transpose`). -/
def seedBytes (transpose : Bool) : List Instr :=
  if transpose then [.store .b .s6 .s11 (oSeed + 32), .store .b .s5 .s11 (oSeed + 33)]
  else [.store .b .s5 .s11 (oSeed + 32), .store .b .s6 .s11 (oSeed + 33)]

/-! ## The parameter sets -/

/-- What the top-level functions of a parameter set need: its parameters
`p` (`k`, `d_u`, `d_v`), the size of `scratch` its contracts give, and the
primitives (and their symbols) that compress to and decompress from `d_u`
and `d_v` bits. -/
structure KemLay where
  p : Spec.MlKem.Params
  scratch : Nat
  compressSym : String
  compress : Prog isa
  decompressSym : String
  decompress : Prog isa

namespace KemLay

variable (K : KemLay)

abbrev k : Nat := K.p.k
abbrev du : Nat := K.p.du
abbrev dv : Nat := K.p.dv

/-- The sum of a row (polynomial `3k + 2`), a product (`3k + 3`) and a
sampled entry of `Â` (`3k + 4`). -/
abbrev jAcc : Nat := 3 * K.k + 2
abbrev jTmp : Nat := 3 * K.k + 3
abbrev jAhat : Nat := 3 * K.k + 4
/-- The working space of `vg_mlkem_sample_ntt` (2048 bytes), of the NTTs and
`vg_mlkem_multiply_ntts` (1024 bytes), and the ciphertext `c'` of
decapsulation's re-encryption. -/
abbrev jSample : Nat := 3 * K.k + 5
abbrev jNtt : Nat := 3 * K.k + 7
abbrev jCt : Nat := 3 * K.k + 8

/-- The bytes of `ek`, of `dk`, of `ByteEncode_{d_u}(Compress_{d_u}(u[i]))`, of
`ByteEncode_{d_v}(Compress_{d_v}(v))`, and of the ciphertext. -/
abbrev ekLen : Nat := 384 * K.k + 32
abbrev dkLen : Nat := 768 * K.k + 96
abbrev uLen : Nat := 32 * K.du
abbrev vLen : Nat := 32 * K.dv
abbrev ctLen : Nat := K.uLen * K.k + K.vLen

def callCU : Prog isa := .call K.compressSym K.compress
def callDU : Prog isa := .call K.decompressSym K.decompress

/-! ## Sampling -/

/-- `SamplePolyCBD₂(PRF₂(σ, N))` into polynomial `k + N`, with `N` in `s6`
(and `σ ‖ N` at `952`), then its NTT if `withNtt`. -/
def prfBody (withNtt : Bool) (N₁ : Nat) : Prog isa :=
  .seq (.block [.store .b .s6 .s11 (oSigma + 32)]) <|
  .seq (hash 136 0x1f [⟨.s11, oSigma, 33⟩] [⟨.s11, oPrf, 128⟩]) <|
  .seq (.block (.addi .a0 .s11 oPrf :: slotAt .a1 .s6 K.k)) <|
  .seq callCbd2 <|
  .seq (if withNtt then .seq (.block (slotAt .a0 .s6 K.k ++ polyAddr .a1 K.jNtt)) callNtt
    else .block [])
    (.block (count .s6 N₁))

/-- `prfBody` for `N` from `N₀` to `N₁ - 1`. -/
def prfLoop (withNtt : Bool) (N₀ N₁ : Nat) : Prog isa :=
  .seq (.block [.li .s6 N₀]) (.loop (K.prfBody withNtt N₁) (.nonzero .t0))

/-- Entry `j` of row `i` (in `s5` and `s6`) of `Â` (or of `Â^⊺`) sampled,
and its product with polynomial `k + j` added to the sum. -/
def rowBody (transpose : Bool) : Prog isa :=
  .seq (.block (seedBytes transpose ++ .addi .a0 .s11 oSeed :: polyAddr .a1 K.jAhat ++ polyAddr .a2 K.jSample)) <|
  .seq callSample <|
  .seq (.block [.logic .and .s4 .s4 .a0]) <|
  .seq (.ite (.zero .a0) (.block (slotAt .a1 .s5 K.k)) (.block (polyAddr .a1 K.jAhat))) <|
  .seq (.block (polyAddr .a0 K.jTmp ++ slotAt .a2 .s5 K.k ++ polyAddr .a3 K.jNtt)) <|
  .seq callMul <|
  .seq (.block (polyAddr .a0 K.jAcc ++ polyAddr .a1 K.jTmp)) <|
  .seq callAdd (.block (count .s5 K.k))

/-- Row `i` of `Â ∘ v̂` (or of `Â^⊺ ∘ v̂`), `v̂` polynomials `k` to `2k - 1`,
into polynomial `3k + 2`. -/
def rowSum (transpose : Bool) : Prog isa :=
  .seq (zeroPoly K.jAcc) (.seq (.block [.li .s5 0]) (.loop (K.rowBody transpose) (.nonzero .t0)))

def dotBody : Prog isa :=
  .seq (.block (polyAddr .a0 K.jTmp ++ slotAt .a1 .s5 0 ++ slotAt .a2 .s5 K.k ++ polyAddr .a3 K.jNtt)) <|
  .seq callMul <|
  .seq (.block (polyAddr .a0 K.jAcc ++ polyAddr .a1 K.jTmp)) <|
  .seq callAdd (.block (count .s5 K.k))

/-- The sum of the products of polynomials `j` and `k + j`, into polynomial
`3k + 2`. -/
def dot : Prog isa := .seq (zeroPoly K.jAcc) (.seq (.block [.li .s5 0]) (.loop K.dotBody (.nonzero .t0)))

end KemLay

/-! ## Saving our caller's registers -/

/-- The callee-saved registers we use, and where they are saved in `scratch`. -/
def topSaved : List (Reg × Nat) :=
  [(.s3, oSave), (.s4, oSave + 8), (.s5, oSave + 16), (.s6, oSave + 24), (.s7, oSave + 32),
    (.s8, oSave + 40), (.s9, oSave + 48), (.s10, oSave + 56), (.s11, oSave + 64)]

/-- Our caller's registers and our return address saved, with `scratch` in `b`. -/
def topSave (b : Reg) : List Instr :=
  topSaved.map (fun (r, d) => .store .d r b d) ++ ([.store .d .ra b (oSave + 72)] : List Instr)

/-- The return value, and our caller's registers and our return address
restored (`s11`, the base, last). -/
def topEnd : List Instr :=
  [mov .a0 .s4, .load .d .ra .s11 (oSave + 72), .load .d .s3 .s11 oSave, .load .d .s4 .s11 (oSave + 8),
    .load .d .s5 .s11 (oSave + 16), .load .d .s6 .s11 (oSave + 24), .load .d .s7 .s11 (oSave + 32),
    .load .d .s8 .s11 (oSave + 40), .load .d .s9 .s11 (oSave + 48), .load .d .s10 .s11 (oSave + 56),
    .load .d .s11 .s11 (oSave + 64)]

/-! ## `vg_mlkem<n>_keygen(seed = a0, ek = a1, dk = a2, scratch = a3) -> a0` -/

namespace KemLay

variable (K : KemLay)

def kgSetup : List Instr :=
  topSave .a3 ++ ([mov .s10 .a0, mov .s9 .a1, mov .s8 .a2, mov .s11 .a3, .li .t0 K.k, .store .b .t0 .s11 oK] :
    List Instr)

/-- Row `i` (in `s6`) of `t̂ = Â ∘ ŝ + ê`, encoded into `ek`. -/
def kgRowBody : Prog isa :=
  .seq (K.rowSum false) <|
  .seq (.block (polyAddr .a0 K.jAcc ++ slotAt .a1 .s6 (2 * K.k))) <|
  .seq callAdd <|
  .seq (.block (polyAddr .a0 K.jAcc ++ atMul .a1 .s9 .s6 384)) <|
  .seq callEncode12 (.block (count .s6 K.k))

/-- `ŝ[j]` (`j` in `s6`) encoded into `dk`. -/
def kgSBody : Prog isa :=
  .seq (.block (slotAt .a0 .s6 K.k ++ atMul .a1 .s8 .s6 384)) (.seq callEncode12 (.block (count .s6 K.k)))

def keygen : Prog isa :=
  .seq (.block K.kgSetup) <|
  .seq (hash 72 0x06 [⟨.s10, 0, 32⟩, ⟨.s11, oK, 1⟩] [⟨.s11, oG, 64⟩]) <|
  .seq (copy .s11 oG .s11 oSeed 32) <|
  .seq (K.prfLoop true 0 (2 * K.k)) <|
  .seq (.block [.li .s4 1, .li .s6 0]) <|
  .seq (.loop K.kgRowBody (.nonzero .t0)) <|
  .seq (.block [.li .s6 0]) <|
  .seq (.loop K.kgSBody (.nonzero .t0)) <|
  .seq (copy .s11 oSeed .s9 (384 * K.k) 32) <|
  .seq (copy .s9 0 .s8 (384 * K.k) K.ekLen) <|
  .seq (.block [.addi .s8 .s8 (384 * K.k)]) <|
  .seq (hash 136 0x06 [⟨.s9, 0, K.ekLen⟩] [⟨.s8, 384 * K.k + 32, 32⟩]) <|
  .seq (copy .s10 32 .s8 (384 * K.k + 64) 32) (.block topEnd)

/-! ## K-PKE.Encrypt, with `ek` in `s10`, `m` in `s9`, `r` at `952` and `c` to `s7` -/

/-- `t̂[i] = ByteDecode₁₂(ek[384i : 384i + 384])` (`i` in `s6`). -/
def decTBody : Prog isa :=
  .seq (.block (atMul .a0 .s10 .s6 384 ++ slotAt .a1 .s6 0)) (.seq callDecode12 (.block (count .s6 K.k)))

/-- `u[i]` (`i` in `s6`), compressed and encoded into `c`. -/
def encRowBody : Prog isa :=
  .seq (K.rowSum true) <|
  .seq (.block (polyAddr .a0 K.jAcc ++ polyAddr .a1 K.jNtt)) <|
  .seq callNttInv <|
  .seq (.block (polyAddr .a0 K.jAcc ++ slotAt .a1 .s6 (2 * K.k))) <|
  .seq callAdd <|
  .seq (.block (atMul .a2 .s7 .s6 K.uLen ++ polyAddr .a0 K.jAcc ++ [.li .a1 K.du, .li .a3 K.uLen])) <|
  .seq K.callCU (.block (count .s6 K.k))

def encrypt : Prog isa :=
  .seq (copy .s10 (384 * K.k) .s11 oSeed 32) <|
  .seq (.block [.li .s6 0]) <|
  .seq (.loop K.decTBody (.nonzero .t0)) <|
  .seq (K.prfLoop true 0 K.k) <|
  .seq (K.prfLoop false K.k (2 * K.k + 1)) <|
  .seq (.block ([mov .a0 .s9, .li .a1 32, .li .a2 1] ++ polyAddr .a3 (3 * K.k + 1))) <|
  .seq callDecompress <|
  .seq (.block [.li .s4 1, .li .s6 0]) <|
  .seq (.loop K.encRowBody (.nonzero .t0)) <|
  .seq K.dot <|
  .seq (.block (polyAddr .a0 K.jAcc ++ polyAddr .a1 K.jNtt)) <|
  .seq callNttInv <|
  .seq (.block (polyAddr .a0 K.jAcc ++ polyAddr .a1 (3 * K.k))) <|
  .seq callAdd <|
  .seq (.block (polyAddr .a0 K.jAcc ++ polyAddr .a1 (3 * K.k + 1))) <|
  .seq callAdd <|
  .seq (.block (polyAddr .a0 K.jAcc ++ [.li .a1 K.dv, .addi .a2 .s7 (K.uLen * K.k), .li .a3 K.vLen])) K.callCU

end KemLay

/-! ## `vg_mlkem<n>_encaps(ek = a0, m = a1, key = a2, ct = a3, scratch = a4) -> a0` -/

def encapsSetup : List Instr :=
  topSave .a4 ++ ([mov .s10 .a0, mov .s9 .a1, mov .s8 .a2, mov .s7 .a3, mov .s11 .a4] : List Instr)

def KemLay.encaps (K : KemLay) : Prog isa :=
  .seq (.block encapsSetup) <|
  .seq (copy .s9 0 .s11 oMsg 32) <|
  .seq (.block [.addi .s9 .s11 oMsg]) <|
  .seq (hash 136 0x06 [⟨.s10, 0, K.ekLen⟩] [⟨.s11, oHek, 32⟩]) <|
  .seq (hash 72 0x06 [⟨.s11, oMsg, 32⟩, ⟨.s11, oHek, 32⟩] [⟨.s11, oG, 64⟩]) <|
  .seq (copy .s11 oG .s8 0 32) <|
  .seq K.encrypt (.block topEnd)

/-! ## `vg_mlkem<n>_decaps(dk = a0, ct = a1, key = a2, scratch = a3) -> a0` -/

def decapsSetup : List Instr :=
  topSave .a3 ++ ([mov .s3 .a2, mov .s10 .a0, mov .s8 .a1, mov .s11 .a3] : List Instr)

def cmpBody : List Instr :=
  [.load .b .a2 .a0 0, .load .b .a3 .a1 0, .logic .xor .a2 .a2 .a3, .logic .or .t2 .t2 .a2,
   .addi .a0 .a0 1, .addi .a1 .a1 1, .addi .s6 .s6 (-1)]

/-- A mask in `t2` (all ones if `c = c'`); `a0`, `a1` and `a2` point to
`K'`, `K̄` and `key`. -/
def selSetup : List Instr :=
  [.addi .t2 .t2 (-1), .shift .srl .d .t2 .t2 63, .li .a0 0, .sub .t2 .a0 .t2, .addi .a0 .s11 oG,
   .addi .a1 .s11 oKbar, mov .a2 .s3, .li .s6 32]

/-- `key[i] = K̄[i] ^ ((K'[i] ^ K̄[i]) & mask)`. -/
def selBody : List Instr :=
  [.load .b .a3 .a0 0, .load .b .a4 .a1 0, .logic .xor .a3 .a3 .a4, .logic .and .a3 .a3 .t2,
   .logic .xor .a3 .a3 .a4, .store .b .a3 .a2 0, .addi .a0 .a0 1, .addi .a1 .a1 1, .addi .a2 .a2 1,
   .addi .s6 .s6 (-1)]

namespace KemLay

variable (K : KemLay)

/-- `û[i] = NTT(Decompress_{d_u}(ByteDecode_{d_u}(c[32d_u·i : 32d_u·(i + 1)])))` (`i` in `s6`). -/
def decUBody : Prog isa :=
  .seq (.block (atMul .a0 .s8 .s6 K.uLen ++ [.li .a1 K.uLen, .li .a2 K.du] ++ slotAt .a3 .s6 K.k)) <|
  .seq K.callDU <|
  .seq (.block (slotAt .a0 .s6 K.k ++ polyAddr .a1 K.jNtt)) <|
  .seq callNtt (.block (count .s6 K.k))

/-- K-PKE.Decrypt, with `dk` in `s10` and `c` in `s8`: `m'` to `1024`. -/
def decrypt : Prog isa :=
  .seq (.block [.li .s6 0]) <|
  .seq (.loop K.decUBody (.nonzero .t0)) <|
  .seq (.block [.li .s6 0]) <|
  .seq (.loop K.decTBody (.nonzero .t0)) <|
  .seq K.dot <|
  .seq (.block (polyAddr .a0 K.jAcc ++ polyAddr .a1 K.jNtt)) <|
  .seq callNttInv <|
  .seq (.block ([.addi .a0 .s8 (K.uLen * K.k), .li .a1 K.vLen, .li .a2 K.dv] ++ polyAddr .a3 (3 * K.k))) <|
  .seq K.callDU <|
  .seq (.block (polyAddr .a0 (3 * K.k) ++ polyAddr .a1 K.jAcc)) <|
  .seq callSub <|
  .seq (.block (polyAddr .a0 (3 * K.k) ++ [.li .a1 1, .addi .a2 .s11 oMsg, .li .a3 32]))
    callCompress

/-- The OR of the XORs of the bytes of `c` (`s8`) and `c'` (`s7`), into `t2`. -/
def compare : Prog isa :=
  .seq (.block [mov .a0 .s8, mov .a1 .s7, .li .t2 0, .li .s6 K.ctLen])
    (.loop (.block cmpBody) (.nonzero .s6))

def decaps : Prog isa :=
  .seq (.block decapsSetup) <|
  .seq (.block (polyAddr .s9 22)) <|
  .seq (copy .s8 0 .s9 0 K.ctLen) <|
  .seq (.block [mov .s8 .s9]) <|
  .seq K.decrypt <|
  .seq (.block [.addi .s10 .s10 (384 * K.k)]) <|
  .seq (hash 72 0x06 [⟨.s11, oMsg, 32⟩, ⟨.s10, 384 * K.k + 32, 32⟩] [⟨.s11, oG, 64⟩]) <|
  .seq (hash 136 0x1f [⟨.s10, 384 * K.k + 64, 32⟩, ⟨.s8, 0, K.ctLen⟩] [⟨.s11, oKbar, 32⟩]) <|
  .seq (.block (.addi .s9 .s11 oMsg :: polyAddr .s7 K.jCt)) <|
  .seq K.encrypt <|
  .seq K.compare <|
  .seq (.block selSetup) <|
  .seq (.loop (.block selBody) (.nonzero .s6)) (.block topEnd)

end KemLay

/-! ## ML-KEM-768

`k = 3`, `d_u = 10`, `d_v = 4`. -/

/-- ML-KEM-768's parameters, which compress with `vg_mlkem_compress_encode`. -/
def kl768 : KemLay :=
  ⟨Spec.MlKem.mlKem768, 32768, "vg_mlkem_compress_encode", compressEncode, "vg_mlkem_decode_decompress",
    decodeDecompress⟩

abbrev keygen : Prog isa := kl768.keygen
abbrev encaps : Prog isa := kl768.encaps
abbrev decaps : Prog isa := kl768.decaps

end VG.Impl.MlKem.RISCV64
