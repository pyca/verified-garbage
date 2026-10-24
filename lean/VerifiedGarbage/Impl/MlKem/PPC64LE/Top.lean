module

public import VerifiedGarbage.Impl.MlKem.PPC64LE.Sample
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Ntt
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Codec
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Compress
public import VerifiedGarbage.Spec.MlKem

/-!
# ML-KEM on PPC64LE: key generation, encapsulation, decapsulation

As on 32-bit ARM (`Impl/MlKem/Arm/Top.lean`): the top-level functions of
ML-KEM-768 and ML-KEM-1024, for any parameter set `K : KemLay`, are
sequences of calls of the verified primitives and SHA-3 functions, on
buffers at fixed offsets in `scratch` and in the arguments. Every argument,
the calls' and ours, is in a register. The pointers are kept in callee-saved
registers, which the callees preserve: `r31` is `scratch` throughout, and
`r27`–`r30` the other buffers; `r26` and `r25` count loops and `r24` is the
return value: 1, or 0 once a `SampleNTT` has not finished within 280
iterations. They save our caller's `r24`–`r31` and our return address in
`scratch`, so the only stack they use is that of their callees (48 bytes).

`scratch` holds, at these offsets:

* `0`: the Keccak state; `200`: the working space of the sponge functions;
* `840`: our caller's `r24`–`r31` and our return address; `912`: the pointer
  `key` of decapsulation;
* `920`: the 64 bytes of `G`, `ρ ‖ σ` or `K ‖ r`, so `σ` (or `r`) is at
  `952`, the seed of `PRF`, followed by its counter `N`; `992`: `H(ek)`;
  `1024`: the message: a copy of `m` in encapsulation, `m'` in
  decapsulation; `1056`: the 128 bytes of a `PRF`; `1184`: the byte `k` of
  `G(d ‖ k)`; `1216`: `K̄`; `1248`: the seed `ρ ‖ j ‖ i` of `SampleNTT`;
* `2048 + 1024 j` for `j < 3k + 5`: polynomials (`oPoly`), as on ARM, then
  the working space of `vg_mlkem_sample_ntt` (2048 bytes), that of the NTTs
  and `vg_mlkem_multiply_ntts` (1024 bytes), then the ciphertext `c'` of
  decapsulation's re-encryption; `24576`: a copy of the ciphertext `c` of
  decapsulation.

Every address is a pointer plus a constant or a counter, every branch is on
a counter, on whether a `SampleNTT` finished (a function of the public seed
`ρ` and two indices), or on nothing secret; decapsulation compares `c` and
`c'` by the OR of the XORs of their bytes, and selects `K'` or `K̄` by a
mask, in constant time.
-/

@[expose] public section

namespace VG.Impl.MlKem.PPC64LE

open VG.PPC64LE
open VG.Impl.Sha3.PPC64LE.Stream (mov)

/-! ## The layout of `scratch` -/

abbrev oWork : Nat := 200
abbrev oSave : Nat := 840
abbrev oExtra : Nat := 912
abbrev oG : Nat := 920
abbrev oSigma : Nat := 952
abbrev oHek : Nat := 992
abbrev oMsg : Nat := 1024
abbrev oPrf : Nat := 1056
abbrev oK : Nat := 1184
abbrev oKbar : Nat := 1216
abbrev oSeed : Nat := 1248
/-- The polynomial `k`. -/
abbrev oPoly (k : Nat) : Nat := 2048 + 1024 * k
abbrev oCin : Nat := 24576

/-! ## Building blocks -/

/-- `d ← r31 + 1024 c + off`: polynomial `c` of an array of them at `off` in
`scratch`. -/
def slotAt (d c : Reg) (off : Nat) : List Instr := [.lsl d c 10, .add d .r31 d, .addi d d off]

/-- `d ← b + m c`, through `r0`. -/
def atMul (d b c : Reg) (m : Nat) : List Instr := [.li .r0 m, .mul .r0 c .r0, .add d b .r0]

/-- The counter `c` incremented, and `r0 = c - n`: zero when it reaches `n`. -/
def count (c : Reg) (n : Nat) : List Instr := [.addi c c 1, .subi .r0 c n]

/-- A buffer: `off` bytes past the pointer in `base`, of `len` bytes. -/
structure Piece where
  base : Reg
  off : Nat
  len : Nat

/-- The position: 0 at `first`, or the position the previous call returned. -/
def posArg (first : Bool) : Instr := if first then .li .r5 0 else mov .r5 .r3

/-- The arguments of `absorb` or `squeeze`: the Keccak state, the rate, the
position, the piece `p` and its length, and the working space. -/
def spongeArgs (rate : Nat) (first : Bool) (p : Piece) : List Instr :=
  [posArg first, mov .r3 .r31, .li .r4 rate, .addi .r6 p.base p.off, .li .r7 p.len, .addi .r8 .r31 oWork]

def callAbsorb : Prog isa := .call "vg_keccak_absorb_scratch" Impl.Sha3.PPC64LE.Stream.absorb
def callPad : Prog isa := .call "vg_keccak_pad_scratch" Impl.Sha3.PPC64LE.Stream.pad
def callSqueeze : Prog isa := .call "vg_keccak_squeeze_scratch" Impl.Sha3.PPC64LE.Stream.squeeze

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
  .seq (.block (zeroState .r31)) <|
  .seq (absorbs rate true ins) <|
  .seq (.block [mov .r5 .r3, mov .r3 .r31, .li .r4 rate, .li .r6 sfx, .addi .r7 .r31 oWork])
    (.seq callPad (squeezes rate true outs))

def copyBody : List Instr :=
  [.lbz .r6 .r3 0, .stb .r6 .r4 0, .addi .r3 .r3 1, .addi .r4 .r4 1, .subi .r5 .r5 1]

/-- Copy `len` bytes from `sb + so` to `db + dO`. -/
def copy (sb : Reg) (so : Nat) (db : Reg) (dO len : Nat) : Prog isa :=
  .seq (.block [.addi .r3 sb so, .addi .r4 db dO, .li .r5 len]) (.loop (.block copyBody) (.nonzero .d .r5))

def zeroBody : List Instr := [.store .w .r4 .r3 0, .addi .r3 .r3 4, .subi .r5 .r5 1]

/-- The polynomial at `off` in `scratch` set to zero. -/
def zeroPoly (off : Nat) : Prog isa :=
  .seq (.block [.addi .r3 .r31 off, .li .r4 0, .li .r5 256]) (.loop (.block zeroBody) (.nonzero .d .r5))

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

/-- The indices of the seed: `ρ ‖ j ‖ i` for `Â[i, j]`, with `i` in `r26` and
`j` in `r25`, or `ρ ‖ i ‖ j` for `Â[j, i]` (`transpose`). -/
def seedBytes (transpose : Bool) : List Instr :=
  if transpose then [.stb .r26 .r31 (oSeed + 32), .stb .r25 .r31 (oSeed + 33)]
  else [.stb .r25 .r31 (oSeed + 32), .stb .r26 .r31 (oSeed + 33)]

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
abbrev oAcc : Nat := oPoly (3 * K.k + 2)
abbrev oTmp : Nat := oPoly (3 * K.k + 3)
abbrev oAhat : Nat := oPoly (3 * K.k + 4)
/-- The working space of `vg_mlkem_sample_ntt` (2048 bytes), of the NTTs and
`vg_mlkem_multiply_ntts` (1024 bytes), and the ciphertext `c'` of
decapsulation's re-encryption. -/
abbrev oSample : Nat := oPoly (3 * K.k + 5)
abbrev oNtt : Nat := oPoly (3 * K.k + 7)
abbrev oCt : Nat := oPoly (3 * K.k + 8)

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

/-- `SamplePolyCBD₂(PRF₂(σ, N))` into polynomial `k + N`, with `N` in `r26`
(and `σ ‖ N` at `952`), then its NTT if `withNtt`. -/
def prfBody (withNtt : Bool) (N₁ : Nat) : Prog isa :=
  .seq (.block [.stb .r26 .r31 (oSigma + 32)]) <|
  .seq (hash 136 0x1f [⟨.r31, oSigma, 33⟩] [⟨.r31, oPrf, 128⟩]) <|
  .seq (.block (.addi .r3 .r31 oPrf :: slotAt .r4 .r26 (oPoly K.k))) <|
  .seq callCbd2 <|
  .seq (if withNtt then .seq (.block (slotAt .r3 .r26 (oPoly K.k) ++ [.addi .r4 .r31 K.oNtt])) callNtt
    else .block [])
    (.block (count .r26 N₁))

/-- `prfBody` for `N` from `N₀` to `N₁ - 1`. -/
def prfLoop (withNtt : Bool) (N₀ N₁ : Nat) : Prog isa :=
  .seq (.block [.li .r26 N₀]) (.loop (K.prfBody withNtt N₁) (.nonzero .d .r0))

/-- Entry `j` of row `i` (in `r25` and `r26`) of `Â` (or of `Â^⊺`) sampled,
and its product with polynomial `k + j` added to the sum. -/
def rowBody (transpose : Bool) : Prog isa :=
  .seq (.block (seedBytes transpose ++ [.addi .r3 .r31 oSeed, .addi .r4 .r31 K.oAhat, .addi .r5 .r31 K.oSample])) <|
  .seq callSample <|
  .seq (.block [.logic .and .r24 .r24 .r3]) <|
  .seq (.ite (.zero .d .r3) (.block (slotAt .r4 .r25 (oPoly K.k))) (.block [.addi .r4 .r31 K.oAhat])) <|
  .seq (.block (.addi .r3 .r31 K.oTmp :: slotAt .r5 .r25 (oPoly K.k) ++ [.addi .r6 .r31 K.oNtt])) <|
  .seq callMul <|
  .seq (.block [.addi .r3 .r31 K.oAcc, .addi .r4 .r31 K.oTmp]) <|
  .seq callAdd (.block (count .r25 K.k))

/-- Row `i` of `Â ∘ v̂` (or of `Â^⊺ ∘ v̂`), `v̂` polynomials `k` to `2k - 1`,
into polynomial `3k + 2`. -/
def rowSum (transpose : Bool) : Prog isa :=
  .seq (zeroPoly K.oAcc) (.seq (.block [.li .r25 0]) (.loop (K.rowBody transpose) (.nonzero .d .r0)))

def dotBody : Prog isa :=
  .seq (.block (.addi .r3 .r31 K.oTmp :: slotAt .r4 .r25 (oPoly 0) ++ slotAt .r5 .r25 (oPoly K.k) ++
    [.addi .r6 .r31 K.oNtt])) <|
  .seq callMul <|
  .seq (.block [.addi .r3 .r31 K.oAcc, .addi .r4 .r31 K.oTmp]) <|
  .seq callAdd (.block (count .r25 K.k))

/-- The sum of the products of polynomials `j` and `k + j`, into polynomial
`3k + 2`. -/
def dot : Prog isa := .seq (zeroPoly K.oAcc) (.seq (.block [.li .r25 0]) (.loop K.dotBody (.nonzero .d .r0)))

end KemLay

/-! ## Saving our caller's registers -/

/-- The nonvolatile registers we use, and where they are saved in `scratch`. -/
def topSaved : List (Reg × Nat) :=
  [(.r24, oSave), (.r25, oSave + 8), (.r26, oSave + 16), (.r27, oSave + 24), (.r28, oSave + 32),
    (.r29, oSave + 40), (.r30, oSave + 48), (.r31, oSave + 56)]

/-- Our caller's registers and our return address saved, with `scratch` in `b`. -/
def topSave (b : Reg) : List Instr :=
  .mflr .r0 :: topSaved.map (fun (r, d) => .store .d r b d) ++ ([.store .d .r0 b (oSave + 64)] : List Instr)

/-- The return value, and our caller's registers and our return address
restored (`r31`, the base, last). -/
def topEnd : List Instr :=
  [mov .r3 .r24, .load .d .r0 .r31 (oSave + 64), .mtlr .r0, .load .d .r24 .r31 oSave,
    .load .d .r25 .r31 (oSave + 8), .load .d .r26 .r31 (oSave + 16), .load .d .r27 .r31 (oSave + 24),
    .load .d .r28 .r31 (oSave + 32), .load .d .r29 .r31 (oSave + 40), .load .d .r30 .r31 (oSave + 48),
    .load .d .r31 .r31 (oSave + 56)]

/-! ## `vg_mlkem<n>_keygen(seed = r3, ek = r4, dk = r5, scratch = r6) -> r3` -/

namespace KemLay

variable (K : KemLay)

def kgSetup : List Instr :=
  topSave .r6 ++ ([mov .r30 .r3, mov .r29 .r4, mov .r28 .r5, mov .r31 .r6, .li .r0 K.k, .stb .r0 .r31 oK] :
    List Instr)

/-- Row `i` (in `r26`) of `t̂ = Â ∘ ŝ + ê`, encoded into `ek`. -/
def kgRowBody : Prog isa :=
  .seq (K.rowSum false) <|
  .seq (.block (.addi .r3 .r31 K.oAcc :: slotAt .r4 .r26 (oPoly (2 * K.k)))) <|
  .seq callAdd <|
  .seq (.block (.addi .r3 .r31 K.oAcc :: atMul .r4 .r29 .r26 384)) <|
  .seq callEncode12 (.block (count .r26 K.k))

/-- `ŝ[j]` (`j` in `r26`) encoded into `dk`. -/
def kgSBody : Prog isa :=
  .seq (.block (slotAt .r3 .r26 (oPoly K.k) ++ atMul .r4 .r28 .r26 384)) (.seq callEncode12 (.block (count .r26 K.k)))

def keygen : Prog isa :=
  .seq (.block K.kgSetup) <|
  .seq (hash 72 0x06 [⟨.r30, 0, 32⟩, ⟨.r31, oK, 1⟩] [⟨.r31, oG, 64⟩]) <|
  .seq (copy .r31 oG .r31 oSeed 32) <|
  .seq (K.prfLoop true 0 (2 * K.k)) <|
  .seq (.block [.li .r24 1, .li .r26 0]) <|
  .seq (.loop K.kgRowBody (.nonzero .d .r0)) <|
  .seq (.block [.li .r26 0]) <|
  .seq (.loop K.kgSBody (.nonzero .d .r0)) <|
  .seq (copy .r31 oSeed .r29 (384 * K.k) 32) <|
  .seq (copy .r29 0 .r28 (384 * K.k) K.ekLen) <|
  .seq (hash 136 0x06 [⟨.r29, 0, K.ekLen⟩] [⟨.r28, 768 * K.k + 32, 32⟩]) <|
  .seq (copy .r30 32 .r28 (768 * K.k + 64) 32) (.block topEnd)

/-! ## K-PKE.Encrypt, with `ek` in `r30`, `m` in `r29`, `r` at `952` and `c` to `r27` -/

/-- `t̂[i] = ByteDecode₁₂(ek[384i : 384i + 384])` (`i` in `r26`). -/
def decTBody : Prog isa :=
  .seq (.block (atMul .r3 .r30 .r26 384 ++ slotAt .r4 .r26 (oPoly 0))) (.seq callDecode12 (.block (count .r26 K.k)))

/-- `u[i]` (`i` in `r26`), compressed and encoded into `c`. -/
def encRowBody : Prog isa :=
  .seq (K.rowSum true) <|
  .seq (.block [.addi .r3 .r31 K.oAcc, .addi .r4 .r31 K.oNtt]) <|
  .seq callNttInv <|
  .seq (.block (.addi .r3 .r31 K.oAcc :: slotAt .r4 .r26 (oPoly (2 * K.k)))) <|
  .seq callAdd <|
  .seq (.block (atMul .r5 .r27 .r26 K.uLen ++ [.addi .r3 .r31 K.oAcc, .li .r4 K.du, .li .r6 K.uLen])) <|
  .seq K.callCU (.block (count .r26 K.k))

def encrypt : Prog isa :=
  .seq (copy .r30 (384 * K.k) .r31 oSeed 32) <|
  .seq (.block [.li .r26 0]) <|
  .seq (.loop K.decTBody (.nonzero .d .r0)) <|
  .seq (K.prfLoop true 0 K.k) <|
  .seq (K.prfLoop false K.k (2 * K.k + 1)) <|
  .seq (.block [mov .r3 .r29, .li .r4 32, .li .r5 1, .addi .r6 .r31 (oPoly (3 * K.k + 1))]) <|
  .seq callDecompress <|
  .seq (.block [.li .r24 1, .li .r26 0]) <|
  .seq (.loop K.encRowBody (.nonzero .d .r0)) <|
  .seq K.dot <|
  .seq (.block [.addi .r3 .r31 K.oAcc, .addi .r4 .r31 K.oNtt]) <|
  .seq callNttInv <|
  .seq (.block [.addi .r3 .r31 K.oAcc, .addi .r4 .r31 (oPoly (3 * K.k))]) <|
  .seq callAdd <|
  .seq (.block [.addi .r3 .r31 K.oAcc, .addi .r4 .r31 (oPoly (3 * K.k + 1))]) <|
  .seq callAdd <|
  .seq (.block [.addi .r3 .r31 K.oAcc, .li .r4 K.dv, .addi .r5 .r27 (K.uLen * K.k), .li .r6 K.vLen]) K.callCU

end KemLay

/-! ## `vg_mlkem<n>_encaps(ek = r3, m = r4, key = r5, ct = r6, scratch = r7) -> r3` -/

def encapsSetup : List Instr :=
  topSave .r7 ++ ([mov .r30 .r3, mov .r29 .r4, mov .r28 .r5, mov .r27 .r6, mov .r31 .r7] : List Instr)

def KemLay.encaps (K : KemLay) : Prog isa :=
  .seq (.block encapsSetup) <|
  .seq (copy .r29 0 .r31 oMsg 32) <|
  .seq (.block [.addi .r29 .r31 oMsg]) <|
  .seq (hash 136 0x06 [⟨.r30, 0, K.ekLen⟩] [⟨.r31, oHek, 32⟩]) <|
  .seq (hash 72 0x06 [⟨.r31, oMsg, 32⟩, ⟨.r31, oHek, 32⟩] [⟨.r31, oG, 64⟩]) <|
  .seq (copy .r31 oG .r28 0 32) <|
  .seq K.encrypt (.block topEnd)

/-! ## `vg_mlkem<n>_decaps(dk = r3, ct = r4, key = r5, scratch = r6) -> r3` -/

def decapsSetup : List Instr :=
  topSave .r6 ++ ([.store .d .r5 .r6 oExtra, mov .r30 .r3, mov .r28 .r4, mov .r31 .r6] : List Instr)

def cmpBody : List Instr :=
  [.lbz .r5 .r3 0, .lbz .r6 .r4 0, .logic .xor .r5 .r5 .r6, .logic .or .r12 .r12 .r5,
   .addi .r3 .r3 1, .addi .r4 .r4 1, .subi .r26 .r26 1]

/-- A mask in `r12` (all ones if `c = c'`); `r3`, `r4` and `r5` point to
`K'`, `K̄` and `key`. -/
def selSetup : List Instr :=
  [.subi .r12 .r12 1, .lsr .d .r12 .r12 63, .li .r3 0, .sub .r12 .r3 .r12, .addi .r3 .r31 oG,
   .addi .r4 .r31 oKbar, .load .d .r5 .r31 oExtra, .li .r26 32]

/-- `key[i] = K̄[i] ^ ((K'[i] ^ K̄[i]) & mask)`. -/
def selBody : List Instr :=
  [.lbz .r6 .r3 0, .lbz .r7 .r4 0, .logic .xor .r6 .r6 .r7, .logic .and .r6 .r6 .r12,
   .logic .xor .r6 .r6 .r7, .stb .r6 .r5 0, .addi .r3 .r3 1, .addi .r4 .r4 1, .addi .r5 .r5 1,
   .subi .r26 .r26 1]

namespace KemLay

variable (K : KemLay)

/-- `û[i] = NTT(Decompress_{d_u}(ByteDecode_{d_u}(c[32d_u·i : 32d_u·(i + 1)])))` (`i` in `r26`). -/
def decUBody : Prog isa :=
  .seq (.block (atMul .r3 .r28 .r26 K.uLen ++ [.li .r4 K.uLen, .li .r5 K.du] ++ slotAt .r6 .r26 (oPoly K.k))) <|
  .seq K.callDU <|
  .seq (.block (slotAt .r3 .r26 (oPoly K.k) ++ [.addi .r4 .r31 K.oNtt])) <|
  .seq callNtt (.block (count .r26 K.k))

/-- K-PKE.Decrypt, with `dk` in `r30` and `c` in `r28`: `m'` to `1024`. -/
def decrypt : Prog isa :=
  .seq (.block [.li .r26 0]) <|
  .seq (.loop K.decUBody (.nonzero .d .r0)) <|
  .seq (.block [.li .r26 0]) <|
  .seq (.loop K.decTBody (.nonzero .d .r0)) <|
  .seq K.dot <|
  .seq (.block [.addi .r3 .r31 K.oAcc, .addi .r4 .r31 K.oNtt]) <|
  .seq callNttInv <|
  .seq (.block [.addi .r3 .r28 (K.uLen * K.k), .li .r4 K.vLen, .li .r5 K.dv, .addi .r6 .r31 (oPoly (3 * K.k))]) <|
  .seq K.callDU <|
  .seq (.block [.addi .r3 .r31 (oPoly (3 * K.k)), .addi .r4 .r31 K.oAcc]) <|
  .seq callSub <|
  .seq (.block [.addi .r3 .r31 (oPoly (3 * K.k)), .li .r4 1, .addi .r5 .r31 oMsg, .li .r6 32])
    callCompress

/-- The OR of the XORs of the bytes of `c` (`r28`) and `c'`, into `r12`. -/
def compare : Prog isa :=
  .seq (.block [mov .r3 .r28, .addi .r4 .r31 K.oCt, .li .r12 0, .li .r26 K.ctLen])
    (.loop (.block cmpBody) (.nonzero .d .r26))

def decaps : Prog isa :=
  .seq (.block decapsSetup) <|
  .seq (copy .r28 0 .r31 oCin K.ctLen) <|
  .seq (.block [.addi .r28 .r31 oCin]) <|
  .seq K.decrypt <|
  .seq (hash 72 0x06 [⟨.r31, oMsg, 32⟩, ⟨.r30, 768 * K.k + 32, 32⟩] [⟨.r31, oG, 64⟩]) <|
  .seq (hash 136 0x1f [⟨.r30, 768 * K.k + 64, 32⟩, ⟨.r31, oCin, K.ctLen⟩] [⟨.r31, oKbar, 32⟩]) <|
  .seq (.block [.addi .r30 .r30 (384 * K.k), .addi .r29 .r31 oMsg, .addi .r27 .r31 K.oCt]) <|
  .seq K.encrypt <|
  .seq K.compare <|
  .seq (.block selSetup) <|
  .seq (.loop (.block selBody) (.nonzero .d .r26)) (.block topEnd)

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

end VG.Impl.MlKem.PPC64LE
