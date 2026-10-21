module

public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashCallers
public import VerifiedGarbage.Impl.Sha3.AArch64.Hybrid.X3
public import VerifiedGarbage.Impl.MlKem.AArch64.Paired

/-! # ML-KEM encapsulation hashing `ek` inside the paired matrix sampling

The hardware-SHA3 encapsulation computes `H(ek) = SHA3-256(ek)` in the third
state of `vg_keccak_f1600_x3_sha3`, while the paired SHAKE128 streams of the
matrix run in its vector state, instead of with separate permutations before
the matrix:

1. the prologue, `m` and `ρ`, and the all-zero third state at `ST` of
   `scratch` (`startH`);
2. the matrix (`Kem16P.matrixP`), whose first `hashPairs` pairs each make their
   three main squeezes with `x3` calls (`pair3`), each after XORing the next
   136-byte block of `ek` into the third state (`absorbBlock`; the last block
   is partial, and carries SHA3-256's padding `0x06 … 0x80`);
3. `H(ek)`, the first 32 bytes of the third state, into `HB`, and
   `G(m ‖ H(ek))` (`tailH`), right after those pairs, so that the rest of the
   matrix computes PRF outputs in its idle Keccak states (`Kem16P`);
4. noise, `u`, `v` and the epilogue.

Only the public lengths decide which blocks are absorbed when; the third
state's pointer is `scratch`'s. Key generation (`Kem16P.keyGen`) uses the same
pairs (`pairM`), each absorbing up to three blocks of the part of `ek` its
rows have encoded so far.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Hybrid
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM

/-- The message the third state absorbs: `len` bytes at `r + base`, padded
with the suffix `sfx` (rate 136). -/
structure HSrc where
  r : Reg
  base : Nat
  len : Nat
  sfx : Nat

/-- `ek`, for SHA3-256 (`H`). -/
def ekSrc (L : KemLay) : HSrc := ⟨.x25, 0, L.ekLen, 6⟩

/-- The number of 136-byte blocks of `pad(M)`. -/
def blocks (S : HSrc) : Nat := S.len / 136 + 1

/-- The pairs of the matrix whose main squeezes absorb the message: three blocks each. -/
def hashPairs (S : HSrc) : Nat := blocks S / 3

/-- XOR the `n` words at `r + eo` into the first `n` lanes of the third state
(at `scratch + ST`, `ST = 0`). -/
def absorbWords (r : Reg) (eo n : Nat) : List Instr :=
  (List.range n).flatMap fun w =>
    [.ldr .x .x9 r (eo + 8 * w), .ldr .x .x10 .x28 (8 * w), .logic .eor .x .x9 .x9 .x10,
      .str .x .x9 .x28 (8 * w)]

/-- XOR the byte `value` into byte `off` of `scratch`. -/
def xorByte (off value : Nat) : List Instr :=
  [.ldrb .x9 .x28 off, .movz .x .x10 (BitVec.ofNat 16 value) 0, .logic .eor .x .x9 .x9 .x10, .strb .x9 .x28 off]

/-- Block `b` of `pad(M)` (rate 136, suffix `S.sfx`) into the third state. -/
def absorbBlock (S : HSrc) (b : Nat) : List Instr :=
  if 136 * b + 136 ≤ S.len then absorbWords S.r (S.base + 136 * b) 17
  else absorbWords S.r (S.base + 136 * b) ((S.len - 136 * b) / 8) ++
    xorByte (S.len - 136 * b) S.sfx ++ xorByte 135 128

/-- `vg_keccak_f1600_x3_sha3` on the pair at `x19`, the third state at `scratch`
(`ST = 0`) and its working space at `x19 + 1536`, keeping `x30` after it. -/
def x3call : Prog isa :=
  .seq (.block [.addImm .x .x2 .x19 1536, .str .x .x30 .x2 128, .addImm .x .x0 .x19 0,
      .addImm .x .x1 .x28 0])
    (.seq (.call Impl.Sha3.AArch64.Hybrid.X3.name Impl.Sha3.AArch64.Hybrid.X3.code)
      (.block [.ldr .x .x30 .x19 1664]))

/-- The squeeze's tail: both states' first 21 words, and the next blocks. -/
def squeezeTail : List Instr :=
  Impl.Sha3.AArch64.Neon.X2.squeeze 21 .x19 .x20 .x21 ++ [.addImm .x .x20 .x20 168, .addImm .x .x21 .x21 168]

/-- One main squeeze absorbing block `b`. -/
def step3 (S : HSrc) (b : Nat) : Prog isa :=
  .seq (.block (absorbBlock S b)) (.seq x3call (.block squeezeTail))

/-- A main squeeze absorbing no block: `vg_keccak_f1600_x2_sha3` alone. -/
def plainStep : Prog isa :=
  .seq (VG.Impl.Sha3.AArch64.Neon.X2.call true .x19 .x19 1536) (.block squeezeTail)

/-- Main squeeze `k` of a pair absorbing blocks `j`, …, `j + m - 1`. -/
def stepM (S : HSrc) (j m k : Nat) : Prog isa :=
  if k < m then step3 S (j + k) else plainStep

/-- The three main squeezes of a pair, the first `m` absorbing blocks `j`, …, `j + m - 1`. -/
def squeezeM (S : HSrc) (j m : Nat) : Prog isa :=
  .seq (stepM S j m 0) (.seq (stepM S j m 1) (stepM S j m 2))

/-- `Paired.pair` with `squeezeM` for the three main squeezes, its seed at `sb`,
its working space at `ss` and its entries at `off`. -/
def pairM (sb ss off : Nat) (L : KemLay) (S : HSrc) (a j m : Nat) (w16 : Bool := false) : Prog isa :=
  seqs [.block (Paired.init sb ss a (a+1) L.k), squeezeM S j m, .block Rej8.rejConsts,
    Paired.reject 400 (off+1024*a) .x22 w16,
    .block [.str .x .x3 .x19 1680,.str .x .x4 .x19 1688],
    Paired.reject 904 (off+1024*(a+1)) .x23 w16,
    .block [.str .x .x3 .x19 1696,.str .x .x4 .x19 1704,.logic .and .x .x6 .x22 .x23],
    .ite (.zero .x .x6) (Paired.extraPair w16) (.block []),
    .block ((Paired.saved.zipIdx.reverse.map fun (r,i) => .ldr .x r .x19 (1800+8*i)))]

/-- `Paired.pair` (encapsulation) whose three main squeezes absorb blocks `3i`, `3i + 1`
and `3i + 2`. -/
def pair3 (L : KemLay) (S : HSrc) (a i : Nat) (w16 : Bool := false) : Prog isa :=
  pairM SB SS AH L S a (3 * i) 3 w16

/-- The prologue, `m`, the all-zero third state and `ρ`. -/
def startH (L : KemLay) : Prog isa :=
  .block (L.kemPrologue 4 [0,2,3,4] ++ copy32 .x1 0 .x28 MB ++ zeroState .x28 KEM.ST ++
    copy32 .x25 (384*L.k) .x28 SB)

/-- `H(ek)` into `HB`, and `G(m ‖ H(ek))` into `key` and `RB`. -/
def tailH (hash : FixedHashCallers.HashFn) : Prog isa :=
  .seq (.block (copy32 .x28 KEM.ST .x28 HB))
    (hash .x28 KEM.ST WK 72 6 [⟨.x28,MB,32⟩,⟨.x28,HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,RB,32⟩])

end VG.Impl.MlKem.AArch64.Hybrid
